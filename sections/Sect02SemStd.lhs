%if False
\begin{code}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wall #-}

module Sect02SemStd where

import Control.Monad.Except
import Control.Monad.Fail as Fail
import qualified Control.Monad.HT as HT
import Data.Tuple.HT
import Data.Maybe
import Control.Monad.Reader (ReaderT, runReaderT)
import qualified Control.Monad.Reader as R


mmap :: Monad m => (a -> m b) -> [a] -> m [b]
mmap = HT.map

\end{code}
%endif
\section{Definitional Interpreter for a Language With Pattern Matching}

\label{sec:def-interp}

Definitional interpreters define the meaning of a (new) object language by implementing an interpreter for it in an existing, well-understood, language.
We use \emph{Haskell} to implement a definitional interpreter for a functional language with pattern matching.

\subsection{Syntax}
The abstract syntax of the language we consider is summarized in \cref{fig:syntax}.
The expression constructors for |Var|, |Lam|, and |App| are standard expressions for variables, unary functions, and function application.
An expression constructor expression |Con f [e_1, ..., e_n]| represents an |n|-ary term whose head symbol is |f|, and whose sub-term values are the results of evaluating each expression |e_1...e_n|.
|Case e [(p_1, e_1), ..., (p_n, e_n)]| is a pattern match expression which first evaluates |e| to a value and then attempts to match the resulting value against the patterns |p_1...p_n|, where patterns are given by the type |Patt|.
|Letrec| expressions are restricted to bind value expressions, given by the type |ValExpr|.

\begin{figure}
\begin{boxedminipage}{0.77\linewidth}
\begin{code}
data Expr     =  Con String [Expr]
              |  Case Expr [(Patt, Expr)]
              |  Var String
              |  Lam String Expr
              |  App Expr Expr
              |  Let [(String, Expr)] Expr
              |  Letrec [(String, ValExpr)] Expr
              |  EEq Expr Expr
\end{code}
%if False
\begin{code}
              deriving Show
              deriving Eq
\end{code}
%endif
\begin{code}
data ValExpr  =  VCon String [ValExpr]
              |  VLam String Expr
\end{code}
%if False
\begin{code}
              deriving Show
              deriving Eq
\end{code}
%endif
\begin{code}
data Patt     =  PVar String
              |  PCon String [Patt]
\end{code}
%if False
\begin{code}
              deriving Show
              deriving Eq
\end{code}
%endif
\end{boxedminipage}
\caption{Syntax for a language with pattern matching, functions, let, and letrec}
\label{fig:syntax}
\end{figure}

%if False
\begin{code}
class (MonadEnv val m,
       MonadMatch val Cases m,
       TermVal val,
       FunVal val,
       FunApp val m,
       TermEq val m,
       MonadFail m) => EffVal m val where

resolve :: String -> Env v -> v
resolve x nv = fromJust (lookup x nv)
\end{code}
%endif

\begin{figure*}[t]
\centering
\begin{boxedminipage}[c][26em]{0.42\linewidth}
\begin{code}
interp :: EffVal m val => Expr -> m val



interp (Con c es) = do
  vs <- mmap interp es
  return (con_v c vs)
interp (Case e bs) =
  let vbs = map (mapSnd interp) bs in do
  v <- interp e
  match v (Cases vbs)
interp (Var x) = do
  nv <- ask
  return (resolve x nv)
interp (Lam x e) = do
  nv <- ask
  return (clos_v x e nv)
interp (App e_1 e_2) = do
  f <- interp e_1
  a <- interp e_2
  app f a
\end{code}
\end{boxedminipage}
\hspace{2em}
\begin{boxedminipage}[c][26em]{0.42\linewidth}
\begin{code}
interp (Let xes e) = do
  nv <- mmap interpSnd xes
  local (\ nv_0 -> nv ++ nv_0) (interp e)
  where interpSnd (x, e) = do
          v <- interp e; return (x, v)
interp (Letrec xves e) = do
  nv <- ask
  let  nv_b  = map (mapSnd (interpval nv_r)) xves
       nv_r  = nv_b ++ nv in
    local (\ _ -> nv_r) (interp e)
interp (EEq e_1 e_2) = do
  v_1 <- interp e_1
  v_2 <- interp e_2
  eq v_1 v_2


interpval ::  (TermVal val, FunVal val) =>
              Env val -> ValExpr -> val
interpval nv (VLam x e)   = clos_v x e nv
interpval nv (VCon x es)  =
  con_v x (map (interpval nv) es)
\end{code}
\end{boxedminipage}
\caption{A definitional interpreter for a language with pattern matching}
\label{fig:def-interp}
\end{figure*}


\subsection{Prelude to a Definitional Interpreter:\\ Effects and Values}

\label{sec:prelude}

The definitional interpreter for the language we consider in this paper is given in \cref{fig:def-interp}.
The interpreter depends on the |EffVal| type class which in turn depends on a number of type classes that constrain the polymorphic notion of effects (defined by a monad |m|) and values (defined by a value type |val|) of the interpreter.
The |EffVal| type class is thus a polymorphic embedding~\cite{HoferORM08} of a language that allows us to define a \emph{family} of interpreters for the same language, akin to the finally tagless approach of \citet{CaretteKS09}.
We summarize the type classes that |EffVal| comprises.

\paragraph{Effects}

The language that we define has two classes of effects: lexically-scoped functions and pattern matching.
The following Haskell type class constrains a monad |m| to provide two operations for accessing environments (|ask|), and altering which local environment is passed down to recursive calls of the interpreter (|local|):
\begin{code}
type Env val = [(String, val)]
class Monad m => MonadEnv val m where
  ask    :: m (Env val)
  local  :: (Env val -> Env val) -> m val -> m val
\end{code}
|MonadEnv| is a specialized version of the classical reader monad \cite{LiangHJ95,mtlreader,Jones95}:
\begin{code}
class Monad m => ClassicalMonadReader r m where
  ask_c    :: m r
  local_c  :: (r -> r) -> m a -> m a
\end{code}
There are two reasons why we use a specialized version.
The reason we specialize the type of environments, as opposed to an arbitrary type |r|, is to help Haskell's type class instance resolution engine (using GHC v8.6.4).
The reason we insist that the return type is |val| for the computation that |local| takes as argument, is a desire to know that this particular computation is value-producing, for reasons we explain \cref{sec:towards-sym-exc}.

% Our goal is to derive symbolic executors from definitional interpreters.
The purpose of symbolic execution is to decide which inputs cause which parts of a program to execute.
For this reason, we treat conditional branching as an effect.
The following type class constrains a monad |m| to provide a generic operation for branching:
\begin{code}
class Monad m => MonadBranch cval rval fork m where
  branch :: cval -> fork m rval -> m rval
\end{code}
This type class is parameterized by: (1) a value type |cval| that branch selection is conditional upon; (2) a value type |rval| for the return type of computations in branches; and (3) a |fork| type, an abstract notion of branches comprising computations described by |m| and |val|.
To illustrate, consider the following instance of |MonadBranch| which represents a classical if-then-else expression:
\begin{code}
newtype IfThenElse m a = ITE (m a, m a)

instance  Monad m =>
          MonadBranch Bool rval IfThenElse m where
  branch True   (ITE (t, _)) = t
  branch False  (ITE (_, f)) = f 
\end{code}
For our interpreter, which branches on values and returns values of the same type, we rely on the following more restrictive version of |MonadBranch|:\footnote{The main motivation for using the more specific notion of |MonadMatch| here is to help Haskell's type class resolution engine (using GHC v8.6.4). Morally, |MonadBranch| should do.}
\begin{code}
class Monad m => MonadMatch val fork m where
  match :: val -> fork m val -> m val
\end{code}
And our interpreter uses the following notion of |fork| over a list of pairs consisting of a pattern and a (monadic) computation where each computation has the same return type |a|:
\begin{code}
newtype Cases m a = Cases [(Patt, m a)]
\end{code}

\paragraph{Values}

The following type classes define the constructors for term values |con_v| and function closures |clos_v|, as well as operation |app| for applying a function to an argument and operation |eq| for checking equality between two term values.
\begin{code}
class TermVal val where
  con_v   :: String -> [val] -> val

class FunVal val where
  clos_v  :: String -> Expr -> Env val -> val

class FunApp val m where
  app     :: val -> val -> m val

class TermEq val m where
  eq      :: val -> val -> m val
\end{code}

\subsection{A Definitional Interpreter for a Language with Pattern Matching}

\label{sec:def-interp-standard}

The interpreter in \cref{fig:def-interp} relies on the effect and value type classes summarized in the previous section.
Additionally, the interpreter makes use of a few auxiliary functions whose definitions we elide: |mmap| maps a monadic function over a list; |mapSnd| maps a function over the second element of a tuple; and |resolve| resolves a name in an association list, or fails.
The implementation of |Letrec| uses Haskell's support for (lazy) recursive definitions to define a recursive environment |nv_r| that |ValExpr|s are evaluated under.


To run our definitional interpreter we must provide concrete instances of the abstract type classes from \cref{sec:prelude}.
We use the following notion of value and monad:
\begin{code}
data ConcreteValue  =  ConV String [ConcreteValue]
                    |  ClosV String Expr (Env ConcreteValue)
\end{code}
\vspace*{-2em}
%if False
\begin{code}
                   deriving Show
                   deriving Eq
\end{code}
%endif
\begin{code}
type ConcreteMonad  =
  ReaderT (Env ConcreteValue) (Except String)
\end{code}
Here |ReaderT| is a monad transformer \cite{LiangHJ95} for the classical reader monad, and |Except| is the exception monad.
So |ConcreteMonad| is isomorphic to:
\begin{code}
type ConcreteMonad' a =
  Env ConcreteValue -> Either String a
\end{code}
The type class instances for this notion of value and monad are defined in the obvious way.
|MonadMatch| attempts to pattern match a value against a list of cases by attempting each from left-to-right until a match succeeds:
\begin{code}
instance MonadMatch  ConcreteValue Cases
                     ConcreteMonad where
  match v (Cases ((p, m) : bs)) = case vmatch (v, p) of
      Just nv -> local (\ nv0 -> nv ++ nv0) m
      Nothing -> match v (Cases bs)
  match _ (Cases []) = throwError "Match failure"

vmatch ::  (ConcreteValue, Patt) ->
           Maybe (Env ConcreteValue)
\end{code}
%if False
\begin{code}
vmatch (ConV s vs, PCon s' ps) =
  if (s == s' && length vs == length ps)
  then concat <$> mmap vmatch (zip vs ps)
  else Nothing
vmatch (v', PVar x)  = Just [(x, v')]
vmatch (_, _)        = Nothing
\end{code}
%endif
Using these type class instances, our definitional interpreter can be run as follows:
\begin{code}
runSteps ::  Expr -> Env ConcreteValue ->
             Either String ConcreteValue
runSteps e nv = runExcept (runReaderT (interp e) nv)
\end{code}

%if False
\begin{code}
instance TermVal ConcreteValue where
  con_v = ConV

instance FunVal ConcreteValue where
  clos_v = ClosV

instance {-# OVERLAPPING #-} Monad m => MonadFail (ExceptT String m) where
  fail s = throwError s

instance (Monad m, R.MonadReader (Env v) m) => MonadEnv v m where
  ask   = R.ask
  local = R.local

instance FunApp ConcreteValue ConcreteMonad where
  app (ClosV x e nv) v = local (\ _ -> (x, v) : nv) (interp e)
  app _ _ = throwError "Could not apply non-function"

instance TermEq ConcreteValue ConcreteMonad where
  eq v1 v2 | v1 == v2 = return (ConV "true" [])
  eq _  _  = return (ConV "false" [])

instance EffVal ConcreteMonad ConcreteValue where
\end{code}
%endif

%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../document"
%%% End:
