%if False
\begin{code}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

module Sect03TowardsSymExc where

import Control.Monad.Except
import Control.Monad.Fail
import Sect02SemStd
import Control.Monad.Reader (runReaderT)
import qualified Control.Monad.Reader as Reader
\end{code}
%endif
\section{Towards a Symbolic Executor}
\label{sec:towards-sym-exc}

The definitional interpreter presented in \cref{sec:def-interp-standard} uses standard monads and monad transformers to give a semantics for the definitional interpreter in \cref{fig:def-interp}.
But it gives meta-programmers little control over how interpretation proceeds.
Our goal in this paper is to implement a symbolic executor for running a program in a way that interleavingly explores all possible execution paths.
To this end, we want a symbolic executor that can operate on a pool of concurrently running threads where each thread represents a possible path through the program.
We will approach this challenge by adopting a small-step execution strategy for each thread.
In this section we provide alternative type class instances that give meta-programmers more fine-grained control over how interpretation proceeds.
Concretely, we adopt a small-step execution strategy for effect interpretation, by using \emph{free monads}.

Following \citet{KiselyovI15} and \citet{SwierstraB19}, the following data type defines a family of free monads:
\begin{code}
data Free c a  =  Stop a
               |  forall b. Step (c b) (b -> Free c a)
\end{code}
Following \citet{HancockS00}, we call values of this data type \emph{command trees}: each |Step| represents an application of a command |c b|, corresponding to a monadic operation, which yields a value of type |b| when interpreted.
This value is passed to the continuation (|b -> Free c a|) of |Step|.
The |Free| data type is a monad:
%if False
\begin{code}
liftF :: c a -> Free c a
liftF c = Step c Stop

instance Functor (Free c) where
  fmap :: (a -> b) -> Free c a -> Free c b
  fmap g (Stop a)   = Stop (g a)
  fmap g (Step c k) = Step c (fmap g . k)

instance Applicative (Free c) where
  pure :: a -> Free c a
  pure = Stop

  (<*>) :: Free c (a -> b) -> Free c a -> Free c b
  Stop g     <*> f = fmap g f
  (Step c k) <*> f = Step c (\ x -> k x <*> f)
\end{code}
%endif
\begin{code}
instance Monad (Free c) where
  return           = Stop

  Stop a    >>= k  = k a
  Step c f  >>= k  = Step c (\ x -> f x >>= k)
\end{code}
By defining a suitable notion of command, we can define a free monad instance which satisfies the type class constraints for our definitional interpreter from \cref{fig:def-interp}.
The following data type defines such a notion of command:
\begin{code}
data Cmd val :: * -> * where
  Match  ::  val -> Cases (Free (Cmd val)) val ->
             Cmd val val
  Local  ::  (Env val -> Env val) -> Free (Cmd val) val ->
             Cmd val val
  Ask    ::  Cmd val (Env val)
  App_c  ::  val -> val -> Cmd val val
  Eq_c   ::  val -> val -> Cmd val val
  Fail   ::  String -> Cmd val a
\end{code}
%if False
\begin{code}
instance MonadFail (Free (Cmd v)) where
  fail s = liftF (Fail s)

instance {-# OVERLAPPING #-} MonadEnv v (Free (Cmd v)) where
  ask = liftF Ask
  local f m = liftF (Local f m)

instance MonadMatch val Cases (Free (Cmd val)) where
  match v (Cases bs) = liftF (Match v (Cases bs))

instance FunApp val (Free (Cmd val)) where
  app f a = liftF (App_c f a)

instance TermEq val (Free (Cmd val)) where
  eq v_1 v_2 = liftF (Eq_c v_1 v_2)

instance (TermVal val, FunVal val) => EffVal (Free (Cmd val)) val where
\end{code}
%endif
By instantiating each of the type classes we obtain a \emph{compiler} from expressions into command trees:
\begin{code}
comp ::  (TermVal val, FunVal val) =>
         Expr -> Free (Cmd val) val
comp =  interp
\end{code}
The command trees that |comp| yields are the sequences (or rather trees) of effectful operations that define the meaning of object language expressions.
But the meaning of command trees is left open to interpretation.
We define the meaning of command trees by means of a small-step transition function and a driver loop  for the transition function.
This small-step transition function operates on a single command tree (whose type we abbreviate |Thread_c|, since the command tree represents a thread of interpretation), and yields a single command tree as result (or raises an exception).
For brevity, we show just a few cases of the |step| function:
\begin{code}
type Thread_c = Free (Cmd ConcreteValue)

step ::  Thread_c ConcreteValue ->
         ConcreteMonad (Thread_c ConcreteValue)
step (Stop x)                       = return (Stop x)
step (Step (Match _ (Cases [])) _)  =
  throwError "Pattern match failure"
step (Step (Match v (Cases ((p, m) : bs))) k) =
  case vmatch (v, p) of
    Just nv ->
      return (Step (Local (\ nv_0 -> nv ++ nv_0) m) k)
    Nothing -> step (Step (Match v (Cases bs)) k)
\end{code}
%if False
\begin{code}
step (Step (Local f m) k) = do
  r <- Reader.local f (step m)
  return (case r of
            Stop x -> k x
            _      -> Step (Local f r) k)
step (Step Ask k) = do
  nv <- Reader.ask
  return (k nv)
step (Step (App_c (ClosV x e nv) a) k) = do
  return (Step (Local  (\ _ -> (x, a) : nv)
                       (interp e)) k)
step (Step (App_c _ _) _) =
  throwError "Application to non-function argument"
step (Step (Eq_c v_1 v_2) k) | v_1 == v_2 =
  return (k (ConV "true" []))
step (Step (Eq_c _ _) k) =
  return (k (ConV "false" []))
step (Step (Fail s) _) =
  throwError s
\end{code}
%endif
The driver loop for the step function is straightforwardly defined to continue interpretation until the current thread of interpretation terminates successfully (or fails):
\begin{code}
drive ::  Thread_c ConcreteValue ->
          ConcreteMonad ConcreteValue
drive (Stop x)  = return x
drive c         = do r <- step c; drive r
\end{code}
Thus an alternative definitional interpreter for the language in \cref{fig:def-interp} is given by the following function:
\begin{code}
runSteps ::  Expr -> Env ConcreteValue ->
             Either String ConcreteValue
runSteps e nv = runExcept (runReaderT (drive (comp e)) nv)
\end{code}


