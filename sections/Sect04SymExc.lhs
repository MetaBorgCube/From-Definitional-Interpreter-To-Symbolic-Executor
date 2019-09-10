%if False
\begin{code}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall #-}

module Sect04SymExc where

import Sect02SemStd
import Sect03TowardsSymExc
import Control.Monad.Reader (ReaderT, runReaderT)
import qualified Control.Monad.Reader as Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Fail as Fail
import Data.Tuple.HT
import ListMonad
import Lib
import Sugar

import Debug.Trace

\end{code}
%endif

\section{From Definitional Interpreter to Symbolic Executor}

\label{sec:sym-exc}

In this section we derive a symbolic executor from the definitional interpreter in \cref{sec:towards-sym-exc}, by: (1) generalizing the notion of value from previous sections to also incorporate symbolic variables; and (2) generalizing the semantics (monad and small-step transition function) to support instantiation of symbolic variables and fork new threads of interpretation.

\paragraph{Symbolic Values} The updated notion of value is an extension of the notion of |ConcreteValue| data type from \cref{sec:def-interp-standard} with a symbolic variable constructor, |SymV|:
\begin{code}
data SymbolicValue  =  ConV'   String [SymbolicValue]
                    |  ClosV'  String Expr (Env SymbolicValue)
                    |  SymV    String
\end{code}
%if False
\begin{code}
                   deriving Show
                   deriving Eq

instance TermVal SymbolicValue where
  con_v = ConV'

instance FunVal SymbolicValue where
  clos_v = ClosV'
\end{code}
%endif


\paragraph{Monad}

The monad for evaluating a step of symbolic execution has an environment and may raise an exception, just like the monad in \cref{sec:towards-sym-exc} for evaluating a step of concrete execution.
Additionally, the monad has a stateful |Int| field for keeping track of a fresh supply of symbolic variable names:
\begin{code}
type SymbolicMonad =
  ReaderT  (Env SymbolicValue)
           (StateT Int (Except String))
\end{code}
Since symbolic execution should explore all possible execution paths through a program, we generalize the small-step transition relation from \cref{sec:towards-sym-exc} by letting the transition relation take a single thread of interpretation as input, but return a \emph{set} of possible continuation threads.
Each step may result in unifying a symbolic variable in order to explore a possible execution path.
Our generalized notion of monad is thus given by the following types:
\begin{code}
type Unifier   = [(String, SymbolicValue)]
type Unifier_N = [(SymbolicValue, SymbolicValue)]
type SymbolicSetMonad =
  StateT (Unifier, Unifier_N) (ListT SymbolicMonad)
\end{code}
Here, |Unifier| witnesses how symbolic variables must be instantiated in order to complete a single transition step, representing a particular execution path of the program being symbolically executed.
|Unifier_N| represents a set of \emph{negative unification constraints}.
We motivate the use and need for these shortly.
The |ListT| monad transformer generalizes the return type of a monadic computation |m a| to return a list of |a|s; i.e., |m [a]|.
Note that, although we call |ListT| a monad transformer, it is well-known that |ListT| in Haskell is not guaranteed to yield a monad that satisfies the monad laws.
For the purpose of this paper, it is not essential whether the particular definition of |SymbolicSetMonad| above actually satisfies the monad laws.

\paragraph{Small-Step Transition Function}

Our symbolic executor is derived from the concrete semantics of effects in \cref{sec:towards-sym-exc} by altering how we |Match| and |Eq_c| effects are interpreted.
Thus all cases of the transition function |step_s| (below) are identical to the small-step transition function from \cref{sec:towards-sym-exc}, except for the cases for the |Match| and |Eq_c|.
Furthermore, the definitional interpreter from \cref{fig:def-interp} is unchanged.
We summarize the interesting cases for the |step_s| function, which takes a symbolic interpretation thread, |Thread_s|, as input, and returns a \emph{set} of threads (note the use of |SymbolicSetMonad|):
\begin{code}
type Thread_s = Free (Cmd SymbolicValue)

step_s ::  Thread_s SymbolicValue ->
           SymbolicSetMonad (Thread_s SymbolicValue)
step_s (Step (Match _ (Cases [])) _) = mzero
step_s (Step (Match v (Cases ((p, m) : bs))) k) = (do
    (nv, u) <- vmatch_s (v, p)
    (applySubst u (Step (Local (\ nv0 -> nv ++ nv0) m) k))
      `mplus` step_s (Step (Match v (Cases bs)) k))
  `catchError` (\ _ -> step_s (Step (Match v (Cases bs)) k))
step_s (Step (Eq_c v_1 v_2) k) =
  case unify v_1 v_2 of
    Just []  -> return (k (ConV' "true" []))
    Just u   -> do
      (applySubst u (k (ConV' "true" []))) `mplus`
        (constrainUnif_N u (k (ConV' "false" [])))
    Nothing  ->
      return (k (ConV' "false" []))
\end{code}
As in \cref{sec:towards-sym-exc}, there are two cases for |Match|: one for the case where we have exhausted the list of patterns to match a value against, and one for the case where there are more cases to consider.
In case we have exhausted the list of patterns to match a value against, we now use |mzero| to return an empty set of result threads.
Otherwise, we match a value against a pattern, using the side-effectful |vmatch_s| function  (elided for brevity).
If the value contains symbolic variables, the |vmatch_s| function computes a unifier to be be applied to the symbolic variables in order to make the pattern match succeed.
The transition function returns the thread resulting from applying that unifier to the matched branch, unioned with (via the |`mplus`| operation of the |SymbolicSetMonad|) any other threads contained in branches with patterns that may succeed to match (via the recursive call to |step_s| in the second |Match| case above).
This way, the transition function computes the set of all possible execution paths for a given expression.

The case of the |step_s| function above for expressions of the form |Eq_c v_1 v_2| checks whether |v_1| and |v_2| are unifiable.
If they are unifiable with the empty unifier, there is only one possible execution path to consider, namely the execution path where |v_1| and |v_2| are equal.
Otherwise, if |v_1| and |v_2| have a non-empty unifier, there are two possible execution paths to consider: one where |v_1| and |v_2| are equal, and one where they are not.
The |step_s| function returns the union (again, using |`mplus`|) of two threads representing each of these execution paths.
For safety, we register a \emph{negative unification constraint} for the execution path that disequates |v_1| and |v_2|, such that |v_1| and |v_2| cannot be unified at any point in the future during symbolic execution.

%if False
\begin{code}
step_s (Stop x) = return (Stop x)
step_s (Step (Local f t) k) = do
  r <- Reader.local f (step_s t)
  return (case r of
            Stop x -> k x
            _      -> Step (Local f r) k)
step_s (Step Ask k) = do
  nv <- Reader.ask
  return (k nv)
step_s (Step (App_c (ClosV' x e nv) a) k) = do
  return (Step (Local  (\ _ -> (x, a) : nv)
                       (interp e)) k)
step_s (Step (App_c _ _) _) =
  throwError "Application to non-function argument"
step_s (Step (Fail s) _) =
  throwError s

---------------------------
--- auxiliary functions ---
---------------------------

unify :: SymbolicValue -> SymbolicValue -> Maybe Unifier
unify v1             v2             | v1 == v2 =
  return []
unify (ConV' s1 vs1) (ConV' s2 vs2) | s1 == s2 =
  foldr (\ (v1, v2) m -> do
            u <- m
            u' <- unify v1 v2
            return (u ++ u'))
        (return [])
        (zip vs1 vs2)
unify (ConV' _ _)    (ConV' _ _)  = Nothing
unify x@(ConV' _ _)  y@(SymV _)   = unify y x
unify (SymV x)       t            | occurs x t = Nothing
unify (SymV x)       v            = return [(x, v)]
unify _              _            = Nothing

occurs :: String -> SymbolicValue -> Bool
occurs x (SymV y)      | x == y = True
occurs _ (SymV _)      = False
occurs x (ConV' _ vs)  =
  foldl (\ b v -> b || occurs x v) False vs
occurs x (ClosV' _ _ nv) =
  occursnv x nv

occursnv :: String -> Env SymbolicValue -> Bool
occursnv x nv = do
  foldl (\ b (_, v) -> b || occurs x v) False nv

subst :: (String, SymbolicValue) -> SymbolicValue -> SymbolicValue
subst (y, v) (SymV x)        = if x == y then v else (SymV x)
subst (x, v) (ConV' s args)  =
  ConV' s (map (subst (x, v)) args)
subst (x, v) (ClosV' y e nv) =
  ClosV' y e (map (mapSnd (subst (x, v))) nv)

-- auxiliary
mapTuple :: (a -> b) -> (a, a) -> (b, b)
mapTuple f (x, y) = (f x, f y)

mapCmd_v ::  (SymbolicValue -> SymbolicValue) ->
             Cmd SymbolicValue a -> Cmd SymbolicValue a
mapCmd_v f (Match v (Cases bs)) =
  Match (f v) (Cases (map (mapSnd (mapFree_v f)) bs))
mapCmd_v f (Local g t) =
  Local (\ nv -> map (mapSnd f) (g nv)) (mapFree_v f t)
mapCmd_v _ Ask = Ask
mapCmd_v f (App_c g a) =
  App_c (f g) (f a)
mapCmd_v f (Eq_c v_1 v_2) =
  Eq_c (f v_1) (f v_2)
mapCmd_v _ (Fail s) = Fail s

mapFree_v ::  (SymbolicValue -> SymbolicValue) ->
              Thread_s SymbolicValue -> Thread_s SymbolicValue
mapFree_v f (Stop a)    = Stop (f a)
mapFree_v f (Step c k)  = Step (mapCmd_v f c) (fmap f . k)

instance Show (Thread_s SymbolicValue) where
  show (Stop x) = "Stop " ++ show x
  show (Step (Match v (Cases bs)) k) = "Step (Match " ++ show v ++ " (Cases " ++ show bs ++ "))"
  show (Step (Local g t) k) = "Step (Local {-...-} " ++ show t ++ ")"
  show (Step Ask k) = "Step Ask"
  show (Step (App_c g a) k) = "Step (App_c " ++ show g ++ " " ++ show a ++ ")"
  show (Step (Eq_c v_1 v_2) k) = "Step (Eq_c " ++ show v_1 ++ " " ++ show v_2 ++ ")"
  show (Step (Fail s) k) = "Fail " ++ s


--------------------------------
--- monadic helper functions ---
--------------------------------

applySubst :: Unifier -> Thread_s SymbolicValue -> SymbolicSetMonad (Thread_s SymbolicValue)
applySubst u t = do
  (u_0, nu) <- get
  put (u_0 ++ u, nu)
  return t

constrainUnif_N :: Unifier -> Thread_s SymbolicValue -> SymbolicSetMonad (Thread_s SymbolicValue)
constrainUnif_N u t = do
  (u_0, nu) <- get
  put (u_0, nu ++ map (mapFst SymV) u)
  return t

valify :: Patt -> SymbolicSetMonad SymbolicValue
valify (PVar _) = do
  y <- fresh
  return (SymV y)
valify (PCon s ps) = do
  vs <- mmap valify ps
  return (ConV' s vs)

fresh :: SymbolicSetMonad String
fresh = StateT $ \ s ->
  ListT $
  Reader.ReaderT $ \ _ -> do
  i <- get
  put (i + 1)
  return [(("_" ++ show (i + 1)), s)]

fresh' :: SymbolicMonad String
fresh' = do
  i <- get
  put (i + 1)
  return ("_" ++ show (i + 1))

vmatch_s :: (SymbolicValue, Patt) ->
            SymbolicSetMonad (Env SymbolicValue, Unifier)
vmatch_s (v, p) = vsmatch [v] [p]

vsmatch ::  [SymbolicValue] -> [Patt] ->
            SymbolicSetMonad (Env SymbolicValue, Unifier)
vsmatch [] (_:_) = throwError "Pattern match failure"
vsmatch (_:_) [] = throwError "Pattern match failure"
vsmatch []    [] = return ([], [])
vsmatch (ConV' s vs : vs') (PCon s' ps : ps') =
  if (s == s' && length vs == length ps)
  then do
    (nv, u)   <- vsmatch vs ps
    (nv', u') <- vsmatch (map (\ v -> foldr subst v u) vs') ps'
    return (nv ++ nv', u ++ u')
  else throwError "Pattern match failure"
vsmatch (SymV x : vs') (PCon s' ps : ps') = do
  v <- valify (PCon s' ps)
  (nv, u) <- vsmatch [v] [PCon s' ps]
  (nv', u') <- vsmatch (map (\ v' -> subst (x, v) v') vs') ps'
  return (nv ++ nv', (x, v) : u ++ u')
vsmatch (v' : vs) (PVar x : ps) = do
  (nv', u') <- vsmatch vs ps
  return ((x, v') : nv', u')
vsmatch v _ =
  throwError "Pattern match failure"
\end{code}
%endif


\paragraph{Driver Loop}

The driver loop for symbolic execution is generalized to operate on \emph{sets} of possible execution paths, where each execution path is given by a configuration |Config_s|:
\begin{code}
type Config_s a = (a, Env SymbolicValue, Unifier_N)

drive_s ::  [Config_s (Thread_s SymbolicValue)] ->
            SymbolicMonad  (Config_s SymbolicValue,
                           [Config_s (Thread_s SymbolicValue)])
drive_s [] = throwError "No solution found"
drive_s ts =
  case isDone ts of
    (Just c, ts')  -> return (c, ts')
    _              -> do
      ts' <- iterate ts
      drive_s ts'
\end{code}
A configuration comprises a value, an environment which may contain terms with symbolic variables, and a list of negative unification constraints (|Unifier_N|).
The |drive_s| function takes a list of configurations as input, and uses |isDone| to check if one of the input configurations is a value, and returns a pair of that configuration and the remaining configurations.
If none of the input configurations are values already, each input configuration is |iterate|d by a single transition step, and |drive_s| is called recursively on the resulting list of configurations.

%if False
\begin{code}
  where
    isDone ts =
      foldr (\ (t, nv, nu) (status, ts') -> do
                case status of
                  Just v -> (Just v, (t, nv, nu) : ts')
                  Nothing ->
                    case t of
                      Stop v -> (Just (v, nv, nu), ts')
                      _      -> (Nothing, (t, nv, nu) : ts'))
            (Nothing, [])
            ts
    iterate ::  [Config_s (Thread_s SymbolicValue)] ->
                SymbolicMonad [Config_s (Thread_s SymbolicValue)]
    iterate ts =
      foldr (\ (t, nv, nu) ts' ->
               catchError (do ts0 <- Reader.local (\ _ -> nv) (runStep_s (step_s t) nu)
                              ts1 <- ts'
                              return (ts0 ++ ts1))
                          (\ _ -> ts'))
            (return [])
            ts

runStep_s ::  SymbolicSetMonad (Thread_s SymbolicValue) ->
              Unifier_N ->
              SymbolicMonad [Config_s (Thread_s SymbolicValue)]
runStep_s p nu = do
  r <- runListT (runStateT p ([], nu))
  nv <- ask
  foldr (\ (t, (u, nu)) ts -> do
            ts' <- ts
            let nu' = map (mapTuple (\ v' -> foldr subst v' u)) nu
                nv' = map (mapSnd (\ v' -> foldr subst v' u)) nv
                inv = foldr (\ (v_1, v_2) b -> not (v_1 == v_2) && b) True nu' in
              if inv
              then return ((mapFree_v (\ v' -> foldr subst v' u) t, nv', nu') : ts')
              else return ts')
        (return [])
        r
  

runSymbolic :: SymbolicMonad a -> Either String a
runSymbolic m = fmap fst (runExcept (runStateT (runReaderT m []) 0))

runSteps_s ::  Expr -> Env SymbolicValue ->
               Either String (SymbolicValue, [Config_s (Thread_s SymbolicValue)])
runSteps_s e nv = fmap (mapFst (\ (v, _, _) -> v))
                       (runSymbolic (drive_s [(interp e, nv, [])]))
\end{code}
%endif

\paragraph{A Constraint Language for Symbolic Execution}

We have shown how to alter the interpretation of the effects in the definitional interpreter presented in \cref{fig:def-interp}, to derive a symbolic executor from the concrete definitional interpreter from \cref{sec:towards-sym-exc}.
Invoking this symbolic executor with an input program that contains symbolic variables gives rise to a breadth-first search over how these symbolic variables can be instantiated to synthesize a concrete program without symbolic variables in it.
We provide programmers with control over which parts of a program (s)he wishes to synthesize by defining a small constraint language on top of the definitional interpreter from \cref{fig:def-interp}.

The syntax for this constraint language is summarized in \cref{fig:constraint-syntax}.
|CTake n c_x| is a ``top-level'' constraint for picking |n| solutions to a constraint |c_x| that contains existentially quantified symbolic variables.
|CEx x c_x| introduces an existentially quantified symbolic variable, by populating the environment of a symbolic interpreter with a symbolic variable value binding |SymV x_f| for |x|, where |x_f| is a fresh symbolic variable name.
|CEq e_1 e_2| is a constraint that |e_1| and |e_2| evaluate to the same value, and |CNEq e_1 e_2| is a constraint that |e_1| and |e_2| evaluate to different values.

\begin{figure}
\begin{boxedminipage}{0.8\linewidth}
\begin{code}
data Constraint    =  CTake Int ExConstraint
data ExConstraint  =  CEx String ExConstraint
                   |  CEq Expr Expr
                   |  CNEq Expr Expr
\end{code}
%if False
\begin{code}
                   deriving Show
                   deriving Eq
\end{code}
%endif
\end{boxedminipage}
\caption{Syntax for a tiny constraint language}
\label{fig:constraint-syntax}
\end{figure}

Our approach to constraint solving is given by the |solve| function in \cref{fig:constraint-solving} which, in turn, calls the |search_s| function whose type signature is shown in the figure, but whose implementation we omit for brevity.
|search_s e ts ceq n| implements a naive constraint solving strategy which uses a symbolic executor to search for |n| different instantiations of symbolic variables that make the result of symbolic execution of the input expression |e| equal to the result of symbolic execution of a configuration in |ts|, modulo a custom notion of |SymbolicEquality|.

\begin{figure}
\begin{boxedminipage}{\linewidth}
\begin{code}
solve :: Constraint -> SymbolicMonad [Env SymbolicValue]
solve (CTake n c_x) = solve_x c_x n

solve_x ::  ExConstraint -> Int ->
            SymbolicMonad [Env SymbolicValue]
solve_x (CEx x c_x) n = do
  n_x <- fresh'
  Reader.local (\ nv -> (x, SymV n_x) : nv) (solve_x c_x n)
solve_x (CEq e_1 e_2) n = do
  nv <- ask
  search_s e_1 [(interp e_2, nv, [])] unify n
solve_x (CNEq e_1 e_2) n = do
  nv <- ask
  search_s  e_1 [(interp e_2, nv, [])]
            (\ v_1 v_2 ->  case unify v_1 v_2 of
                             Just _   -> Nothing
                             Nothing  -> Just [])
            n

type SymbolicEq =
  SymbolicValue -> SymbolicValue -> Maybe Unifier

search_s ::  Expr ->
             [Config_s (Thread_s SymbolicValue)] ->
             SymbolicEq ->
             Int ->
             SymbolicMonad [Env SymbolicValue]
\end{code}
%if False
\begin{code}
search_s _ _    _   n | n <= 0 = return []
search_s e ts_2 ceq n = do
  ((v_2, nv_2, nu_2), ts_2') <-
    catchError (drive_s ts_2)
               (\ _ -> throwError "Right-hand side unsatisfiable")
  nvs <- match_s [(interp e, nv_2, nu_2)] v_2 ceq n
  nvs' <- search_s e ts_2' ceq (n - length nvs)
  return (nvs ++ nvs')

match_s ::  [Config_s (Thread_s SymbolicValue)] ->
            SymbolicValue ->
            SymbolicEq ->
            Int ->
            SymbolicMonad [Env SymbolicValue]
match_s _    _   _   n | n <= 0 = return []
match_s ts_1 v_2 ceq n = (do
    ((v_1, nv_1, _), ts_1') <- drive_s ts_1
    case ceq v_1 v_2 of
      Just u -> do
        nvs <- match_s ts_1' v_2 ceq (n - 1)
        let nv_1' = map (mapSnd (\ v' -> foldr subst v' u)) nv_1 in
          return (nv_1' : nvs)
      _      ->
        match_s ts_1' v_2 ceq n)
  `catchError` (\ _ -> return [])
\end{code}
%endif
\end{boxedminipage}
\caption{A constraint solver for symbolic execution constraints}
\label{fig:constraint-solving}
\end{figure}


\paragraph{Example: Synthesizing Append Expressions}

To illustrate what we can do with our derived symbolic executor and small constraint language, let us consider list concatenation as an example, inspired by the relational programming techniques and examples given by \citet{ByrdBRM17}.
The |append0| program below grabs a single solution to the constraint which equates |"q"| and the result of concatenating (|append|) a list consisting of three atoms (|a|, |b|, |c|) with a list of two atoms (|d|, |e|):

%if False
\begin{code}
atom :: String -> Expr
atom x = Con x []

--- constraints

(=#=) :: Expr -> Expr -> ExConstraint
(=#=) = CEq

(!=#=) :: Expr -> Expr -> ExConstraint
(!=#=) = CNEq

exists :: String -> ExConstraint -> ExConstraint
exists = CEx

grab :: Int -> ExConstraint -> Constraint
grab = CTake
\end{code}
%endif
\begin{code}
append0 :: Constraint
append0 =
  grab 1 (exists "q"
    ((append  @@  (atom "a" `cons` (atom "b"
                     `cons` (atom "c" `cons` nil)))
              @@  (atom "d" `cons` (atom "e" `cons` nil)))
     `CEq` (var "q")))
\end{code}
Here, |append| is a recursive function defined in the language we are symbolically executing (\cref{fig:syntax}), and |@@| is syntactic sugar for |`App`|.
Solving the |append0| constraint yields the instantiation of |q| to the list contaning all input atoms in sequence.

We can also use symbolic execution to synthesize inputs to functions:
\begin{code}
append01 :: Constraint
append01 =
  grab 1 (exists "q"
    ((append  @@  (var "q")
              @@  (atom "d" `cons` (atom "e" `cons` nil)))
     `CEq` (atom "a" `cons` (atom "b" `cons` (atom "c"
             `cons` (atom "d" `cons` (atom "e" `cons` nil)))))))
\end{code}
Solving the |append01| constraint yields the instantiation of |q| to the list containing the atoms |a|, |b|, |c|.

We can even use symbolic execution to synthesize multiple inputs:
\begin{code}
append02 :: Constraint
append02 =
  grab 6 (exists "x" (exists "y"
    ((append @@ (var "x") @@ (var "y"))
     `CEq` (atom "a" `cons` (atom "b" `cons` (atom "c"
             `cons` (atom "d" `cons` (atom "e" `cons` nil))))))))
\end{code}
Solving the |append02| constraint yields the 6 different possible instantiations of |x| and |y| that satisfy the constraint.

%if False
\begin{code}
ex02 = runSymbolic (solve append02)
\end{code}
%endif

