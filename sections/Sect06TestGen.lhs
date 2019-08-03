%if False
\begin{code}
module Sect06TestGen where

import Sect02SemStd
import Sect04SymExc
import Lib
import Sugar

\end{code}
%endif

\section{Case Study: Automatic Test Generation for Definitional Interpreters}

\label{sec:case-study}

The language we have defined a symbolic executor for (syntax in \cref{fig:syntax}) is well-suited for implementing definitional interpreters in.
In order to test the symbolic executor we have developed, we have defined various interpreters for the simply-typed lambda calculus.
Specifically, we have implemented a canonical, environment-based interpreter, and variations on this interpreter with scoping mistakes.
Symbolic execution is able to automatically synthesize test programs that will detect these mistakes, by looking for programs whose results differ between the correct interpreter and the wrongly-scoped interpreter.
For brevity, we have omit discussion of these test cases, but the Haskell version of this paper contains the test cases that we invite interested readers to consult.
Using GHCi (v8.6.4), symbolic execution takes <1s to synthesize each test program.


%if False
\begin{code}
--------------------------------------------
--- expressions for interpreted language ---
--------------------------------------------

lambda :: String -> Expr -> Expr
lambda x e = Con "lambda" [Con ("__" ++ x) [], e] -- atoms as vars

plambda :: Patt -> Patt -> Patt
plambda x e = PCon "lambda" [x, e]

ap :: Expr -> Expr -> Expr
ap f a = Con "app" [f, a]

papp :: Patt -> Patt -> Patt
papp f a = PCon "app" [f, a]

kvar :: String -> Expr -- atoms as vars
kvar x = Con "var" [Con ("__" ++ x) []]

pkvar :: Patt -> Patt
pkvar p = PCon "var" [p]


---------------------------------------
--- values for interpreted language ---
---------------------------------------

closv :: Expr -> Expr -> Expr -> Expr
closv x e nv = Con "closv" [x, e, nv]

pclosv :: Patt -> Patt -> Patt -> Patt
pclosv x e nv = PCon "closv" [x, e, nv]


-------------------
--- interpreter ---
-------------------

eval :: Expr
eval =
  letrec ( "eval" ~= (vfun "e" $ fun "nv" $
             kase (var "e") $
               punit ~>
                 unit
             : (pkvar (pvar "x")) ~>
                 (kijk @@ var "x" @@ var "nv")
             : (plambda (pvar "x") (pvar "body")) ~>
                 (closv (var "x") (var "body") (var "nv"))
             : (papp (pvar "f") (pvar "a")) ~>
                 (kase (var "eval" @@ var "f" @@ var "nv") $
                   (pclosv (pvar "x") (pvar "body") (pvar "nv_clo")) ~>
                     (var "eval" @@ var "body" @@
                       (cons (pair (var "x") (var "eval" @@ var "a" @@ var "nv"))
                             (var "nv_clo")))
                 : [])
             : [])
         : [])
    (var "eval")


--------------------------------------
--- dynamically-scoped interpreter ---
--------------------------------------

evil :: Expr
evil =
  letrec ( "evil" ~= (vfun "e" $ fun "nv" $
             kase (var "e") $
               punit ~>
                 unit
             : (pkvar (pvar "x")) ~>
                 (kijk @@ var "x" @@ var "nv")
             : (plambda (pvar "x") (pvar "body")) ~>
                 (closv (var "x") (var "body") (var "nv"))
             : (papp (pvar "f") (pvar "a")) ~>
                 (kase (var "evil" @@ var "f" @@ var "nv") $
                   (pclosv (pvar "x") (pvar "body") (pvar "nv_clo")) ~>
                     (var "evil" @@ var "body" @@
                       (cons (pair (var "x") (var "evil" @@ var "a" @@ var "nv"))
                             (var "nv")))
                 : [])
             : [])
         : [])
    (var "evil")


--------------------------------------------------
--- differently-dynamically-scoped interpreter ---
--------------------------------------------------

evil' :: Expr
evil' =
  letrec ( "evil" ~= (vfun "e" $ fun "nv" $
             kase (var "e") $
               punit ~>
                 unit
             : (pkvar (pvar "x")) ~>
                 (kijk @@ var "x" @@ var "nv")
             : (plambda (pvar "x") (pvar "body")) ~>
                 (closv (var "x") (var "body") (var "nv"))
             : (papp (pvar "f") (pvar "a")) ~>
                 (kase (var "evil" @@ var "f" @@ var "nv") $
                   (pclosv (pvar "x") (pvar "body") (pvar "nv_clo")) ~>
                     (var "evil" @@ var "body" @@
                       (cons (pair (var "x") (var "evil" @@ var "a" @@ var "nv"))
                             (append @@ (var "nv_clo") @@ (var "nv"))))
                 : [])
             : [])
         : [])
    (var "evil")


----------------------------------
--- wrongly-scoped interpreter ---
----------------------------------

evil'' :: Expr
evil'' =
  letrec ( "evil" ~= (vfun "e" $ fun "nv" $
             kase (var "e") $
               punit ~>
                 unit
             : (pkvar (pvar "x")) ~>
                 (kijk @@ var "x" @@ var "nv")
             : (plambda (pvar "x") (pvar "body")) ~>
                 (closv (var "x") (var "body") (var "nv"))
             : (papp (pvar "f") (pvar "a")) ~>
                 (kase (var "evil" @@ var "f" @@ var "nv") $
                   (pclosv (pvar "x") (pvar "body") (pvar "nv_clo")) ~>
                     (var "evil" @@ var "body" @@
                       (cons (pair (var "x") (var "evil" @@ var "a" @@ var "nv_clo"))
                             (var "nv_clo")))
                 : [])
             : [])
         : [])
    (var "evil")


------------------
--- constraint ---
------------------

test_eval_neq_evil :: Constraint
test_eval_neq_evil =
  grab 1 $
    exists "e" $
      (eval @@ (var "e") @@ nil) !=#= (evil @@ (var "e") @@ nil)

-- runConcolic (solve test_eval_neq_evil)

test_eval_neq_evil_app :: Constraint
test_eval_neq_evil_app =
  grab 2 $
    exists "e" $
        (eval @@ (ap (ap (var "e") unit) unit) @@ nil) !=#= (evil @@ (ap (ap (var "e") unit) unit) @@ nil)

-- runConcolic (solve test_eval_neq_evil_app)


test_eval_neq_evil' :: Constraint
test_eval_neq_evil' =
  grab 1 $
    exists "e" $
      (eval @@ (var "e") @@ nil) !=#= (evil' @@ (var "e") @@ nil)

-- runConcolic (solve test_eval_neq_evil')

test_eval_neq_evil'' :: Constraint
test_eval_neq_evil'' =
  grab 1 $
    exists "e" $
      (eval @@ (var "e") @@ nil) !=#= (evil'' @@ (var "e") @@ nil)

-- runConcolic (solve test_eval_neq_evil'')

\end{code}
%endif
