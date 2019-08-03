module Lib where

import Sect02SemStd
import Sugar

-------------
--- lists ---
-------------

cons :: Expr -> Expr -> Expr
cons hd tl = Con "cons" [hd, tl]

nil :: Expr
nil = Con "nil" []

pcons :: Patt -> Patt -> Patt
pcons hd tl = PCon "cons" [hd, tl]

pnil :: Patt
pnil = PCon "nil" []

append :: Expr
append =
  letrec ( "append" ~= (vfun "xs" $ fun "ys" $
             kase (var "xs") $
               pnil ~> var "ys"
             : (pcons (pvar "hd") (pvar "tl")) ~>
                 (cons (var "hd") (var "append" @@ var "tl" @@ var "ys"))
             : [])
         : [])
    (var "append")

kreverse :: Expr
kreverse =
  letrec ( "reverse" ~= (vfun "xs" $
             kase (var "xs") $
               pnil ~> nil
             : (pcons (pvar "hd") (pvar "tl")) ~>
                 (append @@ (var "reverse" @@ var "tl") @@
                   cons (var "hd") nil)
             : [])
         : [])
    (var "reverse")


----------------
--- booleans ---
----------------

ktrue :: Expr
ktrue = Con "true" []

kfalse :: Expr
kfalse = Con "false" []

ptrue :: Patt
ptrue = PCon "true" []

pfalse :: Patt
pfalse = PCon "false" []


------------
--- nats ---
------------

sukk :: Expr -> Expr
sukk n = Con "succ" [n]

zero :: Expr
zero = Con "zero" []

psukk :: Patt -> Patt
psukk p = PCon "succ" [p]

pzero :: Patt
pzero = PCon "zero" []

kplus :: Expr
kplus =
  letrec ( "plus" ~= (vfun "n" $ fun "m" $
             kase (var "n") $
                 pzero ~> var "m"
               : psukk (pvar "n'") ~> sukk (var "plus" @@ var "n'" @@ var "m")
               : [])
         : [])
  
    (var "plus")


------------
--- unit ---
------------

unit :: Expr
unit = Con "()" []

punit :: Patt
punit = PCon "()" []


-------------
--- pairs ---
-------------

pair :: Expr -> Expr -> Expr
pair e1 e2 = Con "pair" [e1, e2]

ppair :: Patt -> Patt -> Patt
ppair p1 p2 = PCon "pair" [p1, p2]

proj1 :: Expr
proj1 = letrec ( "proj1" ~= (vfun "p" $
                   kase (var "p") $
                     ppair (pvar "x") (pvar "_") ~>
                       (var "x")
                   : [])
               : [])
          (var "proj1")

proj2 :: Expr
proj2 = letrec ( "proj2" ~= (vfun "p" $
                   kase (var "p") $
                     ppair (pvar "_") (pvar "x") ~>
                       (var "x")
                   : [])
               : [])
          (var "proj2")


-------------------------------
--- association list lookup ---
-------------------------------

kijk :: Expr
kijk = letrec ( "kijk" ~= (vfun "x" $ fun "l" $
                  kase (var "l") $
                    (pcons (ppair (pvar "y") (pvar "v")) (pvar "tl") ~>
                       (kase (var "x" =$= var "y") $
                          ptrue  ~> (var "v")
                        : pfalse ~> (var "kijk" @@ var "x" @@ var "tl")
                        : []))
                    : [])
              : [])
         (var "kijk")
