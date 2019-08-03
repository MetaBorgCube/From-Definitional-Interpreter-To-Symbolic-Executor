module Sugar where

import Sect02SemStd



--------------------------
--- smart constructors ---
--------------------------


--- expressions

kase :: Expr -> [(Patt, Expr)] -> Expr
kase e patts = Case e patts

(~>) :: Patt -> Expr -> (Patt, Expr)
(~>) = (,)

(~=) :: String -> ValExpr -> (String, ValExpr)
(~=) = (,)

var :: String -> Expr
var = Var

pvar :: String -> Patt
pvar = PVar

fun :: String -> Expr -> Expr
fun x e = Lam x e

vfun :: String -> Expr -> ValExpr
vfun x e = VLam x e

(@@) :: Expr -> Expr -> Expr
f @@ a = App f a

letpar :: [(String, Expr)] -> Expr -> Expr
letpar = Let

letrec :: [(String, ValExpr)] -> Expr -> Expr
letrec = Letrec

(=$=) :: Expr -> Expr -> Expr
(=$=)  = EEq

