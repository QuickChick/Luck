{-# LANGUAGE FlexibleInstances #-}
module Outer.AST.Pretty where

import Common.Pretty
import Outer.AST
import Text.PrettyPrint

-- Hand written pretty-printer
instance PP Op2 where
  pp = text . op2ToString

op2ToString :: Op2 -> String
op2ToString op
  = case op of
      OpPlus -> "+"
      OpMinus -> "-"
      OpTimes -> "*"
      OpDiv -> "/"
      OpMod -> "%"
      OpEq -> "=="
      OpNe -> "/="
      OpLt -> "<"
      OpLe -> "<="
      OpGt -> ">"
      OpGe -> ">="

instance PP Op1 where
  pp = text . op1ToString

op1ToString OpNeg = "-"
op1ToString OpNot = "!"

ppVarId = text
ppConId = text

instance PP Decl where
  pp (FunDecl _ f xs e)
    = hang
        (sep [text "fun", ppVarId f, sep (map (ppVarId . snd) xs), text "="])
        2 (pp e)
  pp d = text $ show d

instance PP Exp where
  pp (Var v) = ppVarId v
  pp (Con c) = ppConId c
  pp (Lit (LitInt i)) = int i
  pp (Unop op1 e) = pp op1 <+> ppParensUnless isAppOrAtom e
  pp (Conj e1 e2) = sep [ ppParensUnless isAppOrAtom e1
                        , text "&&"
                        , ppParensUnless isAppOrAtom e2 ]
  -- | TODO: Pretty-yPrint weights?
  pp (Disj w1 e1 w2 e2) = sep [ ppParensUnless isAppOrAtom e1
                              , text "||"
                              , ppParensUnless isAppOrAtom e2 ]
  pp (Binop e1 op2 e2)
    = sep [ ppParensUnless isAppOrAtom e1
          , pp op2
          , ppParensUnless isAppOrAtom e2 ]
  pp (If e1 e2 e3)
    = sep [ text "if" <+> pp e1
          , text "then" <+> pp e2
          , text "else" <+> pp e3 ]
  pp (Case e alts)
    = sep [ sep [text "case", nest 2 (pp e), text "of"]
          , vcat (map pp alts)
          , text "end" ]
  pp (Let bs e)
    = vcat [text "let" <+> vcat (map pp bs) <+> text "in", pp e]
  pp (App e1 e2)
    = sep [ ppParensUnless isAppOrAtom e1, ppParensUnless isAtomExp e2 ]
  pp (Delay v e)
    = text "[|" <> text v <> char '|' <+> pp e <+> text "|]"
  pp (TRACE _ e) = pp e

isAtomExp (Var _) = True
isAtomExp (Con _) = True
isAtomExp (Lit _) = True
isAtomExp (Delay _ _) = True
isAtomExp e = False

isAppOrAtom (App _ _) = True
isAppOrAtom e = isAtomExp e

instance PP Alt where
  pp (Alt _ w p e)
    = hang
        (hsep [ char '|', pp (maybe (litIntE 1) id w), char '%'
              , pp p, text "->"])
        2 (pp e)

instance PP Pat where
  pp (PApp c ps)
    = ppConId c <+> sep (map (ppParensUnless isAtomPat) ps)
  pp (PVar v) = ppVarId v
  pp PWild = char '_'
  pp _ = error "Unimplemented"

isAtomPat (PApp _ []) = True
isAtomPat e = isDefaultPat e

instance PP Prg where
  pp = vcat . map pp

