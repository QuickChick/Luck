-- Not DRY at all with Outer.AST.Pretty
module Core.AST.Pretty where

import Common.Pretty
import Core.AST
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

ppVarId :: VarId -> Doc
ppVarId (a, b) = text $ "v_" ++ show a ++ "_" ++ show b

ppUnknown :: VarId -> Doc
ppUnknown (a, b) = text $ "u_" ++ show a ++ "_" ++ show b

ppConId :: ConId -> Doc
ppConId c = text $ "c_" ++ show c

instance PP Decl where
  pp (FunDecl _ f xs e)
    = hang (sep [text "fun", ppVarId f, sep (map ppVarId xs), text "="]) 2 (pp e)

instance PP Exp where
  pp (Var v) = ppVarId v
  pp (Unknown u) = ppUnknown u
  pp (Lit i) = int i
  pp (Unop op1 e) = pp op1 <+> ppParensUnless isCallOrAtom e
  pp (Conj e1 e2) = ppParensUnless isCallOrAtom e1 <+> text "&&" <+> ppParensUnless isCallOrAtom e2
  pp (Disj w1 e1 w2 e2) = ppParensUnless isCallOrAtom e1 <+> text "||" <+> ppParensUnless isCallOrAtom e2
  pp (Binop e1 op2 e2)
    = ppParensUnless isCallOrAtom e1
      <+> pp op2 <+> ppParensUnless isCallOrAtom e2
  pp (If e1 e2 e3)
    = text "if" <+> pp e1
      <+> text "then" <+> pp e2
      <+> text "else" <+> pp e3
  pp (Case e alts)
    = sep [ sep [text "case", nest 2 (pp e), text "of"]
          , vcat (map pp alts)
          , text "end"]
  pp (Let bs e)
    = text "let" <+> vcat (map pp bs) <+> text "in" <+> pp e
  pp (ADT c es) = ppConId c <+> sep (map (ppParensUnless isAtomExp) es)
  pp (Call f es) = ppVarId f <+> sep (map (ppParensUnless isAtomExp) es)
  pp (Fix vs e)
    = text "Fix" <+> braces (sep (map ppVarId vs) <> char '|' <+> pp e)
  pp (FixN n e)
    = text "Fix" <+> braces (int n <> char '|' <+> pp e)
  pp (Partition v e)
    = brackets (ppVarId v <> char '|' <+> pp e)

isAtomExp (Var _) = True
isAtomExp (Lit _) = True
isAtomExp (Fix _ _) = True
isAtomExp (FixN _ _) = True
isAtomExp (Partition _ _) = True
isAtomExp e = False

isCallOrAtom (Call _ _) = True
isCallOrAtom e = isAtomExp e

instance PP Alt where
  pp (Alt _ w p e)
    = hang
        (hsep [ char '|', pp w, char '%', pp p, text "->"])
        2 (pp e)

instance PP Pat where
  pp (PApp c ps)
    = ppConId c <+> sep (map (ppParensUnless isAtomPat) ps)
  pp (PVar v) = ppVarId v
  pp PWild = char '_'
  pp _ = error "Unimplemented"

isAtomPat (PApp _ []) = False
isAtomPat _ = True

ppPrg :: Prg -> Doc
ppPrg = vcat . map pp

