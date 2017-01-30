module Core.Pretty where

import Common.Util
import Core.AST
import Text.PrettyPrint

import Data.Map(Map)
import qualified Data.Map as Map

printExp v c e = render $ ppExp v c e
printAlt v c a = render $ ppAlt v c a
printPat v c p = render $ ppPat v c p
printAltPats v c as = render $ vcat $ map (\(Alt _ _ p _) -> ppPat v c p) as

--prettyU :: Unknown -> Map VarId O.VarId -> String
prettyU (u,n) m | Just x <- Map.lookup (u,0) m = x ++ "@" ++ show n 
                | otherwise = show (u,n)

ppExp v c (Var u) = parens (char 'V' <+> text (prettyU u v))
ppExp v c (Unknown u) = text (prettyU u v)
ppExp v c (Lit i) = int i
ppExp v c (Unop OpNeg e) = char '-' <+> ppExp v c e
ppExp v c (Binop e1 op e2) = parens (ppExp v c e1 <+> text (show op) <+> ppExp v c e2)
ppExp v c (If e1 e2 e3) = text "if " <+> ppExp v c e1 <+> text " then " $$
                          ppExp v c e2 $$ text " else " <+> ppExp v c e3
ppExp v c (ADT cid es) = text (c ! cid) $$ (nest 2 (vcat (map (ppExp v c) es)))
ppExp v c (Case e alts) = text "CASE " <+> ppExp v c e $$ (nest 2 (vcat $ map (ppAlt v c) alts))
ppExp v c (Inst e u) = text "Inst " <+> ppExp v c e <+> text (prettyU u v)
ppExp v c (Fresh u en e) = text ("Fresh " ++ prettyU u v ++ " :: ") <+> ppExp v c en <+> text " in " <+> ppExp v c e
ppExp v c (Fix e) = text "Fix " <+> ppExp v c e
ppExp v c (FixN n e) = text "FixN " <+> int n <+> ppExp v c e
ppExp v c (Fun vs e) = text "Fun" <+> hcat (map (text . show . fst) vs) <+> (ppExp v c e)
-- Trace 
-- Collect 
ppExp v c (Call (Var f) es) = text (v ! (fst f, 0)) $$ (nest 2 $ vcat (map (ppExp v c) es))
ppExp v c (Call e es) = ppExp v c e $$ (nest 2 $ vcat (map  (ppExp v c) es))
ppAlt v c (Alt _ ew p e) = text "ALT {" <+> ppExp v c ew <+> text "} " <+> ppPat v c p $$ nest 2 (text " |-> " <+> ppExp v c e)

ppPat v c PWild = char '_'
ppPat v c (PApp cid ps) = text (c ! cid) $$ (nest 2 $ vcat (map (ppPat v c) ps))
ppPat v c (PLit n) = int n
ppPat v c (PVar u) = text (prettyU u v)
