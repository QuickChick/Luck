module Core.Types.Pretty where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Common.Pretty
import Common.Types
import Core.Types.Generator

instance PP Void where
  pp _ = text "_"

instance (PP c, PP b) => PP (DataPat' c b) where
  pp = ppDP id

instance PP c => PP (DataTree c) where
  pp = snd . sizedPpDT Nothing id

ppDP p (DPLeaf b) = braces (pp b)
ppDP p (DPCon c []) = pp c
ppDP p (DPCon c cargs) = p . hang (pp c) 2 $ sep (ppDP parens `fmap` cargs)

sizedPpDT :: PP c => Maybe Int -> (Doc -> Doc) -> DataTree c -> (Maybe Int, Doc)
sizedPpDT s p (DInt n) = (s, pp n)
sizedPpDT s p (DCon c []) = (s, pp c)
sizedPpDT (Just 0) _ dt =
  (Just 0, text $ "...[" ++ show (sz dt) ++ " nodes]")
  where sz (DCon _ ts) = 1 + sum (map sz ts)
        sz (DInt _) = 1 :: Int
sizedPpDT s p (DCon c cargs) =
  let (s1, docs) = mapAccumL (\s t -> sizedPpDT s parens t) (decr s) cargs
      doc = p . hang (pp c) 2 $ sep docs
  in (s1, doc)
  where decr = fmap (subtract 1)

ppDataPat :: (PP c, PP tc, PP tv) => DataPat c tc tv -> Doc
ppDataPat = pp

ppInline :: (PP c, PP tc, PP tv) => tc -> [tv] -> [(Int, DataPat c tc tv)] -> Doc
ppInline tc vs alts =
  hang (hsep (pp tc : fmap pp vs) <+> text "=") 2
    . sep . flip map alts
      $ \(w, a) -> text "|" <+> int w <+> text "%" <+> ppDataPat a

ppInlined :: (PP c, PP tc, PP tv) => Map tc ([tv], [(Int, DataPat c tc tv)]) -> Doc
ppInlined inl = vcat . map (\(tc, (vs, alts)) -> ppInline tc vs alts)
  $ Map.toList inl

sizedPpVals s = ((render . vcat) .) . map $ \(v, x) ->
    hang (pp v <> text ":") 2 . snd $ sizedPpDT s id x

