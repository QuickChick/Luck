{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Common.Pretty
  ( PP(..)
  , PPShow(..)
  , ppParensUnless
  , render
  , prettyPrint
  , module Text.PrettyPrint
  ) where

import Text.PrettyPrint hiding (render)

class PP a where
    pp :: a -> Doc

instance PP Doc where
  pp = id

instance PP String where
  pp = text

instance PP Int where
  pp = int

newtype PPShow a = PPShow a

ppParensUnless :: PP a => (a -> Bool) -> a -> Doc
ppParensUnless p e = (if p e then id else parens) (pp e)

render :: Doc -> String
render = renderStyle style { lineLength = 80 }

prettyPrint :: PP a => a -> IO ()
prettyPrint = putStrLn . render . pp

