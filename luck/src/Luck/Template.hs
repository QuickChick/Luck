{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-missing-fields #-}
module Luck.Template
  ( mkGenQ
  , TProxy (..)
  , Flags (..)
  , defFlags
  ) where

import Luck.Main

import Language.Haskell.TH
import Language.Haskell.TH.Quote

import System.Random
import Data.Functor.Identity
import qualified Test.QuickCheck.Gen as QC

import Paths_luck

import qualified Data.ByteString.Char8 as BS

-- * Luck to Haskell

-- | Import a Luck generator as a Haskell value generator at compile time.
--
-- > {-# LANGUAGE TemplateHaskell #-}
-- > -- Should satisfy @Data MyType@, and the definitions of types involved in @MyType@
-- > -- should match those in the Luck program.
-- > luckyGen :: QC.Gen (Maybe MyType)
-- > luckyGen = $(mkGenQ "path/to/MyLuckPrg.luck") defFlags TProxy1
mkGenQ :: String -> Q Exp
mkGenQ filename = [|
  \flags proxy -> stdGenToGen (runIdentity (parse
    flags{_fileName = $(literally filename)}
    (BS.pack $(runIO preludeLuck >>= inlineFile))
    (BS.pack $(inlineFile filename))
    (Cont proxy))) |]

literally :: String -> Q Exp
literally = return . LitE . StringL

lit :: QuasiQuoter
lit = QuasiQuoter { quoteExp = literally }

-- | @[litFile|myFile|] :: String@ makes the content of @myFile@ available as a @String@
-- literal.
litFile :: QuasiQuoter
litFile = quoteFile lit

inlineFile :: String -> Q Exp
inlineFile = quoteExp litFile

stdGenToGen :: (StdGen -> a) -> QC.Gen a
stdGenToGen f = QC.MkGen $ \qcGen _ -> f' qcGen
  where f' = f . mkStdGen . fst . next
