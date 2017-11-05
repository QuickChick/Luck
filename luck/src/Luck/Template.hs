{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-missing-fields #-}

module Luck.Template
  ( mkGenQ
  , TProxy (..)
  , Flags (..)
  , defFlags
  ) where

import Common.SrcLoc (SrcLoc(..))
import Common.Types
import Outer.AST
import Luck.Main

import Language.Haskell.TH.Syntax (Lift(..), Q, runIO)
import qualified Language.Haskell.TH as TH

import System.Random
import Data.Functor.Identity
import qualified Test.QuickCheck.Gen as QC

import Paths_luck

import qualified Data.ByteString as BS

-- * Luck to Haskell

-- | Import a Luck generator as a Haskell value generator at compile time.
--
-- > {-# LANGUAGE TemplateHaskell #-}
-- > -- Should satisfy @Data MyType@, and the definitions of types involved in @MyType@
-- > -- should match those in the Luck program.
-- > luckyGen :: QC.Gen (Maybe MyType)
-- > luckyGen = $(mkGenQ defFlags{_fileName="path/to/MyLuckPrg.luck"}) TProxy1
mkGenQ :: Flags -> Q TH.Exp
mkGenQ flags = do
  ast <- runIO $ getOAST flags
  [| \proxy -> stdGenToGen (runIdentity (parse
      $(lift flags)
      $(lift ast)
      (Cont proxy))) |]

stdGenToGen :: (StdGen -> a) -> QC.Gen a
stdGenToGen f = QC.MkGen $ \qcGen _ -> f' qcGen
  where f' = f . mkStdGen . fst . next

deriving instance Lift RunMode
deriving instance Lift Flags
deriving instance Lift ConDecl
deriving instance Lift Decl
deriving instance Lift Exp
deriving instance Lift TyVarId'
deriving instance Lift Pat
deriving instance Lift Literal
deriving instance Lift Alt
deriving instance Lift Op1
deriving instance Lift Op2
deriving instance Lift SrcLoc
deriving instance (Lift c, Lift v) => Lift (TcType c v)
