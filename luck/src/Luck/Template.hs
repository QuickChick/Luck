{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-missing-fields #-}

module Luck.Template
  ( mkGenQ
  , TProxy (..)
  , tProxy1
  , tProxy2
  , tProxy3
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
import Data.Data (Data)
import Data.Functor.Identity
import qualified Test.QuickCheck.Gen as QC

import Paths_luck

import qualified Data.ByteString as BS

-- * Luck to Haskell

-- | Import a Luck generator as a Haskell value generator at compile time.
--
-- > {-# LANGUAGE TemplateHaskell #-}
-- > {- - @MyType@ should be an instance of @Data@;
-- >    - the definitions of types involved in @MyType@
-- >      should match those in the Luck program;
-- >    - The target predicate (i.e., the last function) should have type
-- >      @MyType -> Bool@.
-- > -}
-- > luckyGen :: QC.Gen (Maybe MyType)
-- > luckyGen = $(mkGenQ defFlags{_fileName="path/to/MyLuckPrg.luck"}) tProxy1
--
-- Depending on the arity of the predicate, use 'tProxy1', 'tProxy2', 'tProxy3',
-- or the 'TProxy' constructors. (The type of the 'TProxy' argument
-- contains the result type of the generator.)
--
-- For example, for a 4-ary predicate of type
-- @A -> B -> C -> D -> Bool@,
-- we can create the following generator:
--
-- > luckGen :: QC.Gen (A, (B, (C, (D, ()))))
-- > luckGen = $(mkGenQ defFlags{_fileName="path/to/MyLuckPrg.luck"})
-- >   (TProxyS . TProxyS . TProxyS . TProxyS $ TProxy0)
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

tProxy1 :: Data a => TProxy a
tProxy1 = TProxyF (\(a, ()) -> a) (TProxyS TProxy0)

tProxy2 :: (Data a, Data b) => TProxy (a, b)
tProxy2 = TProxyF (\(a, (b, ())) -> (a, b)) (TProxyS . TProxyS $ TProxy0)

tProxy3 :: (Data a, Data b, Data c) => TProxy (a, b, c)
tProxy3 = TProxyF (\(a, (b, (c, ()))) -> (a, b, c)) (TProxyS . TProxyS . TProxyS $ TProxy0)

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
