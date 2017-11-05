{-# LANGUAGE DeriveDataTypeable, TemplateHaskell #-}

import Data.Data
import Luck.Template
import Test.QuickCheck

data Type = TArrow Type Type
          | TList
          | TInt
            deriving (Show, Data)

data Term = Var Int
          | Abs Int Type Term
          | App Type Term Term
            deriving (Show, Data)

gen :: Gen (Maybe Term)
gen = $(mkGenQ defFlags{_fileName="examples/STLC.luck",_maxUnroll=2}) TProxy1
{-# NOINLINE gen #-}

main = sample gen
