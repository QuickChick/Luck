{-# LANGUAGE TemplateHaskell #-}
import Luck.Template
import Test.QuickCheck

gen :: Gen (Maybe [Bool])
gen = $(mkGenQ "examples/Combination.luck") defFlags{_maxUnroll=14} TProxy1

main = sample $ (fmap . fmap . fmap) fromEnum gen
