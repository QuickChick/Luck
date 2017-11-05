{-# LANGUAGE TemplateHaskell #-}
import Luck.Template
import Test.QuickCheck

gen :: Gen (Maybe [Bool])
gen = $(mkGenQ defFlags{_fileName="examples/Combination.luck",_maxUnroll=14}) TProxy1

main = sample $ (fmap . fmap . fmap) fromEnum gen
