{-# LANGUAGE TemplateHaskell, DeriveDataTypeable #-}
import Control.Monad
import Control.Applicative
import Control.Arrow

import Luck.Template
import Test.QuickCheck

import Data.Data
import Data.Maybe
import Data.List

import System.Directory
import System.Process

import Data.Data

data Type = TArrow Type Type
          | TList 
          | TInt
            deriving (Show, Data)

sizeT :: Type -> Int
sizeT (TArrow t1 t2) = 1 + sizeT t1 + sizeT t2
sizeT _ = 1

data Term = Var Int
          | Abs Int Type Term
          | App Type Term Term
            deriving (Show, Data)

size :: Term -> Int
size (Var _) = 1
size (Abs _ t e) = 1 + sizeT t + size e
size (App t e1 e2) = 1 + sizeT t + size e1 + size e2


mapping :: Int -> String
mapping 0 = "(undefined :: Int)"
mapping 1 = "id"
mapping 2 = "seq"
mapping 3 = "id"
mapping 4 = "seq"
mapping n = "x" ++ show n

unparse :: Term -> String
unparse (Var x) = mapping x
unparse (Abs n _ e) = "(\\" ++ mapping n ++ " -> " ++ unparse e ++ ")"
unparse (App _ e1 e2) = "(" ++ unparse e1 ++ " " ++ unparse e2 ++ ")"

ghcGen :: Gen (Maybe Term)
ghcGen = $(mkGenQ defFlags{_fileName="examples/STLC.luck", _maxUnroll=2}) tProxy1

--main = do 
--  (x:_) <- sample' gen 
--  case x of 
--    Just t  -> putStrLn $ unparse t
--    Nothing -> putStrLn "NOTHING"

runWait c = do
  p <- runCommand c
  waitForProcess p

generateAndPack :: IO ()
generateAndPack = do 
  -- | Generate a file
  putStrLn "Generating 1100 tests...\n"
  let tmp = "examples-template/Main.hs"
  funs <- (catMaybes . concat) <$> (replicateM 10 $ sample' ghcGen)
  putStrLn "Writing to haskell module...\n"
  copyFile "examples-template/ModuleIntro.txt" tmp
  let appendString = "  " ++ (concat $ intersperse ",\n  " (fmap unparse funs))
  appendFile tmp appendString
  appendFile tmp "  ]\n"

compileAndRun :: String -> IO Bool
compileAndRun fileBase = do
  let dotO  = fileBase ++ ".o"
      dotHs = fileBase ++ ".hs" 
  putStrLn "Compiling...\n"
  -- | Compile 
  runWait $ "rm " ++ dotO
  e1 <- runWait $ "ghc-6.12.1 -o Main " ++ dotHs
  runWait $ "rm " ++ dotO
  -- | Run and test
  putStrLn " Running and testing outputs...\n"
  e2 <- runWait $ "ghc-6.12.1 -o MainOpt -O2 " ++ dotHs
  (ePlain, outPlain, _) <- readProcessWithExitCode "./Main" [] ""
  (eOpt, outOpt, _)  <- readProcessWithExitCode "./MainOpt" [] ""
  return (outPlain == outOpt)

main :: IO ()
main = do 
  -- Calculate sizes
  funs <- (catMaybes . concat) <$> (replicateM 1 $ sample' ghcGen)
--  putStrLn $ show $ sum $ fmap size funs
  generateAndPack
  b <- compileAndRun "examples-template/Main"
  if b then putStrLn "New Batch\n" -- >> main
  else do 
    putStrLn "Counterexample Found!"
    files <- getDirectoryContents "examples-template/ghc-counters"
    copyFile "examples-template/Main.hs" ("examples-template/ghc-counters/" 
                                     ++ (show $ length files) 
                                     ++ ".hs")
