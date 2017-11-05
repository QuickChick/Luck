{-# LANGUAGE TemplateHaskell, RecordWildCards, DeriveDataTypeable #-}
import Control.Monad
import Control.Applicative
import Control.Arrow hiding ((<+>))

import Control.Monad.State

import System.IO
import System.Directory
import System.Process
import Control.Concurrent
import Control.Exception
import System.Exit
import System.IO
import System.IO.Error
import System.Posix.Signals
import System.Process.Internals

import System.Environment
import System.Random
import System.Console.CmdArgs
import System.Exit

import Luck.Template
import Test.QuickCheck

import Data.Data
import Data.Maybe
import Data.List

import System.Directory
import System.Process

import Data.Set (Set)
import qualified Data.Set as Set    
import Data.Data

import Text.PrettyPrint (Doc, (<+>), (<>), ($$))
import qualified Text.PrettyPrint as PP

import qualified Data.Urn as U
import Data.Urn (Urn)
    
data Exp = Var Int
         | Int Int
         | Add Exp Exp
         | Eq Exp Exp
           deriving (Show, Data)

data Stmt = Declare Int          Stmt
          | Asgn Int Exp         Stmt 
          | If Exp Stmt Stmt     Stmt
          | For Int Int Int Stmt Stmt
          | PrintVar Int         Stmt
          | FunCall Int [Exp]    Stmt 
          | Empty
            deriving (Show, Data)

class PP a where 
    pp :: a -> Doc

instance PP Int where
    pp = PP.int 

instance PP Exp where
    pp (Var x) = PP.text $ "var" ++ show x
    pp (Int n) = pp n
    pp (Add e1 e2) = PP.parens $ pp e1 <+> PP.char '+'  <+> pp e2
    pp (Eq e1 e2)  = PP.parens $ pp e1 <+> PP.text "==" <+> pp e2

ppForVar :: Int -> Doc 
ppForVar i = PP.char 'i' <> PP.int i

instance PP Stmt where
    pp (Declare x s) = PP.text "int" <+> pp (Var x) <+> PP.char ';' $$ pp s
    pp (Asgn x e s)  = pp (Var x) <+> PP.char '=' <+> pp e <+> PP.char ';' $$ pp s
    pp (If e s1 s2 s') = PP.text "if" <+> PP.parens (pp e) <+> PP.char '{' 
                                      $$ PP.nest 2 (pp s1)
                                      $$ PP.char '}'
                                      $$ PP.text "else {" 
                                      $$ PP.nest 2 (pp s2)
                                      $$ PP.char '}'
                                      $$ pp s'
    pp (PrintVar n s') = PP.text "printf(\"%d\\n\", " <+> pp (Var n) <+> PP.text ");" $$ pp s'
    pp (FunCall (-2) [] s') = PP.text "empty();" $$ pp s'
    pp (FunCall (-1) [] s') = PP.text "loop();" $$ pp s'
    pp (FunCall fid es s') = 
        PP.char 'a' <> PP.int fid <> PP.char '(' 
              <> PP.hcat (intersperse (PP.char ',') (map pp es))
              <> PP.text ");" $$ pp s'
    pp Empty = PP.empty
    pp (For i low high sfor s') = 
        PP.text "for (int" <+> ppForVar i <+> PP.char '=' <+> PP.int low  <> PP.char ';' 
                           <+> ppForVar i <+> PP.char '<' <+> PP.int high <> PP.char ';'
                           <+> ppForVar i <> PP.text "++) {" 
          $$ PP.nest 2 (pp sfor) 
          $$ PP.text "}"
          $$ pp s'

type Variable = Int
             
data GenState = GS { deadCode :: Bool         -- ^ In dead code or not
                   , declared :: Int          -- ^ Number of declared variables
                   , assigned :: Set Variable -- ^ Set of assigned variables
                   } deriving (Eq, Ord, Show)
             
type CGen = StateT GenState Gen

certain :: Gen a -> Gen (Maybe a)
certain = fmap Just
    
genAssigned :: CGen (Gen (Maybe Variable))
genAssigned = do
  set <- assigned <$> get
  if Set.null set then return $ pure Nothing
  else return $ certain $ elements $ Set.toList set

genInt :: Gen Int
genInt = choose (-10, 10)

genVar :: CGen (Gen (Maybe Variable))
genVar = do
  gs <- get
  if deadCode gs then
      if declared gs == 0 then return $ pure Nothing
      else return $ certain $ choose (0, declared gs - 1)
  else genAssigned 

backtrack :: Urn (Gen (Maybe a)) -> Gen (Maybe a)
backtrack u = do
  (_, g, mu) <- U.remove u
  ma <- g
  case ma of
    Just a -> return $ Just a
    Nothing -> case mu of
                 Just u' -> backtrack u'
                 Nothing -> return Nothing
       
genExp :: Int -> CGen (Maybe Exp)
genExp 0 = do
  g <- genVar
  let urn = fromJust $ U.fromList [ (1, (Var <$>) <$> g)
                                  , (1, (Int <$>) <$> (certain genInt)) ]
  lift $ backtrack urn
  
 

{-
stmtGen :: Gen (Maybe [Stmt])
stmtGen = $(mkGenQ defFlags{_fileName="examples/C.luck", _maxUnroll=2}) tProxy1

runWait c = do
  p <- runCommand c
  waitForProcess p


dump :: [Stmt] -> String -> String -> IO ()
dump (t:ts) fn1 fn2 = do 
  let indices = map fst $ zip [0..] ts
  let tDoc = PP.vcat [ PP.text "void a0(int var0, int var1, int var2) {"
                     , PP.nest 2 $ pp t 
                     , PP.text "}" ]
      tsDoc = PP.vcat $ PP.text "#include <stdio.h>" 
                      : (PP.text "void loop() { while (1) { printf(\"1\"); } }")
                      : (PP.text "void empty() { }")
                      : map (\(i,t) -> 
                                 PP.vcat [ PP.text "void a" <> PP.int i <> PP.text "(int var0, int var1, int var2) {"
                                         , PP.nest 2 $ pp t 
                                         , PP.text "}" ]
                            ) (reverse $ zip [1..] $ ts) 
--  let calls = map (\(i,_) -> PP.text "a" <> PP.int i <+> PP.text "();") (zip [0..] ts)
  let doc = PP.render $ PP.vcat ( PP.text "#include <stdio.h>" 
                                : (map (\(i,_) -> PP.text "extern void a" 
                                                      <> PP.int i <> PP.text "(int x, int y, int z);"
                                               ) (zip [1..] ts)
                                  )
                                ++ [ PP.text "extern void loop(); "
                                   , PP.text "extern void empty(); " ]
                                ++ [ tDoc 
                                   , PP.text "int main() {"
                                   , PP.text "  int undef;"
                                   , PP.text "  a0(undef, 0,1);"
                                   , PP.text "}" ])
  writeFile fn1 doc
  writeFile fn2 (PP.render tsDoc)

compileAndRun :: CFlags -> IO Bool
compileAndRun cflags@CFlags{..} = do
  let fn1 = _outFN ++ "1.c"
      fn2 = _outFN ++ "2.c"
  putStrLn "Compiling...\n"
  -- | Compile 
  e1 <- runWait $ "clang-3.6 -Wno-tautological-compare -Wno-parentheses-equality " 
                  ++ fn1 ++ " " ++ fn2 ++ " -o test.NotOpt" 
  e2 <- runWait $ "clang-3.6 -Wno-tautological-compare -Wno-parentheses-equality -O3"
                  ++ " -mllvm -inline-threshold=10000 "
                  ++ fn1 ++ " " ++ fn2 ++ " -o test.Opt"

  -- | Run and test
  putStrLn "Running and testing outputs...\n"
  (ePlain, outPlain, _) <- readProcessWithExitCode "timeout" [show _timeout, "./test.NotOpt"] ""
  (eOpt, outOpt, _)  <- readProcessWithExitCode "timeout" [show _timeout, "./test.Opt"] ""
  return (outPlain == outOpt)

runSingleBatch :: CFlags -> IO Bool
runSingleBatch cflags@CFlags{..} = do 
  (mts : _ ) <- sample' stmtGen
  case mts of 
    Just ts -> do 
      let fn1 = _outFN ++ "1.c"
          fn2 = _outFN ++ "2.c"
      dump ts fn1 fn2
      compileAndRun cflags
    Nothing -> error "Unsuccesful generation"

-- TODO: Expose Luck options?
data CFlags = CFlags { _numTries :: !Int
                     , _timeout  :: !Double
                     , _outFN    :: String
                     }
             deriving (Eq, Show, Read, Typeable, Data)

cFlags = CFlags { _numTries = 100 
                            &= name "num-tries" &= help "Number of tests to run"
                , _timeout  = 0.1
                            &= name "timeout" &= help "Timeout per-test (s)" 
                , _outFN    = "test"
                            &= name "filename" &= help "Generated .c filename"
                }

main :: IO ()
main = do
  cflags@CFlags{..} <- cmdArgs cFlags
  let aux 0 = putStrLn "Counterexample not found"
      aux n = do 
        b <- runSingleBatch cflags
        if b then putStrLn "Found!"
        else aux $ n-1
  aux _numTries 
-}
