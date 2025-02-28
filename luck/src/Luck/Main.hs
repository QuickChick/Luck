{-# LANGUAGE TupleSections, RecordWildCards,
    DeriveDataTypeable, BangPatterns, LambdaCase, GADTs
  #-}
module Luck.Main where

import Control.Monad
import Control.Monad.Random

import Common.Pretty (render, prettyPrint, pp)
import Common.SrcLoc
import Common.Util
import Common.Types hiding (subst)
import Common.Conversions (convertToCore, CoreTranslation(..), iBuiltIn)
import Outer.Parser
import Outer.ParseMonad
import Outer.Renamer(rename)
import Outer.Types(typeInference, removeClassBindings)
import Outer.Expander(expandWildcards)
import Outer.ClassMono(monomorphiseClasses)

import Core.AST
import qualified Outer.AST as OAST
import Core.CSet
import Core.Semantics hiding (rename)
import Core.Optimizations
import Core.Pretty

import Debug.Trace

import Paths_luck

import System.Environment
import System.Random
import System.Console.CmdArgs
import System.Exit
import qualified System.FilePath as FN

import Data.Functor.Identity
import Data.Map(Map)
import qualified Data.Map as Map

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8

import Core.Rigidify (DataTree)
import qualified Core.Rigidify as Rigidify

data RunMode = Single | Evaluate
  deriving (Eq, Show, Read, Typeable, Data)

-- This is a hack which allows to reuse the existing huge main function without
-- packing/unpacking the whole context of intermediate computations,
-- which introduce a lot of variables.
data Returns m a where
  RunSingle :: Returns IO ()
  RunEvaluate :: Returns IO ()
  Cont :: TProxy a -> Returns Identity (StdGen -> Maybe a)

data TProxy a where
  TProxy0 :: TProxy ()
  TProxyS :: Data a => TProxy b -> TProxy (a, b)
  TProxyF :: (a -> b) -> TProxy a -> TProxy b

runModeReturns Single = RunSingle
runModeReturns Evaluate = RunEvaluate

data Flags = Flags { _fileName :: String
                   , _function :: Maybe String
                   , _runMode  :: RunMode
                   , _evalTries :: Int
                   -- , _tryGenerator :: Maybe (String, Int, Int)
                   , _fullOutput :: Int
                   , _noSample :: Bool
                   , _maxUnroll :: Int
                   -- , _warnings :: Bool
                   , _maxBacktrack :: Int
                   , _defDepth :: Int
                   , _intRangeMin :: Int
                   , _intRangeMax :: Int
                   }
             deriving (Eq, Show, Read, Typeable, Data)

defFlags = Flags { _fileName = "" &= argPos 0 &= typFile
                 , _function = Nothing &= name "fun"
                 , _runMode  = Single  &= name "mode"
                 , _evalTries = 1000  &= name "reps"
                 -- , _tryGenerator = Nothing &= name "debug-trygen"
                 --     &= typ "TYPE,SIZE,RPT"
                 --     &= help "Generate RPT random values of type TYPE \
                 --             \with size SIZE, ex: \"[[Bool]]\",14,4"
                 , _fullOutput = 5 &= name "f" &= name "full-output"
                     &= opt (0 :: Int)
                     &= help "With no argument, do not truncate the output. \
                             \With INT, keep INT internal nodes."
                 , _noSample = False &= name "no-sample"
                     &= help "Do not sample holes"
                 , _maxUnroll = 0 &= name "maxUnroll"
                     &= help "Maximum number of times to unroll a function"
                 -- , _warnings = True &= name "warnings"
                 , _maxBacktrack = maxBound &= name "max-backtrack"
                 , _defDepth = 10 &= name "default-depth"
                 , _intRangeMin = -42 &= name "irmin" &= help "Bottom of default int range"
                 , _intRangeMax =  42 &= name "irmax" &= help "Top of default int range"
                 }

preludeLuck = getDataFileName "src/Luck/Prelude.luck"

main :: IO ()
main = do
  flags@Flags{..} <- cmdArgs defFlags
  ast <- getOAST flags
  parse flags ast (runModeReturns _runMode)

handleIncludes :: String -> OAST.Decl -> IO [OAST.Decl]
handleIncludes relPath (OAST.IncludeDecl fileName) = do
    newFile <- BS.readFile (relPath FN.</> (fileName ++ ".luck"))
    let pState = mkPState newFile (SrcLoc fileName 1 1)
    newAst <- failEither $ runP parser pState 
    handleAllInclusions relPath newAst
handleIncludes _ x = return [x]

handleAllInclusions :: String -> [OAST.Decl] -> IO [OAST.Decl]
handleAllInclusions relPath l = concat <$> mapM (handleIncludes relPath) l

getOAST :: Flags -> IO OAST.Prg
getOAST flags@Flags{..} = do
  preludePath <- preludeLuck
  prelude <- BS.readFile preludePath
  contents <- BS.readFile _fileName
  let relativePath = FN.takeDirectory _fileName
  parseFiles flags relativePath prelude contents

parseFiles Flags{..} relativePath prelude contents = do
  astPrelude <- failEither $ runP parser $ mkPState prelude (SrcLoc "Prelude" 1 1)
  let pState = mkPState contents (SrcLoc _fileName 1 1)
  astOriginal <- failEither $ runP parser pState
  astIncluded <- handleAllInclusions relativePath astOriginal
  return (astPrelude ++ astIncluded)

parse :: (Monad m, MonadFail m) => Flags -> OAST.Prg -> Returns m a -> m a
parse Flags{..} ast r = do
  (fwdRenMap, revRenMap, astRenamed) <- failEither $ rename ast
--  traceM $ unlines (map show astRenamed)
  (astAnnotated, tcEnv') <- failEither $ typeInference astRenamed
--  traceM $ unlines (map show astAnnotated)
  (astClass, tcEnv'') <- failEither $ monomorphiseClasses astAnnotated tcEnv'
--  traceM $ unlines (map show astClass)
  let tcEnv = removeClassBindings astAnnotated tcEnv''
--  traceShowM ("TC:", tcEnv)
--  traceM $ unlines ("DeClassed:" : map show astClass)
  -- TODO: -42..42 needs to *at least* be parameterized
  astExpanded <- failEither $ expandWildcards astClass tcEnv (-42) 42
--  traceM $ unlines ("EXPANDED:" : map show astExpanded)
  coreResult <- failEither $ convertToCore fwdRenMap tcEnv astExpanded _defDepth
  let topFuns = gatherTopFuns $ ct_prog coreResult
      toFItem (fid, args, e) = (fid, FItem args e)
      initFMap = Map.fromList (map toFItem topFuns)
  (fid, FItem args e) <- case _function of
              Nothing -> return $ toFItem $ last topFuns
              Just f -> error "implement specific function test"
  let conTrue  = ct_cEnv coreResult ! "True"
      conFalse = ct_cEnv coreResult ! "False"
      c = ct_cRev coreResult
      v = ct_vRev coreResult
      args' = map fst args
      e' = subst e args' (map Unknown args')
      (eFinal, idx0, step, fenvFinal) = inlineAndPropagate v c conTrue conFalse _maxUnroll initFMap e'
      rs = mkReaderState fenvFinal (ct_tcEnv coreResult) (ct_vRev coreResult) (ct_cRev coreResult) conTrue conFalse (_intRangeMin, _intRangeMax)
      fbs = mkFBState (idx0+1) step _maxBacktrack
      k = initCtrSet args
      -- Value rigidification
      (fid', _) = fid
      Forall _ fty = varEnv (ct_tcEnv coreResult) Map.! (fid', 0)
      (argTys, _) = unFun fty
      typedArgs = zip args' argTys
      dataGens :: MonadRandom n => Rigidify.DataGenMap' n
      dataGens = Rigidify.simpleMake (ct_tcEnv coreResult) (iBuiltIn (ct_cEnv coreResult))
      finalize :: MonadRandom n => CtrSet -> n (CtrSet, [DataTree ConId])
      finalize k = case _noSample of
        True -> return (Rigidify.partializeTargets k args')
        False -> Rigidify.finalizeTargets (ct_tcEnv coreResult) dataGens k typedArgs
      oArgs = map (ct_vRev coreResult Map.!) args'
      oValues :: [DataTree ConId] -> [DataTree String]
      oValues = fmap . fmap $ conName
      conName = \case
        -777 -> "_" -- Unconstrained ADT
        -888 -> "_'" -- Unconstrained Int
        c -> ct_cRev coreResult Map.! c
      nonZero 0 = Nothing
      nonZero n = Just n
      run_ :: (ReaderState -> FBState -> Exp -> Pat -> CtrSet -> t1 -> t) -> t1 -> t
      run_ runLuck g = runLuck rs fbs eFinal (PApp conTrue []) k g
      run = run_ runLuck
      run' = run_ runLuck'

--  putStrLn $ show (idx0+1, step)
--  forM_ (Map.assocs fenvFinal) $ \(fid, FItem args e) -> do
--      putStrLn $ (((ct_vRev coreResult) ! fid) ++ " : ")
--      putStrLn $ printExp (ct_vRev coreResult) (ct_cRev coreResult) e
--  putStrLn $ printExp (ct_vRev coreResult) (ct_cRev coreResult) eFinal
  case r of
    RunSingle -> do
--      putStrLn $ printExp (ct_vRev coreResult) (ct_cRev coreResult) eFinal
      g <- getStdGen
      case run g of
        Right (_,k') -> do
--          traceShowM ("Ran", k')
          (k'', vs) <- finalize k'
          Rigidify.ppBindings _fullOutput oArgs (oValues vs)
        Left err -> error err
    RunEvaluate ->
      let aux !cnt 0 = return cnt
          aux !cnt n = do
            g <- newStdGen
            case run g of
              Right (_,k') ->
                  aux (cnt + countFor k' args') (n-1)
              Left _ -> aux cnt n
      in do
        g <- getStdGen
        res <- aux 0 _evalTries
        putStrLn $ show res
    Cont p ->
      let
        convert_ :: Data a => DataTree ConId -> a
        convert_ = Rigidify.convert conName (conIndices (ct_tcEnv coreResult))
        convert' :: TProxy a -> [DataTree ConId] -> a
        convert' TProxy0 [] = ()
        convert' (TProxyS p) (x : xs) = strictPair (convert_ x) (convert' p xs)
        convert' (TProxyF f p) xs = f (convert' p xs)
        convert' _ _ = error "convert': arity mismatch"
        f = convert' p
      in
        return $ \g ->
          case run' g of
            Right (((_,k'), _), g) -> Just (f (evalRand (snd <$> finalize k') g))
            Left _ -> Nothing

strictPair :: a -> b -> (a, b)
strictPair x y = x `seq` y `seq` (x, y)
