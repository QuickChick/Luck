{-# LANGUAGE RecordWildCards #-}
module Common.Conversions (convertToCore, CoreTranslation(..), iBuiltIn) where

import Common.Types
import qualified Outer.AST as O
import Outer.Types (oBuiltIn)
import qualified Core.AST  as I

import Common.Error
import Common.SrcLoc
import Common.Util

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Lens
import Control.Arrow

import Data.Maybe
import Data.List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Common.Pretty
import Text.PrettyPrint.HughesPJ (Doc, (<+>))
import qualified Text.PrettyPrint.HughesPJ as PP

import Debug.Trace

data CoreTranslation = CT { ct_prog  :: I.Prg
                          , ct_tcEnv :: I.TcEnv 
                          , ct_vEnv  :: Map O.VarId I.VarId
                          , ct_vRev  :: Map I.VarId O.VarId
                          , ct_cEnv  :: Map O.ConId I.ConId
                          , ct_cRev  :: Map I.ConId O.ConId 
                          } deriving (Show)

convertToCore :: Map O.VarId O.VarId -> O.OTcEnv -> O.Prg -> 
                 Int -> 
                 Either Message CoreTranslation
convertToCore vrRev tcEnv@TcEnv{..} prg defDepth = 
    let cons  = Map.keys conEnv 
        cons' = [0..length cons]
        conenv' = Map.fromList $ zip cons  cons'
        conRev' = Map.fromList $ zip cons' cons
    in do 
      (prg', venv', vrev') <- convert vrRev tcEnv prg defDepth conenv'
      let varEnv'   = Map.mapKeys (venv' !) varEnv
          conEnv'   = Map.mapKeys (conenv' !) conEnv
          conIndices' = Map.mapKeys (conenv' !) conIndices
          tyConEnv' = Map.map (over _2 $ map (conenv' !)) tyConEnv

          tcEnv'    :: I.TcEnv
          tcEnv'    = TcEnv varEnv' conEnv' conIndices' tyConEnv'
      tcEnv' `seq` return (CT prg' tcEnv' venv' vrev' conenv' conRev')

data CState = CS { venv  :: Map O.VarId I.VarId 
                 , vrev  :: Map I.VarId O.VarId
                 , var   :: Int 
                 , cenv  :: Map O.ConId I.ConId
                 , vrRev :: Map O.VarId O.VarId
                 , defDepth :: Int 
                 } deriving (Show) 

initState :: Map O.ConId I.ConId -> Map O.VarId O.VarId -> Int -> CState 
initState cenv vrRev defDepth = CS Map.empty Map.empty 0 cenv vrRev defDepth

type Converter = StateT CState (Either Message)

freshVar :: O.VarId -> Converter I.VarId 
freshVar x = do 
  rs@CS{..} <- get 
  let x'   = (var, 0)
      venv' = Map.insert x x' venv
      vrev' = Map.insert x' x vrev
      var' = var + 1 
  put rs{vrev = vrev', var = var', venv = venv'}
  return x'

addVar :: O.VarId -> I.VarId -> Converter ()
addVar x x' = do 
  rs@CS{..} <- get 
  let venv' = Map.insert x x' venv
      vrev' = Map.insert x' x vrev
  put rs{vrev = vrev', venv = venv'}

lookupVar :: O.VarId -> Converter I.VarId
lookupVar x = do 
  CS{..} <- get
  case Map.lookup x venv of 
    Just x' -> return x' 
    Nothing -> throwParseE noLoc "Unknown variable" (x ++ " not found in " ++ show venv)

lookupFun :: O.VarId -> Converter I.VarId
lookupFun f = do 
  CS{..} <- get
  case Map.lookup f venv of 
    Just x -> return x
    Nothing -> throwParseE noLoc "Unknown function" f

lookupCon :: O.ConId -> Converter I.ConId
lookupCon x = do 
  CS{..} <- get
  case Map.lookup x cenv of 
    Just x' -> return x' 
    Nothing -> throwParseE noLoc "Unknown constructor" x

convert :: Map O.VarId O.VarId -> O.OTcEnv -> O.Prg -> Int -> Map O.ConId I.ConId ->
           Either Message (I.Prg, Map O.VarId I.VarId, Map I.VarId O.VarId)
convert vrRev tcEnv decls defDepth cenv = 
    case runStateT (do { CS{..} <- get
                       ; mapM_ freshDecl decls
                       ; decls' <- mapM (convertDecl tcEnv) decls 
                       ; return $ concat decls' }
                  ) (initState cenv vrRev defDepth) of       
      Right (decls', rs) -> Right (decls', venv rs, vrev rs)
      Left err -> Left err

freshDecl :: O.Decl -> Converter ()
freshDecl (O.FunDecl _ fid _ _) = void (freshVar fid)
freshDecl _ = return ()

convertDecl :: O.OTcEnv -> O.Decl -> Converter [I.Decl]
convertDecl tcEnv (O.FunDecl loc fid vars e) = do 
  (fid',0) <- lookupVar fid
  vars' <- mapM (\(v,d) -> do 
                   v' <- freshVar v
                   def <- defDepth <$> get
                   case d of 
                     Just n  -> return (v', n)
                     Nothing -> return (v', def)) vars
  e' <- convertExp freshVar e 
  return [ I.FunDecl loc (fid', 0) vars' e' ]
convertDecl _tcEnv _decl = return []

convertAlt :: (O.VarId -> Converter I.VarId) -> O.Alt -> Converter [I.Alt]
convertAlt l a@(O.Alt loc (Just exp) p e) = do 
  exp' <- convertExp l exp
  p' <- convertPat l p
  e' <- convertExp l e
  return $ [I.Alt loc exp' p' e']
-- Nothings have been made Just 1 from earlier passes

convertPat :: (O.VarId -> Converter I.VarId) -> O.Pat -> Converter I.Pat 
convertPat l (O.PVar x) = I.PVar <$> l x 
convertPat l (O.PLit (O.LitInt x)) = pure  (I.PLit x)
convertPat l O.PWild    = pure $ I.PWild 
convertPat l (O.PApp cid pats) = do 
  (I.ADT cid' _nil) <- convertExp l (O.Con cid)
  pats' <- mapM (convertPat l) pats
  return $ I.PApp cid' pats'

convertOp2 :: O.Op2 -> I.Op2
convertOp2 O.OpPlus  = I.OpPlus
convertOp2 O.OpMinus = I.OpMinus
convertOp2 O.OpTimes = I.OpTimes
convertOp2 O.OpDiv   = I.OpDiv
convertOp2 O.OpMod   = I.OpMod
convertOp2 O.OpEq    = I.OpEq
convertOp2 O.OpNe    = I.OpNe
convertOp2 O.OpLt    = I.OpLt
convertOp2 O.OpGt    = I.OpGt
convertOp2 O.OpLe    = I.OpLe
convertOp2 O.OpGe    = I.OpGe

flatten :: O.Exp -> (O.Exp, [O.Exp])
flatten (O.App (O.Con c) e) = (O.Con c, [e])
flatten (O.App (O.Var x) e) = (O.Var x, [e])
flatten (O.App e1 e2) = second (++[e2]) (flatten e1)
flatten _ = error "Incorrect argument to flatten/Conversions"

notMacro :: I.ConId -> I.ConId -> I.Exp -> I.Exp 
notMacro t f e = 
  I.Case e [ (I.Alt noLoc (I.Lit 1) (I.PApp t []) (I.ADT f []))
           , (I.Alt noLoc (I.Lit 1) (I.PApp f []) (I.ADT t [])) ]

andMacro :: I.ConId -> I.ConId -> I.Exp -> I.Exp -> I.Exp
andMacro t f e1 e2 =
  I.Case e1 [ (I.Alt noLoc (I.Lit 1) (I.PApp t []) e2)
            , (I.Alt noLoc (I.Lit 1) (I.PApp f []) (I.ADT f [])) ]

orMacro :: I.VarId -> I.ConId -> I.ConId -> I.Exp -> I.Exp -> I.Exp -> I.Exp -> I.Exp
orMacro u t f w1 w2 e1 e2 =
  I.Fresh u (I.Lit 1) $
    I.Case (I.Var u) [ 
       (I.Alt noLoc w1 (I.PApp t []) $ 
          I.Case e1 [ (I.Alt noLoc (I.Lit 1) (I.PApp t []) (I.ADT t []))
                    , (I.Alt noLoc (I.Lit 1) (I.PApp f []) e2) ]
       ) ,
       (I.Alt noLoc w2 (I.PApp f []) $ 
          I.Case e2 [ (I.Alt noLoc (I.Lit 1) (I.PApp t []) (I.ADT t []))
                    , (I.Alt noLoc (I.Lit 1) (I.PApp f []) e1) ]
       ) ]

convertExp :: (O.VarId -> Converter I.VarId) -> O.Exp -> Converter I.Exp 
convertExp l (O.Var x) = I.Var <$> lookupVar x
convertExp l (O.Con c) = liftM2 I.ADT (lookupCon c) (pure [])
convertExp l (O.Lit (O.LitInt x)) = pure $ I.Lit x
convertExp l (O.Unop O.OpNot e) = do
  s <- get 
--  fid <- lookupVar $ vrRev s ! "notF"
  e' <- convertExp l e
  t <- lookupCon "True"
  f <- lookupCon "False"
  return $ notMacro t f e'
convertExp l (O.Unop O.OpNeg e) = I.Unop I.OpNeg <$> convertExp l e
-- Conj always does e1 first. 
-- Users can use "and" instead to explicitly control this
convertExp l (O.Conj e1 e2) = do 
  s <- get
--  fid <- lookupVar $ vrRev s ! "and"
  e1' <- convertExp l e1
  e2' <- convertExp l e2
  trueCon <- lookupCon "True"
  falseCon <- lookupCon "False"
  return $ andMacro trueCon falseCon e1' e2' 
         --I.Call fid [I.ADT trueCon [], I.Lit 1, I.Lit 1, e1', e2']
-- Disjunction generates a fresh unknown for choosing a branch 
-- Users can use "or" instead to explicitly control this
convertExp l (O.Disj w1 e1 w2 e2) = do 
  w1' <- case w1 of 
           Just e -> convertExp l e 
           _      -> pure $ I.Lit 1
  e1' <- convertExp l e1 
  w2' <- case w2 of 
           Just e -> convertExp l e 
           _      -> pure $ I.Lit 1
  e2' <- convertExp l e2 
  s <- get
--  fid <- lookupVar $ vrRev s ! "or"
  freshX <- freshVar "uOr"
  t <- lookupCon "True"
  f <- lookupCon "False"
  return $ orMacro freshX t f w1' w2' e1' e2' 
--  return $ I.Fresh freshX (I.Lit 1) (I.Call fid [I.Var freshX, w1', w2', e1', e2'])
convertExp l (O.Binop e1 op e2) =
  liftM3 I.Binop (convertExp l e1) (pure $ convertOp2 op) (convertExp l e2)
convertExp l (O.App e1 e2) = 
  case flatten (O.App e1 e2) of 
    (O.Con c, es) -> do 
      cid' <- lookupCon c
      es'  <- mapM (convertExp l) es
      return $ I.ADT cid' es'
    (O.Var fid, es) -> do 
        fid' <- lookupFun fid
        es'  <- mapM (convertExp l) es
        return $ I.Call fid' es'
    _ -> error "Result of flatten incorrect/Conversions"
convertExp l (O.If e1 e2 e3) = 
  liftM3 I.If (convertExp l e1) (convertExp l e2) (convertExp l e3) 
convertExp l (O.Case e alts) = do 
  e' <- convertExp l e
  alts' <- mapM (convertAlt l) alts
  return $ I.Case e' (concat alts')
convertExp l (O.Let b e) = error "Implement convertExp for Let"
convertExp l (O.Fix e) = I.Fix <$> convertExp l e
convertExp l (O.FixN n e) = I.FixN n <$> convertExp l e
convertExp l (O.Inst e x) = 
  liftM2 I.Inst (convertExp l e) (lookupVar x)
convertExp l (O.Fresh x t en e) = 
  liftM3 I.Fresh (freshVar x) (convertExp l en) (convertExp l e)
convertExp l (O.TRACE x e) = liftM2 I.TRACE (convertExp l (O.Var x)) (convertExp l e)
convertExp l (O.Collect e1 e2) = liftM2 I.Collect (convertExp l e1) (convertExp l e2)

ppADT :: Map I.ConId O.ConId -> I.Exp -> Doc 
ppADT = fmap snd . sizedPpADT (Just 10)

ppADTFull = fmap snd . sizedPpADT Nothing

sizedPpADT :: Maybe Int -> Map I.ConId O.ConId -> I.Exp -> (Maybe Int, Doc)
sizedPpADT size cenv (I.Lit n) = (size, PP.int n)
sizedPpADT size cenv (I.ADT cid []) = (size, PP.text (cenv ! cid))
sizedPpADT (Just 0) _ e
  = (Just 0, PP.text $ "...[" ++ show (sz e) ++ " nodes]")
  where sz (I.ADT _ es) = 1 + sum (sz <$> es)
        sz (I.Lit _) = 1
        sz _ = error "Unhandled case: sz/Conversions"
sizedPpADT size cenv (I.ADT cid es) =
  let (s1, docs) = mapAccumL (\s e -> sizedPpADT s cenv e) (decr size) es
      doc = PP.parens . PP.hang (PP.text (cenv ! cid)) 2 $ PP.sep docs
  in (s1, doc)
sizedPpADT _ _ _ = error "Unhandled case: sizedPpADT/Conversions"

decr = (subtract 1 <$>)

showVals :: Bool
         -> Map I.ConId O.ConId -> Map I.VarId O.VarId -> [(I.VarId, I.Exp)]
         -> Doc
showVals full crev vrev vs = PP.vcat . map ppSample $ vs
  where
    ppVar v = PP.text (vrev ! v) PP.<> PP.text ":"
    ppSample (v, x) = PP.hang (ppVar v) 2 (pp crev x)
    pp = if full then ppADTFull else ppADT

iBuiltIn :: Map O.ConId I.ConId -> BuiltIn I.ConId I.TyConId I.TyVarId
iBuiltIn cenv =
  let BuiltIn{..} = oBuiltIn
  in BuiltIn
    { biInt = biInt
    , biList = biList
    , biListArg = biListArg
    , biListCons = cenv Map.! biListCons
    , biListNil = cenv Map.! biListNil
    , biUnit = cenv Map.! biUnit
    }

