{-# LANGUAGE RecordWildCards, TupleSections, FlexibleContexts #-}
module Outer.Renamer
  ( rename
  , subsExp
  ) where

import Outer.AST
import Common.Error
import Common.SrcLoc

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Arrow

import Data.Map (Map)
import qualified Data.Map as Map

import Debug.Trace
import qualified Common.Types as CT

data RState = RS { env :: Map VarId VarId 
                 , rev :: Map VarId VarId
                 , nat :: Int 
                 } deriving (Show) 

-- | Modifies the behavior of renaming actions.
data RenamerMode = RM
  { _fresh :: VarId -> Renamer_ VarId
  , _lookupVar :: VarId -> Renamer_ VarId
  }

-- | Renaming parameterized by @RenamerMode@.
type Renamer = ReaderT RenamerMode Renamer_
-- | The original Renamer monad.
type Renamer_ = StateT RState (Either Message)

lookupWith f x = do
  lookupF <- f <$> ask
  lift $ lookupF x

fresh :: VarId -> Renamer VarId 
fresh = lookupWith _fresh

lookupVar :: VarId -> Renamer VarId
lookupVar = lookupWith _lookupVar

-- | Modifier for the renaming phase.
uniqueRM :: RenamerMode
uniqueRM = RM
  { _fresh = \x -> do
      rs@RS{..} <- get 
      let x'   = x ++ "@" ++ show nat 
          env' = Map.insert x x' env
          rev' = Map.insert x' x rev
          nat' = nat + 1 
      put rs{rev = rev', nat = nat', env = env'}
      return x'
  , _lookupVar = \x -> do 
      RS{..} <- get
      case Map.lookup x env of 
        Just x' -> return x'
        Nothing -> throwParseE noLoc "(Renamer) Unknown variable: " x
  }

withEnv :: Map VarId VarId -> Renamer a -> Renamer a
withEnv e m = do 
  rs <- get 
  put rs{env = e}
  m

rename :: Prg -> Either Message (Map VarId VarId, Map VarId VarId, Prg)
rename decls = 
    case runStateT (renamerUnique $ mapM_ renameSigs decls >> mapM renameDecl decls) empty of
      Right (decls', rs) -> Right (env rs, rev rs, decls')
      Left err -> Left err
  where
    renamerUnique :: Renamer a -> Renamer_ a
    renamerUnique m = runReaderT m uniqueRM
    empty = RS Map.empty Map.empty 0

-- | Modifier for simple substitutions.
subsRM :: RenamerMode
subsRM = RM
  { _fresh = subs -- Rename bound variables
  , _lookupVar = subs
  } where subs x = Map.findWithDefault x x . env <$> get

runSubs :: Map VarId VarId -> Renamer a -> a
runSubs s m
  = case evalStateT (renamerSubs m) s' of
      Left m -> error $ "Invalid arguments. " ++ show m
      Right e' -> e'
  where
    renamerSubs :: Renamer a -> Renamer_ a
    renamerSubs m = runReaderT m subsRM
    s' = RS s (error "Unused") (error "Unused")

subsExp :: Map VarId VarId -> Exp -> Exp
subsExp s e = runSubs s (renameExp e)

renameSigs :: Decl -> Renamer ()
renameSigs (TypeSig loc fid _ ty) = do 
  _ <- fresh fid
  return ()
renameSigs _ = return ()

renameDecl :: Decl -> Renamer Decl
renameDecl (FunDecl loc fid vars e mt) = do
  rs <- get
  fid' <- case Map.lookup fid (env rs) of
    Nothing -> fresh fid
    Just f -> return f
  vars' <- mapM (\(a,b) -> (,b) <$> fresh a) vars
  e' <- renameExp e
  return $ FunDecl loc fid' vars' e' mt
renameDecl (TypeSig loc fid ctrs ty) = do
  rs <- get
  case Map.lookup fid (env rs) of
    Nothing -> error "Sig not processed twice? (rename)"
    Just fid' -> return $ TypeSig loc fid' ctrs ty
renameDecl d@(ClassDecl loc cid typ bindings) = do
  bindings' <- mapM (\(a,b) -> (,b) <$> fresh a) bindings
  return (ClassDecl loc cid typ bindings')
renameDecl (InstanceDecl loc cid typ ctrs bindings) = do
  bindings' <- mapM (\(fid, vars, e, mt) -> do
                       fid' <- lookupVar fid
                       vars' <- mapM (\(a,b) -> (,b) <$> fresh a) vars
                       e' <- renameExp e
                       return (fid', vars', e', mt)
                    ) bindings
  return (InstanceDecl loc cid typ ctrs bindings')
renameDecl d = pure d

renameAlt :: Alt -> Renamer Alt
renameAlt (Alt loc Nothing p e) = 
    liftM2 (Alt loc Nothing) (renamePat p) (renameExp e)
renameAlt (Alt loc (Just w) p e) = 
    liftM3 (Alt loc) (fmap Just $ renameExp w) (renamePat p) (renameExp e)

renamePat :: Pat -> Renamer Pat 
renamePat (PVar x) = fmap PVar $ fresh x 
renamePat (PLit l) = pure $ PLit l
renamePat PWild    = pure $ PWild 
renamePat (PApp x pats) = fmap (PApp x) $ mapM renamePat pats

renameMaybeExp :: Maybe Exp -> Renamer (Maybe Exp)
renameMaybeExp Nothing = return Nothing
renameMaybeExp (Just e) = do 
  e' <- renameExp e 
  return $ Just e'

renameExp :: Exp -> Renamer Exp 
renameExp (Var (x, _)) = lookupVar x >>= (\x' -> return $ Var (x', Nothing))
renameExp (Con c) = pure $ Con c
renameExp (Lit l) = pure $ Lit l            
renameExp (Unop op e) = fmap (Unop op) $ renameExp e
renameExp (Conj e1 e2) = liftM2 Conj (renameExp e1) (renameExp e2)
renameExp (Disj w1 e1 w2 e2) = liftM4 Disj (renameMaybeExp w1) (renameExp e1) 
                                           (renameMaybeExp w2) (renameExp e2)
renameExp (Binop e1 op e2) = 
    liftM3 Binop (renameExp e1) (pure op) (renameExp e2)
renameExp (App e1 e2) = 
    liftM2 App (renameExp e1) (renameExp e2)
renameExp (If e1 e2 e3) = 
    liftM3 If (renameExp e1) (renameExp e2) (renameExp e3)
renameExp (Case e alts) = do 
  e' <- renameExp e
  RS{env = env} <- get 
  alts' <- mapM (withEnv env . renameAlt) alts
  return $ Case e' alts'
renameExp (Fun vs e) = do
  vs' <- mapM (\(v,d) -> (,d) <$> fresh v) vs
  Fun vs' <$> renameExp e
renameExp (Let b e) = error "Implement renameExp"
renameExp (Fix e) = Fix <$> renameExp e
renameExp (FixN n e) = FixN n <$> renameExp e
renameExp (Inst e x) = liftM2 Inst (renameExp e) (lookupVar x)
renameExp (Fresh x t en e) = liftM4 Fresh (fresh x) (pure t) (renameExp en) (renameExp e)
renameExp (TRACE v e) = liftM2 TRACE (lookupVar v) (renameExp e)
renameExp (Collect e1 e2) = liftM2 Collect (renameExp e1) (renameExp e2)

--renameTcEnv :: Map VarId VarId -> OTcEnv -> OTcEnv
--renameTcEnv venv t = 
--    t{CT.varEnv = Map.mapKeys (venv Map.!) $ CT.varEnv t}
