{-# LANGUAGE TupleSections, RecordWildCards, TemplateHaskell #-}
module Outer.ClassMono where

import Data.Data
import Data.Functor
import Data.List
import Data.Foldable (foldlM)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer hiding (Alt)
import Control.Arrow

import Control.Lens

import Outer.AST
import Common.Pretty (PP(..), (<+>))
import qualified Common.Pretty as PP
import Common.SrcLoc
import Common.Error
import Common.Types
import Outer.Types

import Debug.Trace

monomorphiseClasses :: Prg -> OTcEnv -> Either Message (Prg, OTcEnv)
monomorphiseClasses dcls tc = do 
  (decls, st) <- runStateT (mapM monomorphiseDecl dcls) (REnv Set.empty Map.empty)
  let tc' = Set.foldr (\fid (TcEnv ve ce ci tce) -> TcEnv (Map.delete fid ve) ce ci tce) (aux (concat decls) tc) (constrained st)
  return (snd $ unzip (concat decls), tc')
      where aux [] tc = tc 
            aux ((False, _):rest) tc = tc
            aux ((True, FunDecl _ fid _ _ (Just t)):rest) (TcEnv ve ce ci tce) = 
              -- New binding, add!
              let t' = fmap_tyvarid unPrimeTyVarId t in
              aux rest (TcEnv (Map.insert fid (Forall (fv t') t') ve) ce ci tce)

data REnv = REnv { constrained :: Set VarId 
                 , renv        :: Map VarId (Map OTcType' (Bool, VarId, Exp))
                 } deriving (Eq, Ord, Show)

-- | Assumes ALL variables have different IDs (Rewriting phase needed!)
type Declass a = StateT REnv (Either Message) a

registerClassFun :: VarId -> Declass ()
registerClassFun fid = modify $ \st -> st{renv = Map.insert fid Map.empty (renv st)}

registerInstance :: Bool -> VarId -> [(VarId, Maybe Int)] -> Exp -> OTcType' -> Declass ()
registerInstance b fid vars e ty = 
  modify $ \st -> st {renv = Map.adjust (Map.insert ty (b, fid, Fun vars e)) fid (renv st)}

registerConstrained :: VarId -> Declass ()
registerConstrained fid = 
  modify $ \st -> st {constrained = Set.insert fid (constrained st)}

monomorphiseDecl :: Decl -> Declass [(Bool, Decl)]
monomorphiseDecl (ClassDecl _ _ _ binds) = do
  forM_ binds $ registerClassFun . fst 
  pure []
monomorphiseDecl (InstanceDecl _ _ _ _ binds) = do 
  forM_ binds $ \(fid, vars, e, Just ty) ->
    registerInstance True fid vars e ty
  pure []
monomorphiseDecl (TypeSig _ _ [] _) = pure []
monomorphiseDecl (TypeSig _ fid _ ty) = 
    registerConstrained fid >> pure []
monomorphiseDecl (FunDecl loc fid args e mt) = do 
  let Just t = mt -- This shouldn't fail
  st <- get 
  if Set.member fid (constrained st) then do
--    traceShowM ("Registering Constrained", fid)
    registerClassFun fid
    registerInstance True fid args e t
    pure []
  else do
    (decls, e') <- replaceBindings e
--    traceShowM ("Replace into", decls, fid, e')
    return (decls ++ [(False, FunDecl loc fid args e' mt)])
monomorphiseDecl d = pure [(False, d)]

-- mgu' works with rigids as well. TODO: think about this more
mgu' :: OTcType' -> OTcType' -> String -> Either Message Substitution
mgu' (TcFun l1 r1) (TcFun l2 r2) err = do
  s1 <- mgu' l1 l2 err
  s2 <- mgu' (subst s1 r1) (subst s1 r2) err
  return $ s1 `after` s2
mgu' (TcVar a) t _err = varAsgn a t
mgu' t (TcVar a) _err = varAsgn a t
--mgu' (TcVar (Rigid a)) (TcVar (Rigid b)) _err | a == b = return emptySub
mgu' (TcCon c1 n1 ts1) (TcCon c2 n2 ts2) err
    | c1 == c2 && n1 == n2 =
--        traceShow ("Here", c1, n1, "Folding over", ts1, ts2) $
        foldM (\s (t1,t2) -> do
                 s' <- mgu' (subst s t1) (subst s t2) err
                 return $ s `after` s'
              ) emptySub (zip ts1 ts2)
    | otherwise = throwTypeE noLoc "Mismatched constructors"
        (show (c1,n1) ++ " - " ++ show (c2,n2) ++ " AT " ++ err)
mgu' t1 t2 err =
    throwTypeE noLoc "Types do not unify"
      (show t1 ++ " - " ++ show t2 ++ " AT " ++ err)

replaceBindings ::  Exp -> Declass ([(Bool,Decl)], Exp)
replaceBindings (Var (x, Nothing)) = return ([], Var (x, Nothing))
replaceBindings (Var (x, Just t)) = do 
  st <- get 
  let r = renv st 
--  traceShowM ("Replacing Binding of", x, t)
  case Map.lookup x r of 
    Nothing -> {- trace "No lookup" $ -} return ([], Var (x, Just t))
    Just m -> 
      case Map.lookup t m of 
        Just (b, _, e') -> if b then replaceBindings e' else return ([], Var (x, Just t))
        Nothing -> aux (reverse $ Map.toAscList m)
            where aux [] = error ("TypeClass Resolution Failure: " ++ show x)
                  aux ((t', (False, _,  _)):bs) = aux bs -- Should have been found/monomorphized
                  aux ( (t', (True, fidOrig, Fun vars eb)) : bs ) = do
                    case mgu' t t' "Class things" of 
                      Left _ -> aux bs
                      Right sub -> 
                        if Set.member x (constrained st) then do --Potentially recursive, do fancy stuff
--                          traceShowM ("Found!", t', fidOrig, eb)
                          let fid' = x ++ show t -- Too much?
                              eb' = subRecFun (fidOrig, fid') $ substExp sub eb
                          registerClassFun fid' 
                          registerInstance False fid' vars (error " Should not be accessed... ClassMono" ) t
                          (decls, eb'') <- replaceBindings eb'
                          return ((True, FunDecl noLoc fid' vars eb'' (Just t)) : decls, (Var (fid', Just t)))
                        else -- class definition, just continue after instantiating types in the body
                          replaceBindings (Fun vars $ substExp sub eb)
replaceBindings (Con c) = return . ([],) $ Con c
replaceBindings (Lit l) = return . ([],) $ Lit l
replaceBindings (Unop op e) = (second (Unop op)) <$> (replaceBindings e)
replaceBindings (Conj e1 e2) = do
  (d1, e1') <- replaceBindings e1
  (d2, e2') <- replaceBindings e2
  return (d1 ++ d2, Conj e1' e2')
replaceBindings (Disj me1 e1 me2 e2) = do 
  (d1m, me1') <- replaceBindingsM me1
  (d1, e1') <- replaceBindings e1
  (d2m, me2') <- replaceBindingsM me2
  (d2, e2') <- replaceBindings e2
  return $ (d1m ++ d1 ++ d2m ++ d2, Disj me1' e1' me2' e2')
replaceBindings (Binop e1 op e2) = do
  (d1, e1') <- replaceBindings e1
  (d2, e2') <- replaceBindings e2
  return (d1 ++ d2, Binop e1' op e2')
replaceBindings (App e1 e2) = do
  (d1, e1') <- replaceBindings e1
  (d2, e2') <- replaceBindings e2
  return (d1 ++ d2, App e1' e2')
replaceBindings (If e1 e2 e3) = do 
  (d1, e1') <- replaceBindings e1
  (d2, e2') <- replaceBindings e2
  (d3, e3') <- replaceBindings e3
  return (d1 ++ d2 ++ d3, If e1' e2' e3')
replaceBindings (Case e alts) = do
  (decls, e') <- replaceBindings e
  (decls', alts') <- unzip <$> mapM replaceBindingsAlt alts 
  return (decls ++ concat decls', Case e' alts')
replaceBindings (Fun args e) = 
  second (Fun args) <$> (replaceBindings e)
replaceBindings (Fresh x t s e) = 
  second (Fresh x t s) <$>  (replaceBindings e)
replaceBindings (Inst e x) = second (\e' -> Inst e' x) <$> replaceBindings e
replaceBindings (TRACE x e) = (second (TRACE x)) <$>  (replaceBindings e)
replaceBindings (Collect e1 e2) = do 
  (dcl1, e1') <- replaceBindings e1
  (dcl2, e2') <- replaceBindings e2
  return $ (dcl1 ++ dcl2, Collect e1' e2')

replaceBindingsM :: Maybe Exp -> Declass ([(Bool, Decl)], Maybe Exp)
replaceBindingsM (Nothing) = return ([], Nothing)               
replaceBindingsM (Just e) = second Just <$> replaceBindings e

replaceBindingsAlt (Alt loc me p e) = do 
  (dcl, e') <- replaceBindings e
  return (dcl, Alt loc me p e')

subRecFun :: (VarId, VarId) -> Exp -> Exp
subRecFun (y, y') (Var (x, mt)) | x == y = Var (y', mt)
                                | otherwise = {- traceShow ("subrecfun", x, y, y') $ -} Var (x, mt)
subRecFun s (Con c) = Con c
subRecFun s (Lit l) = Lit l
subRecFun s (Unop op e) = Unop op $ subRecFun s e
subRecFun s (Conj e1 e2) = Conj (subRecFun s e1) (subRecFun s e2)
subRecFun s (Disj me1 e1 me2 e2) = Disj (subRecFun s <$> me1) (subRecFun s e1)
                                       (subRecFun s <$> me2) (subRecFun s e2)
subRecFun s (Binop e1 op e2) = Binop (subRecFun s e1) op (subRecFun s e2)
subRecFun s (App e1 e2) = App (subRecFun s e1) (subRecFun s e2)
subRecFun s (If e1 e2 e3) = If (subRecFun s e1) (subRecFun s e2) (subRecFun s e3)
subRecFun s (Case e alts) = Case (subRecFun s e) (map (subRecFunAlt s) alts)
subRecFun s (Fun vars e) = Fun vars (subRecFun s e) 
subRecFun s (Fresh x t e1 e2) = Fresh x t (subRecFun s e1) (subRecFun s e2)
subRecFun s (Inst e x) = Inst (subRecFun s e) x
subRecFun s (TRACE x e) = TRACE x (subRecFun s e)
subRecFun s (Collect e1 e2) = Collect (subRecFun s e1) (subRecFun s e2)

subRecFunAlt s (Outer.AST.Alt loc weight pat e) = Outer.AST.Alt loc weight pat (subRecFun s e)
