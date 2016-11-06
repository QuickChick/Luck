-- | Fully instantiate unknowns randomly
{-# LANGUAGE FlexibleContexts, TupleSections #-}
module Core.Rigidify
  ( UMap
  , Gen.DataTree(..)
  , Gen.make
  , DataGenMap'
  , simpleMake
  , finalizeTargets
  , partializeTargets
  , ppBindings
  , convert
  ) where

import qualified Common.Pretty as Pretty
import qualified Common.Types as Ty

import Core.AST
import Core.CSet
import Core.IntRep (Rep)
import qualified Core.IntRep as Rep
import Core.Rigidify.Data
import Core.Rigidify.Generator as Gen
import Core.Rigidify.Pretty

import Control.Lens
import Control.Monad.State
import Control.Monad.Random
import Control.Arrow(first, second)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Traversable

import Debug.Trace

type UMap = Map Unknown (DataTree ConId)
type DataGenMap' m
  = Gen.DataGenMap ConId TyConId TyVarId (Sized m)

simpleMake :: (MonadRandom m, Ord c, Ord tc, Ord tv)
  => Ty.TcEnv v c tc tv -> Ty.BuiltIn c tc tv
  -> DataGenMap c tc tv (Sized m)
simpleMake = (fmap . fmap) (^. _1) Gen.make

-- | Finalize a value of a given type.
finalize :: MonadRandom m
  => Unknown -- ^ Adding an unknown denoting where the Ctr came from
  -> TcEnv
  -> DataGenMap ConId TyConId TyVarId (Sized m)
  -> Map TyVarId (Sized m (DataTree ConId)) -- ^ Type variables to generators
  -> Ctr -> TcType 
  -> StateT (UMap, CtrSet) m (DataTree ConId)
finalize u tcEnv gen tvGen = finalize u
  where
    finalize u (Undef size) ty =
      (lift . Gen.runSized size) (Gen.typedGen gen tvGen ty)
    -- TODO: run ac3?
    finalize u (ZC _) _ty = do
      cs <- snd <$> get
--      traceShowM ("Finalizing ZC for", u)
      mc <- lift $ instantiate u cs
--      traceShowM mc
      case mc of
        Just (CtrSet cset') -> do
            modify (second $ const (CtrSet cset'))
            let (ZC (z,_)) = cset' Map.! u 
            return $ DInt $ fromJust $ Rep.toSingleton z
        Nothing -> error "Please report: Shouldn't fail at this stage (finalize/Nothing)"
    finalize u (DC c cArgs) (Ty.TcCon tc _ tArgs) = 
      let (vs, _) = Ty.tyConEnv tcEnv Map.! tc
          sub = Ty.mkSub vs tArgs
          Ty.Forall _ cTy = Ty.conEnv tcEnv Map.! c
          (cArgTys', _) = Ty.unFun cTy
          cArgTys = map (Ty.subst sub) cArgTys'
      in DCon c <$> sequence (zipWith (finalize undefined) cArgs cArgTys)
    finalize _ (U u) ty = do
--      traceShowM ("Finalizing", u)
      (uMap, CtrSet cset) <- get
      case Map.lookup u uMap of
        Just x -> return x
        Nothing -> do
          x <- finalize u (cset Map.! u) ty
          modify (first $ Map.insert u x)
          return x
    finalize _ (DC _ _) (Ty.TcVar _) = error "Found a DC with an abstract type!?"
    finalize _ _ (Ty.TcFun _ _) = error "Found a hole with a function type!?"

-- | List version
finalizeTargets :: MonadRandom m
  => TcEnv
  -> DataGenMap ConId TyConId TyVarId (Sized m)
  -> CtrSet
  -> [(Unknown, TcType)]
  -> m (CtrSet, [DataTree ConId])
finalizeTargets = (fmap . fmap . fmap . fmap . fmap) fst finalizeTargets'

finalizeTargets' tcEnv gen cset us = runStateT (do us' <- traverse f us
                                                   (_, cset') <- get
                                                   return (cset', us')
                                               ) (Map.empty, cset)
  where
    f = uncurry (finalize undefined tcEnv gen Map.empty . U)

partialize cset (Undef _) = DCon (-777) []
partialize cset (ZC (z,_)) = case Rep.toSingleton z of
  Nothing -> DCon (-888) []
  Just x -> DInt x
partialize cset (DC c cArgs) = DCon c (fmap (partialize cset) cArgs)
partialize cset@(CtrSet cset') (U u) = partialize cset (cset' Map.! u)

partializeTargets cset us = (cset, fmap (partialize cset . U) us)

ppBindings size vars vals =
  let nonZero 0 = Nothing
      nonZero n = Just n
  in Pretty.prettyPrint $ sizedPpVals (nonZero size) (zip vars vals)
