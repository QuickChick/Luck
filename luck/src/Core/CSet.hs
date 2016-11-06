{-# LANGUAGE TupleSections #-}
module Core.CSet where

import Control.Monad
import Control.Monad.Random
import Control.Applicative
import Control.Arrow

import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as Map    
import Data.Traversable (sequence)

import Core.Pretty
import Common.Util
import Core.AST
import Core.IntRep(Rep)
import qualified Core.IntRep as Rep

import qualified Outer.AST as O

import Text.PrettyPrint

import Debug.Trace

data Constraint = Gt | Lt | Le | Ge | Ne | Eq
                  deriving (Eq, Ord, Show)
-- 
--data Constr = Constr { _ctr  :: Constraint 
--                     , _self :: Unknown }
--            deriving (Eq, Ord, Show)

mergeCtr :: Constraint -> Constraint -> Maybe Constraint 
mergeCtr x y | x == y = Just x 
mergeCtr Gt Ge = Just Gt
mergeCtr Gt Ne = Just Gt 
mergeCtr Ge Ne = Just Gt 
mergeCtr Lt Le = Just Lt 
mergeCtr Lt Ne = Just Lt 
mergeCtr Le Ne = Just Lt 
mergeCtr Ge Eq = Just Eq
mergeCtr Le Eq = Just Eq
mergeCtr Ge Le = Just Eq
mergeCtr _ _   = Nothing 

type ZSet = (Rep Int, Map Unknown Constraint)

data Ctr = ZC { _z :: ZSet }
         | DC { _conId :: ConId
              , _ctrs  :: [Ctr] }
         | U { _un :: Unknown } 
         | Undef Int -- Int is depth
         deriving (Show)

newtype CtrSet = CtrSet (Map Unknown Ctr) 
    deriving (Show)

-- | Values are:
-- Unknown
-- Lit 
-- ADT cid <value>

toCtr :: Exp -> Ctr 
toCtr (Unknown u) = U u
toCtr (Lit n) = ZC $ (Rep.singleton n, Map.empty)
toCtr (ADT cid vs) = DC cid $ map toCtr vs
toCtr x = error $ "Not a value: " ++ show x

toCtrPat :: Pat -> Ctr
toCtrPat (PVar v) = U v
toCtrPat (PLit n) = ZC $ (Rep.singleton n, Map.empty)
toCtrPat (PApp cid vs) = DC cid $ map toCtrPat vs
toCtrPat PWild = Undef 42 -- TODO: Think about this number

-- | unify k v w 
-- | INV: v and w are values
-- | INV: w is not a function literal
unify :: CtrSet -> Exp -> Pat -> Maybe CtrSet
unify k _ PWild = Just k
unify k (Lit n1) (PLit n2) | n1 == n2  = Just k
                           | otherwise = Nothing
unify k (ADT c1 vs1) (PApp c2 vs2) 
    | c1 == c2 = foldM (\k (v1,v2) -> unify k v1 v2) k (zip vs1 vs2)
    | otherwise = Nothing
unify (CtrSet m) (Unknown u1) (PVar u2) 
    | u1 == u2 = Just $ CtrSet m
    -- INV: u1 -> u2 only if u1 < u2 (avoid circles)
    | u1 < u2 = 
        case (Map.lookup u1 m, Map.lookup u2 m) of 
          (Just r1, Just r2) -> do 
            (r', m') <- unifyRanges (Map.insert u1 (U u2) m) r1 r2 
            return $ CtrSet $ Map.insert u2 r' m'
          (Just r, Nothing) -> 
              return $ CtrSet $ Map.insert u1 (U u2) $ Map.insert u2 r m
          (Nothing, Just r) -> 
              return $ CtrSet $ Map.insert u1 (U u2) $ Map.insert u2 r m
          _ -> error "Both unknowns can't be unbound"                                
    | u1 < u2 = 
        case (Map.lookup u1 m, Map.lookup u2 m) of 
          (Just r1, Just r2) -> do 
            (r', m') <- unifyRanges (Map.insert u2 (U u1) m) r1 r2 
            return $ CtrSet $ Map.insert u1 r' m'
          (Just r, Nothing) -> 
              return $ CtrSet $ Map.insert u2 (U u1) $ Map.insert u2 r m
          (Nothing, Just r) -> 
              return $ CtrSet $ Map.insert u2 (U u1) $ Map.insert u2 r m
          _ -> error "Both unknowns can't be unbound"                                
unify (CtrSet m) (Unknown u) v = 
    case Map.lookup u m of 
      Just r -> do 
        (r', m') <- unifyRanges m r (toCtrPat v)
        return $ CtrSet $ Map.insert u r' m'
      Nothing -> Just $ CtrSet $ Map.insert u (toCtrPat v) m
unify (CtrSet m) v (PVar u) =
    case Map.lookup u m of 
      Just r -> do 
        (r', m') <- unifyRanges m r (toCtr v)
        return $ CtrSet $ Map.insert u r' m'
      Nothing -> Just $ CtrSet $ Map.insert u (toCtr v) m
unify k v1 v2 = error $ "unhandled case in unify/type error?" ++ show (v1, v2)


unifyRanges :: Map Unknown Ctr -> Ctr -> Ctr -> Maybe (Ctr, Map Unknown Ctr)
unifyRanges m (ZC (z1,cs1)) (ZC (z2,cs2)) = do 
  z'  <- Rep.intersect z1 z2
  cs' <- sequence $ Map.unionWith ((join.).(liftM2 mergeCtr)) (Map.map return cs1) (Map.map return cs2)
  return (ZC (z', cs'), m)
unifyRanges m (DC c1 rs1) (DC c2 rs2) 
    | c1 == c2 = do 
       (rsRev', m') <- foldM (\(acc,m) (r1, r2) -> do 
                                (r', m') <- unifyRanges m r1 r2 
                                return (r':acc, m')
                             ) ([],m) (zip rs1 rs2)
       return (DC c1 $ reverse rsRev', m')
    | otherwise = Nothing
unifyRanges m (Undef n1) (Undef n2) = Just $ (Undef $ min n1 n2, m)
-- TODO: Do something with these indexes?
unifyRanges m (Undef n) (ZC z) = Just (ZC z, m)
unifyRanges m (ZC z) (Undef n) = Just (ZC z, m)
unifyRanges m (DC _ _) (Undef 0) = Nothing
unifyRanges m (Undef 0) (DC _ _) = Nothing
unifyRanges m (DC c rs) (Undef n) = 
  first (DC c . reverse) <$> foldM (\(racc, m) r -> first (:racc) <$> unifyRanges m r (Undef $ n-1)) ([], m) rs
unifyRanges m (Undef n) (DC c rs) = do
  (racc, m') <- foldM (\(racc, m) r -> do 
                         (r', m') <- unifyRanges m r (Undef $ n-1)
--                         traceShowM ("After unifying ranges", r, "Undef", n-1, "in", m, r', m')
                         return (r':racc, m')
                      ) ([], m) rs
  return (DC c $ reverse racc, m')
-- first (DC c . reverse) <$> foldM (\(racc, m) r -> first (:racc) <$> unifyRanges m r (Undef $ n-1)) ([], m) rs
unifyRanges m (U u1) (U u2) 
    | u1 == u2 = return (U u1, m)
    | u1 <  u2 = 
      case (Map.lookup u1 m, Map.lookup u2 m) of 
        (Just r1, Just r2) -> do 
           (r', m') <- unifyRanges m r1 r2 
           return $ (U u1, Map.insert u1 (U u2) $ Map.insert u2 r' m')
        (Just r, Nothing) -> 
           return $ (U u1, Map.insert u1 (U u2) $ Map.insert u2 r m)
        (Nothing, Just r) -> 
           return $ (U u1, Map.insert u1 (U u2) $ Map.insert u2 r m)
        _ -> error "unifying two fresh ranges?"
    | u1 >  u2 =
      case (Map.lookup u1 m, Map.lookup u2 m) of 
        (Just r1, Just r2) -> do 
           (r', m') <- unifyRanges m r1 r2 
           return $ (U u2, Map.insert u2 (U u1) $ Map.insert u1 r' m')
        (Just r, Nothing) -> 
           return $ (U u2, Map.insert u2 (U u1) $ Map.insert u1 r m)
        (Nothing, Just r) -> 
           return $ (U u2, Map.insert u2 (U u1) $ Map.insert u1 r m)
        _ -> error "unifying two fresh ranges?"
unifyRanges m (U u) r = 
    case Map.lookup u m of
      Just r' -> do 
        (r'', m') <- unifyRanges m r r' 
        return (U u, Map.insert u r'' m')
      Nothing -> return (U u, Map.insert u r m)
unifyRanges m r (U u) = 
    case Map.lookup u m of
      Just r' -> do 
        (r'', m') <- unifyRanges m r r' 
        return (U u, Map.insert u r'' m')
      Nothing -> return (U u, Map.insert u r m)
-- Everything else is a failed unification
unifyRanges _ _ _ = error "Ill typed?"

refineWith' :: Constraint -> Rep Int -> Rep Int -> Maybe (Rep Int, Rep Int)
refineWith' Gt r1 r2 = Rep.refineGT r1 r2 
refineWith' Ge r1 r2 = Rep.refineGE r1 r2 
refineWith' Lt r1 r2 = Rep.refineLT r1 r2 
refineWith' Le r1 r2 = Rep.refineLE r1 r2 
refineWith' Ne r1 r2 = Rep.refineNE r1 r2 
refineWith' Eq r1 r2 = Rep.refineEQ r1 r2

-- All constraints should be ZC/U 
-- Probably can't have things without bindings - things have already been refined once
ac3 :: [(Unknown, Unknown, Constraint)] -> Map Unknown Ctr -> Maybe (Map Unknown Ctr)
ac3 [] m = Just m 
ac3 ((u1, u2, op):worklist) m = 
--    traceShow ("Calling ac3", u1, u2, op, worklist) $
    case (Map.lookup u1 m, Map.lookup u2 m) of
      (Just (ZC (r1,cs1)), Just (ZC (r2, cs2))) -> do 
--         traceM $ show ("ZCs", r1, op, r2)
         (r1', r2') <- refineWith' op r1 r2 
         let toAdd1 = if r1' == r1 then [] else map (uncurry (u1,,)) $ Map.toList cs1 
             toAdd2 = if r2' == r2 then [] else map (uncurry (u2,,)) $ Map.toList cs2
             -- TODO OPT: remove if r1/r2 singleton
         ac3 (toAdd1 ++ toAdd2 ++ worklist) ( Map.insert u1 (ZC (r1', cs1)) 
                                            $ Map.insert u2 (ZC (r2', cs2)) m)
      (Just (U u1'), Just (ZC _)) -> ac3 ((u1', u2, op):worklist) m
      (Just (ZC _), Just (U u2')) -> ac3 ((u1, u2', op):worklist) m
      (Just (U u1'), Just (U u2')) -> ac3 ((u1', u2', op):worklist) m
      x -> error $ show x

instantiate :: MonadRandom m => Unknown -> CtrSet -> m (Maybe CtrSet)
instantiate u (CtrSet m) = aux u m (m ! u)
    where aux u m (ZC (r,cs)) = do 
--            traceM $ "Instantiating " ++ show u ++ " @ " ++ show r ++ " @ " ++ show cs 
            r' <- Rep.choose' r
            let worklist = map (uncurry (u,,)) $ Map.toList cs
                -- Add the new r' - remove all constraints from u 
                -- TODO: remove all constraints pointing to u? can be done from OPT in ac3
                m' = Map.insert u (ZC (Rep.singleton r', Map.empty)) m
            return $ CtrSet <$> ac3 worklist m'
          -- TODO: Think about this -n (parameterize at toplevel?)
          aux u m (Undef n) = aux u m (ZC (Rep.range (-n) (n), Map.empty))
          aux u m (U u') = aux u' m (m ! u')
          aux _ _ _ = error "Foo/instantiate"

fromSingleton :: CtrSet -> Ctr -> Maybe Exp
fromSingleton k (ZC (r,_)) = Lit <$> Rep.toSingleton r
fromSingleton k (DC cid rs) = ADT cid <$> mapM (fromSingleton k) rs
fromSingleton k (Undef _) = Nothing
fromSingleton k@(CtrSet m) (U u) = Map.lookup u m >>= fromSingleton k

initCtrSet :: [(Unknown, Int)] -> CtrSet 
initCtrSet us = CtrSet $ Map.fromList $ map (second Undef) us

printFor :: CtrSet -> [Unknown] -> Map VarId O.VarId -> Map ConId O.ConId -> String
printFor (CtrSet m) us vRev cRev = 
    concat $ map (\u -> prettyU u vRev ++ " |-> " ++ (render $ ppRange m vRev cRev (m ! u)) ++ "\n") us

prettyPr :: CtrSet -> Map VarId O.VarId -> Map ConId O.ConId -> String
prettyPr (CtrSet m) vRev cRev = 
    Map.foldrWithKey (\u r s -> s ++ "[ " ++ prettyU u vRev ++ " |-> " ++ printRangeShallow m vRev cRev r ++ "\n") "" m

ppRange :: Map Unknown Ctr -> Map VarId O.VarId -> Map ConId O.ConId -> Ctr -> Doc
ppRange m vRev cRev (Undef n) = char '_'
ppRange m vRev cRev (ZC (z,cs))    = text (Rep.printRep z) -- <+> text (show cs)
ppRange m vRev cRev (DC c rs) = text (cRev ! c) $$ (nest 2 (vcat (map (ppRange m vRev cRev) rs)))
ppRange m vRev cRev (U u)     = case Map.lookup u m of 
                                     Just x' -> ppRange m vRev cRev (m ! u)
                                     Nothing -> text "NaN"

printRangeShallow :: Map Unknown Ctr -> Map VarId O.VarId -> Map ConId O.ConId -> Ctr -> String
printRangeShallow m vRev cRev (Undef n) = "_"
printRangeShallow m vRev cRev (ZC (z,_))    = Rep.printRep z 
printRangeShallow m vRev cRev (DC c rs) = "(" ++ cRev ! c ++ " [" ++ concat (intersperse " " (map (printRangeShallow m vRev cRev) rs)) ++ "])"
printRangeShallow m vRev cRev (U u)     = prettyU u vRev 

bind :: CtrSet -> Unknown -> Int -> CtrSet
bind (CtrSet m) u n = CtrSet $ Map.insert u (Undef n) m

getCtr :: Op2 -> Constraint
getCtr OpEq = Eq
getCtr OpNe = Ne
getCtr OpGt = Gt
getCtr OpGe = Ge
getCtr OpLt = Lt
getCtr OpLe = Le

getOpCtr :: Op2 -> Constraint
getOpCtr OpEq = Ne
getOpCtr OpNe = Eq
getOpCtr OpGt = Le
getOpCtr OpGe = Lt
getOpCtr OpLt = Ge
getOpCtr OpLe = Gt

-- x < y -> y > x
getSymCtr :: Constraint -> Constraint
getSymCtr Ne = Ne
getSymCtr Eq = Eq
getSymCtr Gt = Lt
getSymCtr Ge = Le
getSymCtr Le = Ge
getSymCtr Lt = Gt

{-
getRefiner :: Op2 -> (Ctr -> Ctr -> Maybe (Ctr, Ctr))
getRefiner OpEq = refineWith refineEQ
getRefiner OpNe = refineWith refineNE
getRefiner OpLt = refineWith refineLT
getRefiner OpGt = refineWith refineGT
getRefiner OpLe = refineWith refineLE
getRefiner OpGe = refineWith refineGE

getOpRefiner :: Op2 -> (Ctr -> Ctr -> Maybe (Ctr, Ctr))
getOpRefiner OpEq = refineWith refineNE
getOpRefiner OpNe = refineWith refineEQ
getOpRefiner OpLt = refineWith refineGE
getOpRefiner OpGt = refineWith refineLE
getOpRefiner OpLe = refineWith refineGT
getOpRefiner OpGe = refineWith refineLT

type Refiner = Ctr -> Ctr -> Maybe (Ctr, Ctr)

toCtr2 :: (Rep Int, Rep Int) -> (Ctr, Ctr)
toCtr2 = ZC *** ZC

-- | Only applied to possible int ones!
refineEQ,refineNE,refineGT,refineLT,refineLE,refineGE :: Refiner
refineEQ (ZC x) (ZC y) = fmap toCtr2 $ Rep.refineEQ x y
refineNE (ZC x) (ZC y) = fmap toCtr2 $ Rep.refineNE x y
refineLE (ZC x) (ZC y) = fmap toCtr2 $ Rep.refineLE x y
refineGE (ZC x) (ZC y) = fmap toCtr2 $ Rep.refineGE x y
refineLT (ZC x) (ZC y) = fmap toCtr2 $ Rep.refineLT x y
refineLT x y = error $ "Unhandled: " ++ show (x, y)
refineGT (ZC x) (ZC y) = fmap toCtr2 $ Rep.refineGT x y

refineWith :: Refiner -> Ctr -> Ctr -> Maybe (Ctr, Ctr)
--refineWith refiner (Undef n) x = refineWith refiner (ZC (Rep.range (-424242) 424242)) x 
--refineWith refiner x (Undef n) = refiner x (ZC (Rep.range (-424242) 424242))
refineWith refiner (Undef n) x = refineWith refiner (ZC (Rep.range (-n) n)) x
refineWith refiner x (Undef n) = refiner x (ZC (Rep.range (-n) n))
refineWith refiner x y = refiner x y

followToCtr :: Map Unknown Ctr -> Unknown -> Ctr
followToCtr m u = 
  case Map.lookup u m of 
    Just z@(ZC _) -> z
    Just z@(Undef _) -> z
    Just (U u') -> followToCtr m u'
    _ -> error "WTF"

doRefine :: Refiner -> Unknown -> Unknown -> CtrSet -> Maybe CtrSet 
doRefine f u1 u2 (CtrSet m) = do
  (r1', r2') <- f (followToCtr m u1) (followToCtr m u2)
  return $ CtrSet $ Map.insert u1 r1' $ Map.insert u2 r2' m
-}

-- Exps are narrowed: unknowns or literals
-- TODO: Optimization: make the lookups a followToCtr or something similar
-- TODO: Decide what to do with the 424242
registerConstraint :: (Int,Int) -> Constraint -> Exp -> Exp -> CtrSet -> Maybe CtrSet
registerConstraint ir ctr (Unknown u1) (Unknown u2) (CtrSet m) =
--    traceShow ("Registering...", u1, u2) $
    -- only case where we actually register constraints
    case (Map.lookup u1 m, Map.lookup u2 m) of 
      (Just (ZC (r1, cs1)), Just (ZC (r2, cs2))) -> do 
--         traceM $ show ("Refinining", r1, ctr, r2) 
         (r1', r2') <- refineWith' ctr r1 r2 
         let w1 = if r1 == r1' then [] else map (uncurry (u1,,)) (Map.toList cs1) 
             w2 = if r2 == r2' then [] else map (uncurry (u2,,)) (Map.toList cs2) 
         m' <- ac3 (w1 ++ w2) ( Map.insert u1 (ZC (r1', Map.insert u2 ctr cs1)) 
                              $ Map.insert u2 (ZC (r2', Map.insert u1 (getSymCtr ctr) cs2)) m)
         return $ CtrSet m'
      (Just (U u1'), _) -> registerConstraint ir ctr (Unknown u1') (Unknown u2) (CtrSet m)
      (_, Just (U u2')) -> registerConstraint ir ctr (Unknown u1) (Unknown u2') (CtrSet m)
      (Just (Undef _), _) -> 
          registerConstraint ir ctr (Unknown u1) (Unknown u2) 
                                 (CtrSet $ Map.insert u1 (ZC (uncurry Rep.range ir,
                                                              Map.singleton u2 ctr)) m)
      (Nothing, _) -> 
          registerConstraint ir ctr (Unknown u1) (Unknown u2) 
                                 (CtrSet $ Map.insert u1 (ZC (uncurry Rep.range ir,
                                                              Map.singleton u2 ctr)) m)
      (_, Just (Undef n)) ->
          registerConstraint ir ctr (Unknown u1) (Unknown u2) 
                                 (CtrSet $ Map.insert u2 (ZC (uncurry Rep.range ir,
                                                              Map.singleton u1 (getSymCtr ctr))) m)
      (_, Nothing) ->
          registerConstraint ir ctr (Unknown u1) (Unknown u2) 
                                 (CtrSet $ Map.insert u2 (ZC (uncurry Rep.range ir,
                                                              Map.singleton u1 (getSymCtr ctr))) m)
registerConstraint ir ctr (Unknown u) (Lit n) (CtrSet m) =
    -- Stupidest bug EVER
    registerConstraint ir (getSymCtr ctr) (Lit n) (Unknown u) (CtrSet m)
registerConstraint ir ctr (Lit n) (Unknown u) (CtrSet m) = 
--    traceShow ("Registering lit", n, u, ctr) $
    case Map.lookup u m of 
      Just (ZC (r,cs)) -> do 
--        traceM $ show ("Refinining", n, ctr, r)
        (_, r') <- refineWith' ctr (Rep.singleton n) r
--        traceM $ show ("Refine result:", r')
        if r' == r then 
          Just (CtrSet m)
        else 
          let worklist = map (uncurry (u,,)) (Map.toList cs) in
          CtrSet <$> ac3 worklist (Map.insert u (ZC (r',cs)) m)
      Just (U u') -> 
        registerConstraint ir ctr (Lit n) (Unknown u') (CtrSet m)
      Just (Undef _) -> 
          registerConstraint ir ctr (Lit n) (Unknown u) 
                                 (CtrSet $ Map.insert u (ZC (uncurry Rep.range ir,
                                                             Map.empty)) m)
      Nothing ->
          registerConstraint ir ctr (Lit n) (Unknown u) 
                                 (CtrSet $ Map.insert u (ZC (uncurry Rep.range ir, Map.empty)) m)

registerConstraint ir ctr (Lit n1) (Lit n2) m = do 
  _ <- refineWith' ctr (Rep.singleton n1) (Rep.singleton n2)
  Just m

countFor :: CtrSet -> [Unknown] -> Int 
countFor k@(CtrSet m) us = 
    sum $ map (\u -> countNodes (m ! u) k) us

countNodes :: Ctr -> CtrSet -> Int
countNodes (DC _ ts) k = 1 + sum (map (flip countNodes k) ts)
countNodes (ZC _) _ = 1
countNodes (Undef _) _ = 1
countNodes (U u) k@(CtrSet m) = countNodes (m ! u) k

