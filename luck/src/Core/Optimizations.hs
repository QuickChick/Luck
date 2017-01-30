{-# LANGUAGE TemplateHaskell, TupleSections #-}
module Core.Optimizations (inlineAndPropagate) where

import Control.Applicative
import Control.Monad 
import Control.Arrow
import Control.Monad.State 
import Control.Monad.Reader
import Core.AST
import Core.Pretty 

import Text.PrettyPrint

import Common.Util
import Control.Lens
import Data.Maybe

import Data.Map.Strict(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set

--import Common.Pretty (PP(..), text, ($$), prettyPrint, render)
import Debug.Trace

type Inliner = ReaderT R (State S)
type S = Int
data R = R { _fenv :: Map VarId (Int, FItem)
           , _step :: !Int
           , _pred :: VarId -> Inliner Bool
           , _localAdjust :: VarId -> R -> R
           , _vrev :: Map VarId String
           , _crev :: Map ConId String
           , _nesting :: !Int
           }
makeLenses ''R

lookupFun :: VarId -> Inliner (Int, FItem)
lookupFun = views fenv . flip (!)

decreaseCnt :: VarId -> R -> R
decreaseCnt fid r = r{_fenv = Map.adjust (first $ subtract 1) fid (_fenv r)
                     ,_nesting = _nesting r + 1 }
-- fenv `over` Map.adjust (first $ subtract 1) fid 

withAdjustedR :: VarId -> Inliner x -> Inliner x 
withAdjustedR fid = local (\r -> (_localAdjust r) fid r) 

withDecreasedCnt :: VarId -> Inliner x -> Inliner x
withDecreasedCnt fid = local (fenv `over` Map.adjust (first $ subtract 1) fid)

-- | Rename variables to index
rename :: Set Int -> Int -> Exp -> Exp
rename vars idx (Var (x,m)) 
    | Set.member x vars = Var (x, m + idx)
    | otherwise = Var (x,m)
rename vars idx (Unknown u) = Unknown u
rename vars idx (Unop op e)  = Unop op (rename vars idx e)
rename vars idx (Binop e1 op e2) = 
    Binop (rename vars idx e1) op (rename vars idx e2)
rename vars idx (If e1 e2 e3) = 
    If (rename vars idx e1) (rename vars idx e2) (rename vars idx e3)
rename vars idx (ADT cid exps) = 
    ADT cid (map (rename vars idx) exps)
rename vars idx (Call fid exps) = 
    Call fid $ map (rename vars idx) exps
rename vars idx (Case e alts) = 
    Case (rename vars idx e) (map (renameAlt vars idx) alts)
rename vars idx (Fix e) = 
    Fix (rename vars idx e)
rename vars idx (FixN n e) = 
    FixN n (rename vars idx e)
rename vars idx (Fun vs e) =
    let vs' = map (first (second (+idx))) vs in
    Fun vs' (rename (Set.union vars (Set.fromList (map (fst . fst) vs))) idx e)
rename vars idx (Fresh (x,m) en e) = 
    let vars' = Set.insert x vars in
    -- en is renamed with vars (not ') although it doesn't make a difference
    Fresh (x, m + idx) (rename vars idx en) (rename vars' idx e)
rename vars idx (Inst e (x,m)) 
    | Set.member x vars = Inst (rename vars idx e) (x, m + idx)
    | otherwise = Inst (rename vars idx e) (x, m)
rename _ _ (Lit x) = Lit x
rename vars idx (TRACE e e') = TRACE (rename vars idx e) (rename vars idx e')
rename vars idx x = error $ "Core/Interpreter/rename error - unhandled: "  ++ show x

renameAlt :: Set Int -> Int -> Alt -> Alt
renameAlt vars idx (Alt loc w p e) =
    let vars' = Set.union vars $ getVarsP p in
    Alt loc (rename vars idx w) (renamePat vars' idx p) (rename vars' idx e)

renamePat :: Set Int -> Int -> Pat -> Pat
renamePat vars idx (PVar (x,m)) 
    | Set.member x vars = PVar (x, m + idx)
    | otherwise = PVar (x,m)
renamePat vars idx (PApp cid ps) = 
    PApp cid $ map (renamePat vars idx) ps
renamePat vars idx p = p

getVarsP :: Pat -> Set Int 
getVarsP (PVar x) = Set.singleton (fst x)
getVarsP (PApp _ ps) = Set.unions (map getVarsP ps)
getVarsP _ = Set.empty

-- | Argument replacing

replaceArguments :: Int -> [VarId] -> [Exp] -> Exp -> Exp
replaceArguments idx args es = replace find
    where store = Map.fromList $ zip (map (second $ const idx) args) es
          find x = Map.findWithDefault (Var x) x store

unvar :: Exp -> Maybe VarId
unvar (Var x) = Just x 
unvar (Unknown x) = Just x
unvar (Lit n )= Nothing
unvar (ADT _ _)= Nothing
unvar x = error $ show ("Unvaring", x)

replace :: (VarId -> Exp) -> Exp -> Exp
replace f (Var x) = f x
replace f (Unknown u) = Unknown u
replace f (Lit n) = Lit n
replace f (Unop op e) = Unop op (replace f e)
replace f (Binop e1 op e2) = Binop (replace f e1) op (replace f e2)
replace f (If e1 e2 e3) = If (replace f e1) (replace f e2) (replace f e3)
replace f (ADT c es) = ADT c (map (replace f) es)
replace f (Case e alts) = Case (replace f e) (map (replaceAlt f) alts)
replace f (Fix e) = Fix (replace f e)
replace f (FixN n e) = FixN n (replace f e)
replace f (Fresh x en e) = Fresh x (replace f en) (replace f e)
replace f (Inst e x) = 
  case f x of 
    Var x' -> Inst (replace f e) x'
    Unknown u -> Inst (replace f e) u
    _ -> traceShow ("Ignoring", e) e -- TODO: This might cause some bugs?
replace f (TRACE v e) = TRACE (replace f v) (replace f e)
replace f (Call fid es) = Call fid $ map (replace f) es

replaceAlt :: (VarId -> Exp) -> Alt -> Alt
replaceAlt f (Alt loc w p e) = Alt loc (replace f w) p (replace f e)

inlineExp :: Exp -> Inliner Exp
inlineExp (Var x) = pure $ Var x 
inlineExp (Unknown x) = pure $ Unknown x
inlineExp (Lit n) = pure $ Lit n
inlineExp (Unop op e) = fmap (Unop op) (inlineExp e)
inlineExp (Binop e1 op e2) = liftM3 Binop (inlineExp e1) (pure op) (inlineExp e2)
inlineExp (If e1 e2 e3) = liftM3 If (inlineExp e1) (inlineExp e2) (inlineExp e3)
inlineExp (ADT c es) = liftM (ADT c) (mapM inlineExp es)
inlineExp (Case e alts) = liftM2 Case (inlineExp e) (mapM inlineAlt alts)
inlineExp (Fun vs e) = Fun vs <$> inlineExp e
inlineExp (Fix e) = liftM (Fix) (inlineExp e)
inlineExp (FixN n e) = liftM (FixN n) (inlineExp e)
inlineExp (Inst e u) = liftM2 Inst (inlineExp e) (pure u)
inlineExp (Fresh x en e) = liftM2 (Fresh x) (inlineExp en) (inlineExp e)
inlineExp (TRACE v e) = liftM2 TRACE (inlineExp v) (inlineExp e)
inlineExp (Call (Var fid) es) = do
  rs <- ask
  b <- (_pred rs) fid
  if b then do
--    traceM $ render $ nest (_nesting rs) $ text $ "Inlining function " ++ show (_vrev rs ! fid)
    (cnt, FItem args body) <- lookupFun fid 
    idx <- get
    -- Ignore the depths
    let args' = map fst args
    -- First rename the body
    let renamed  = rename (Set.fromList $ map fst args') idx body
    -- Then replace the arguments (they are now at @idx@)
    let replaced = replaceArguments idx args' es renamed
    put $ idx + (_step rs)
--    traceM $ render $ nest (_nesting rs + 1 ) $ text $ "CP, this is at " ++ show (idx + (_step rs))
    -- Finally try doing inlining in the renamed+replaced body
    body' <- withAdjustedR fid $ inlineExp replaced
--    traceM $ "Returning body: " ++ printExp (_vrev rs) (_crev rs) body'
    return body'
  else Call (Var fid) <$> mapM inlineExp es -- TODO: this might not be sane :)
inlineExp (Call f es) = return (Call f es) -- TODO: optimize
inlineExp e = error $ show e

inlineAlt :: Alt -> Inliner Alt 
inlineAlt (Alt loc w p e) = liftM3 (Alt loc) (inlineExp w) (pure p) (inlineExp e)

origInlinerState :: Map VarId String -> Map ConId String -> Int -> Int -> FMap -> R 
origInlinerState vrev crev step rolls fmap = 
    R { _fenv = Map.map (rolls,) fmap 
      , _step = step
      , _pred = \fid -> do
          (cnt, _) <- lookupFun fid
          return (cnt > 0)
      , _localAdjust = decreaseCnt 
      , _vrev = vrev
      , _crev = crev 
      , _nesting = 0
      }


-- | Simple computations
data CS = CS { cTrue  :: ConId
             , cFalse :: ConId 
             }
          deriving (Eq, Show)
type Computer = State CS

isConFalse,isConTrue :: Exp -> Computer Bool
isConFalse (ADT c _) = do 
  s <- get 
  return $ c == cFalse s 
isConFalse _ = return False
isConTrue (ADT c _) = do 
  s <- get 
  return $ c == cTrue s
isConTrue _ = return False

fromBool :: Bool -> Computer Exp
fromBool True  = fmap ((ADT ?? []) . cTrue ) get
fromBool False = fmap ((ADT ?? []) . cFalse) get 

compute :: Exp -> Computer Exp
compute (Var x) = pure $ Var x
compute (Unknown u) = pure $ Unknown u
compute (Lit n) = pure $ Lit n
compute (Unop OpNeg e) = do
  e' <- compute e
  case e' of 
    Lit n -> return $ Lit (-n)
    _ -> return $ Unop OpNeg e'
compute (Binop e1 op e2) = do
  e1' <- compute e1 
  e2' <- compute e2
  case (e1', e2') of 
    (Lit n1, Lit n2) -> 
      case op of 
        OpPlus  -> return $ Lit $ n1 + n2 
        OpMinus -> return $ Lit $ n1 - n2 
        OpTimes -> return $ Lit $ n1 * n2 
        OpDiv   -> return $ Lit $ n1 `div` n2 
        OpMod   -> return $ Lit $ n1 `mod` n2 
        OpEq    -> fromBool (n1 == n2)
        OpNe    -> fromBool (n1 /= n2)
        OpLt    -> fromBool (n1 <  n2)
        OpLe    -> fromBool (n1 <= n2)
        OpGt    -> fromBool (n1 >  n2)
        OpGe    -> fromBool (n1 >= n2)
    _ -> return $ Binop e1' op e2'
-- I think I eliminated if's from the core..
compute (If e1 e2 e3) = do
  e1' <- compute e1 
  e2' <- compute e2
  e3' <- compute e3
  b1 <- isConTrue  e1'
  b2 <- isConFalse e1'
  if b1 then return e2'
  else if b2 then return e3' 
  else return $ If e1' e2' e3'
compute (ADT c es) = liftM (ADT c) $ mapM compute es
compute (Call f es) = liftM (Call f) $ mapM compute es
compute (Fun vs e) = return $ Fun vs e
compute (Case e alts) = do
--    traceM $ "Computing in case" ++ show e
    let def = Case <$> compute e <*> mapM computeAlt alts 
    e' <- compute e
    case e' of 
      ADT cid es -> 
          case getAltADT cid alts of 
            Just (Alt loc w (PApp cid' ps) e') -> 
                case mkReplaceFun es ps of 
                  Just zipped -> 
                    let (vs, es') = unzip zipped in
                    case vs of 
                      [] -> compute e'
                      ((_,idx):_) -> compute $ replaceArguments idx vs es' e'
                  _ -> def -- What is this?
            Just _ -> def -- In this case the match is unnecessary?
            _ -> fromBool False -- No ADT in options, will fail anyway! 
      _ -> def
compute (Fix e) = liftM Fix $ compute e
compute (FixN n e) = FixN n <$> compute e
compute (Fresh x en e) = liftM2 (Fresh x) (compute en) (compute e)
compute (Inst e u) = liftM2 Inst (compute e) (pure u)
compute (TRACE v e) = TRACE <$> compute v <*> compute e

computeAlt :: Alt -> Computer Alt
computeAlt (Alt loc w p e) = 
    Alt loc <$> compute w <*> pure p <*> compute e

getAltADT :: ConId -> [Alt] -> Maybe Alt 
getAltADT cid [] = Nothing
getAltADT cid (a@(Alt loc w p e):as) = 
    case p of 
      PApp cid' _ -> if cid == cid' then Just a else getAltADT cid as
      _ -> Just a

mkReplaceFun :: [Exp] -> [Pat] -> Maybe [(VarId, Exp)]
mkReplaceFun es ps =
    let aux [] [] bindings = Just bindings
        aux (e:es) (PVar x : ps) bindings = aux es ps ((x,e):bindings)
        aux (_:es) (PWild : ps)  bindings = aux es ps bindings
        aux _ _ _ = Nothing
    in aux es ps []


--- Remove Unnecessary Patterns
removeExtra :: Exp -> Pat -> Exp
removeExtra (Var x) _     = Var x 
removeExtra (Unknown u) _ = Unknown u
removeExtra (Lit n) _     = Lit n
removeExtra (Unop op e) p = Unop op (removeExtra e p)
removeExtra (Binop e1 op e2) p = Binop (removeExtra e1 p) op (removeExtra e2 p)
removeExtra (If e1 e2 e3) p = If e1 (removeExtra e2 p) (removeExtra e3 p)
removeExtra e@(ADT _ _) _ = e --TODO: Maybe allow fail?
removeExtra (Case e alts) pat@(PApp cid ps) = 
  let alts0 = map (\(Alt l w p e) -> Alt l w p $ removeExtra e pat) alts
      alts' = filter (\(Alt _ _ _ e) -> 
                          case e of 
                            ADT cid' _ -> cid == cid'
                            _ -> True
                     ) alts0 in
  case alts' of 
    [Alt _ _ p _] -> Case (removeExtra e p) alts'
    _ -> Case e alts'
removeExtra (Case e alts) _ = Case e alts
removeExtra (Call fid es) _ = Call fid es
removeExtra (Fix e) p = Fix (removeExtra e p)
removeExtra (FixN n e) p = FixN n (removeExtra e p)
removeExtra (Inst e u) p = Inst (removeExtra e p) u
removeExtra (Fresh x en e) p = Fresh x (removeExtra en p) (removeExtra e p)

-- | Returns true if it contains *any* calls that satisfy p
functionFilter :: (VarId -> Bool) -> Exp -> Bool
functionFilter p (Var x) = False
functionFilter p (Unknown x) = False
functionFilter p (Lit n) = False
functionFilter p (Unop op e) = functionFilter p e
functionFilter p (Binop e1 op e2) = 
    functionFilter p e1 || functionFilter p e2
functionFilter p (If e1 e2 e3) = 
    functionFilter p e1 || functionFilter p e2 || functionFilter p e3
functionFilter p (ADT c es) = any (functionFilter p) es
functionFilter p (Case e alts) = 
    functionFilter p e || any (functionFilterAlt p) alts
functionFilter p (Fix e) = functionFilter p e
functionFilter p (FixN n e) = functionFilter p e
functionFilter p (Inst e u) = functionFilter p e
functionFilter p (Fresh x en e) = 
    functionFilter p en || functionFilter p e
functionFilter p (TRACE v e) = functionFilter p v || functionFilter p e
functionFilter p (Fun vars e) = p (-1,-1) 
functionFilter p (Call (Fun vars e) es) 
    | p (-1, -1) = True
    | otherwise = any (functionFilter p) (e : es)
functionFilter p (Call (Var fid) es) 
    | p fid = True
    | otherwise = any (functionFilter p) es

functionFilterAlt p (Alt _ ew _ e) = 
    functionFilter p ew || functionFilter p e

isRecursive :: VarId -> Exp -> Bool
isRecursive fid e = functionFilter (== fid) e

hasAnyCalls :: Exp -> Bool
hasAnyCalls e = functionFilter (const True) e

isLeafFunction :: Exp -> Bool
isLeafFunction e = not $ hasAnyCalls e

getLeafFunctions :: FMap -> Set VarId
getLeafFunctions fenv = 
    Set.fromList $ map fst $ filter (\(fid,FItem args e) -> isLeafFunction e) $ Map.assocs fenv

inlineLeaves :: Map VarId String -> Map ConId String -> Int -> FMap -> Exp 
             -> ConId -> ConId -> (Int, FMap, Exp)
inlineLeaves vrev crev step fenv e cTrue cFalse = 
    let leaves = getLeafFunctions fenv
        rs = R { _fenv = Map.map (undefined,) fenv
               , _step = step
               , _pred = \fid -> return (Set.member fid leaves)
               , _localAdjust = \fid r -> r
               , _vrev = vrev
               , _crev = crev
               , _nesting = 0
               }
        (fs, idxs) = unzip $ map (\(fid, FItem args e) -> 
                                    let (e', idx) = runState ?? 1 $ runReaderT ?? rs $ inlineExp e
                                        eComp = evalState (compute e') (CS cTrue cFalse)
                                    in ((fid, FItem args eComp), idx)
                                ) $ Map.assocs fenv
        (e',idx') = runState ?? 1 $ runReaderT ?? rs $ inlineExp e
    in (maximum (idx':idxs), Map.fromList fs, e')

inlineAndPropagate :: Map VarId String -> Map ConId String -> 
                      ConId -> ConId -> Int -> FMap -> Exp -> (Exp, Int, Int, FMap)
inlineAndPropagate vrev crev cTrue cFalse rolls fenv e = 
   -- TODO fix inlineLeaves :)
   let (step, fenv', e0) = inlineLeaves vrev crev 1 fenv e cTrue cFalse 
       (e', idx) = {- traceShow ("Step", step) $ -} runState (runReaderT (inlineExp e0) 
                                            (origInlinerState vrev crev step rolls fenv')) (step + 1)
       (eCompute, s) = runState (compute e') (CS cTrue cFalse)
       eFinal = {- traceShow ("Removing extra", s) $ -} removeExtra eCompute (PApp cTrue [])
   in (eFinal, idx, step, fenv')

{-
    let fenv' = Map.map (\(FItem as e) -> 
                    FItem as (evalState (compute e) (CS cTrue cFalse))) fenv

        (e', idx) = runState (runReaderT (inlineExp e) 
                                             (R $ Map.map (rolls,) fenv')) 1
        eFinal = evalState (compute e') (CS cTrue cFalse)
    in (eFinal, idx, fenv')
-}

{-
-------------- FMap handling -----------

refineFMap :: (VarId,FItem) -> Map VarId FItem -> Map VarId FItem
refineFMap (fid,fitem@(FItem _ body)) funs = aux (Map.singleton fid fitem) funs body
  where aux :: Map VarId FItem -> Map VarId FItem -> Exp -> Map VarId FItem
        aux acc funs (Var x) = acc
        aux acc funs (Unknown _) = acc
        aux acc funs (Lit _) = acc
        aux acc funs (Unop _ e) = aux acc funs e
        aux acc funs (Conj e1 e2) = aux (aux acc funs e1) funs e2
        aux acc funs (Disj _ e1 _ e2) = aux (aux acc funs e1) funs e2
        aux acc funs (Binop e1 _ e2)  = aux (aux acc funs e1) funs e2
        aux acc funs (If e1 e2 e3) = aux (aux (aux acc funs e1) funs e2) funs e3
        aux acc funs (ADT _ es) = foldr (\e acc' -> aux acc' funs e) acc es
        aux acc funs (Call f es) = 
            let (fItem@(FItem _ body)) = funs ! f
                acc' = if Map.member f acc then acc 
                       else aux (Map.insert f fItem acc) funs body
            in foldr (\e' acc' -> aux acc' funs e') acc' es
        aux acc funs (Case e alts) = 
            foldr (\(Alt _ _ _ e') acc' -> aux acc' funs e') 
                      (aux acc funs e) alts 
        aux acc funs (Let _ _) = undefined
        aux acc funs (Fix u e) = aux acc funs e
        aux acc funs (FixN _ e) = aux acc funs e
        aux acc funs (Partition _ e) = aux acc funs e
        aux acc funs (TRACE e e') = aux (aux acc funs e) funs e'


             
-}
