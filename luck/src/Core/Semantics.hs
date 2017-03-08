{-# LANGUAGE TupleSections, MultiWayIf, 
  FlexibleInstances, MultiParamTypeClasses, UndecidableInstances
  , TemplateHaskell #-}
module Core.Semantics where

import Common.Types hiding (TcType, TcEnv, subst)
import Common.Error
import Common.Util

import Core.AST
import qualified Core.IntRep as Rep
import Core.CSet
import Core.Pretty

import Control.Monad
import Control.Applicative
import Control.Arrow

import Control.Monad.Except
import Control.Monad.Signatures
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Random
import System.Random (StdGen)

import Data.Bifunctor(bimap)
import Data.List(intersperse)
import Data.Map(Map)
import qualified Data.Map as Map
import Data.Set(Set)
import qualified Data.Set as Set

import Control.Lens

import Debug.Trace

data ReaderState = RS { _fMap :: FMap 
                        -- ^ Function Environment
                      , _tcEnv :: TcEnv
                        -- ^ Type Environment
                      , _revVMap :: Map VarId String
                       -- ^ Maps variables and unknowns back to strings. For pretty printing
                      , _revCMap :: Map ConId String
                       -- ^ Maps constructors back to strings. For pretty printing
                      , _conTrue  :: ConId
                      , _conFalse :: ConId
                       -- ^ True and False constructor representations
                      , _integerRange :: (Int, Int)
                       -- ^ Default integer range
                     } deriving (Show)
makeLenses ''ReaderState

data FBState = FBS { _idx :: !Int 
                     -- ^ Index for freshness
                   , _step :: !Int
                     -- ^ Step for increasing freshness 
                   , _backRem :: !Int 
                     -- ^ Backtracking remainder 
                   , _freshIdx :: !Int
                     -- ^ Index for *COMPLETELY* fresh, hidden unknowns
                   } deriving (Show)
makeLenses ''FBState

type Luck = ReaderT ReaderState (StateT FBState (RandT StdGen (Either Message)))

mkReaderState :: FMap -> TcEnv -> Map VarId String -> Map ConId String -> ConId -> ConId -> (Int, Int) -> 
                 ReaderState
mkReaderState = RS

mkFBState :: Int -> Int -> Int -> FBState
mkFBState x y z = FBS x y z (-1)

runLuck :: ReaderState -> FBState -> Exp -> Pat -> CtrSet -> StdGen -> Either String (Exp, CtrSet)
runLuck = ((.) . (.) . (.) . (.) . (.) . (.)) (bimap show (\((x, _), _) -> x)) runLuck'

runLuck' :: ReaderState -> FBState -> Exp -> Pat -> CtrSet -> StdGen ->
  Either Message (((Exp, CtrSet), FBState), StdGen)
runLuck' rs fbs e w k g
  = runRandT ?? g $ runStateT ?? fbs $ runReaderT ?? rs $ do 
--      traceShowM ("Step is: ", _step fbs)
--      debug (\v c -> printExp v c e) 
      (e',k') <- semantics e w k
--      debug (\v c -> printExp v c e')
--      debug (\v c -> prettyPr k' v c)
      return (e', k')

-- Stupidity of the standard library
liftCatch' :: Monad m => Catch e m (a,s) -> Catch e (RandT s m) a
liftCatch' catchE m h =
    liftRandT $ \ s -> runRandT m s `catchE` \ e -> runRandT (h e) s

unsat :: String -> Luck a
unsat msg = do 
  s <- get 
  let bt = _backRem s
  if bt > 0
  then do 
    backRem -= 1
    throwError $ mkUnSat msg
  else throwError $ mkBacktrackMax


fresh :: Luck Unknown
fresh = do 
  s <- get
  freshIdx -= 1
  return (_freshIdx s, _idx s)

freshen :: Unknown -> Luck Unknown
freshen (u,_) = do 
  s <- get 
  return $ (u, _idx s)

increaseIdx :: Luck ()
increaseIdx =  
  modify (\s -> s{_idx = _idx s + _step s})

currentIndex :: Int -> Int -> Int -> Bool
currentIndex idx step n = (n >= idx && n < idx + step)

backtrack :: (Map VarId String -> Map ConId String -> String) -> [Luck a] -> Luck a
backtrack s [] = do 
  unsat $ "Exhausted choices"
backtrack s (m:ms) = 
    m `catchError` (\err -> if isUnSat err then do 
--                              debug s
                              backtrack s ms
                            else throwError err)

luckUnify :: CtrSet -> Exp -> Pat -> Luck (Exp, CtrSet)
luckUnify k e w = 
    case unify k e w of 
      Just x -> return (e, x)
      Nothing -> do 
        rs <- ask 
        let (v, c) = (_revVMap rs, _revCMap rs)
        unsat $ "Unification failed: " ++ printExp v c e ++ " vs " ++ printPat v c w

luckNote :: String -> Maybe a -> Luck a
luckNote s Nothing  = unsat s
luckNote _ (Just x) = return x

debug :: (Map VarId String -> Map ConId String -> String) -> Luck ()
debug f = do 
  rs <- ask 
  let (v, c) = (_revVMap rs, _revCMap rs)
  traceM $ f v c

-- | Semantics: e . w . k -> Luck (v, k')
-- When Doing any sort of arithmetic (negative, binop), numbers should be fixed 
semantics :: Exp -> Pat -> CtrSet -> Luck (Exp, CtrSet)
semantics (Var x) PWild k   = return (Var x, k) -- should only happend for function ids
semantics e@(Unknown u) w k  = do 
--  debug $ \v c -> "Unifying:\n" ++ printExp v c e ++ "\n" ++ printPat v c w
--  debug $ \v c -> printFor k [u] v c
  (e',k') <- luckUnify k e w
--  debug $ \v c -> prettyPr k' v c
  return (e',k')
semantics e@(Lit n) w k      = luckUnify k e w
semantics e@(Unop OpNeg e') w k = do
  (v,k') <- semantics e' PWild k
  case v of 
    Lit n -> luckUnify k (Lit $ -n) w
    Unknown u -> 
      -- This can be made to make a choice
      case fromSingleton k' (U u) of 
        Just (Lit n) -> luckUnify k (Lit $ -n) w
        Nothing -> error "Number not instantiated in -"
    _ -> error $ "Value of wrong type? : " ++ show v
-- TODO: Narrowing semantics should be (implemented and) used here for e1,e2
semantics e@(Binop e1 op2 e2) w@(PApp cid []) k 
  | boolBinop op2 = do 
     rs <- ask 
     let (t, f) = (_conTrue rs, _conFalse rs)
--     debug $ \v c -> printExp v c e1 
--     debug $ \v c -> printExp v c e2
     (v1, k1) <- narrow e1 k 
     (v2, k2) <- narrow e2 k1
     if cid == t then do
--       debug $ \v c -> prettyPr k v c 
--       debug $ \v c -> printExp v c v1
--       debug $ \v c -> printExp v c v2
--       debug (\v c -> "Refining for: " ++ printFor k2 [v1, v2] v c)
       
       -- TODO: Think about w there
       k' <- luckNote "refiner" $ registerConstraint (_integerRange rs) (getCtr op2) v1 v2 k2 
                                  --doRefine (refineWith (getRefiner op2)) w1 w2 k2
       return (ADT cid [], k')
     else do
       -- Opposite refiner
       k' <- luckNote "refiner" $ registerConstraint (_integerRange rs) (getOpCtr op2) v1 v2 k2
                                  -- doRefine (refineWith (getOpRefiner op2)) w1 w2 k2
       return (ADT cid [], k')
semantics e@(Binop e1 op2 e2) w k = do
     (v1,k1) <- narrow e1 k
     (v2,k2) <- narrow e2 k1
--     debug (\v c -> printExp v c v1 ++ " - " ++ printExp v c v2)     
     rs <- ask
     let n1 = extractInt (_revVMap rs) v1 k2
         n2 = extractInt (_revVMap rs) v2 k2 
     luckUnify k2 (Lit $ (getOp op2) n1 n2) w
semantics e@(If e1 e2 e3) w k = do 
  rs <- ask
  opts <- randomize $ zip[1,1] $ [ do { (e1', k') <- semantics e1 (PApp (_conTrue rs ) []) k
                                      ; semantics e2 w k' }
                                 , do { (e1', k') <- semantics e1 (PApp (_conFalse rs) []) k
                                      ; semantics e3 w k' }
                                 ]
  backtrack (\ v c  -> "if: " ++ printExp v c e) opts
semantics e@(ADT cid es) (PApp cid' ws) k 
   | cid == cid' = do -- constructors match, recurse
         first (ADT cid . reverse) <$> 
           foldM (\(res,k) (e,w) -> first (:res) <$> semantics e w k) ([],k) (zip es ws)
   | otherwise = do 
      rs <- ask
      unsat $ "Attempted to unify constructors: " ++ show (_revCMap rs ! cid, _revCMap rs ! cid')
semantics e@(ADT cid es) (PVar w) k = do
  ws <- mapM (\_ -> PVar <$> fresh) es
  (_, k') <- luckUnify k (Unknown w) (PApp cid ws)
  (es', k'') <- foldM (\(res,k) (e,w) -> first (:res) <$> semantics e w k) ([], k') (zip es ws)
  return (ADT cid $ reverse es', k'')
semantics e@(ADT _ _) PWild k = return (e, k)
semantics (Call (Var fid) es) w k = do 
  rs <- ask
--  debug $ \v c -> "Is this called? " ++ show fid
--  debug $ \v c -> "Calling function" ++ v ! (fst fid,0) ++ " : " ++ concat (intersperse "\n" $ map (\e -> printExp v c e) es)
--  debug $ \v c -> prettyPr k v c 
  let (FItem args e) = _fMap rs ! (fst fid, 0)
  semantics (Call (Fun args e) es) w k
semantics (Call (Fun args e) es) w k = 
  if length args == length es then do
--    debug $ \v c -> "Calling anonymous " ++ (printExp v c e)
--                    ++ " : " ++ concat (intersperse "\n" $ map (printExp v c) es)
    (es',k') <- first reverse <$> foldM (\(acc,k) e -> do 
--                                          debug $ \v c -> "Semantics for " ++ printExp v c e
                                          (v, k') <- semantics e PWild k
                                          return (v:acc, k')
                                        ) ([],k) es
    increaseIdx
    -- First rename ALL the variables in the body
    s <- get
    let eRenamed = rename Set.empty (_idx s) e
    -- Then replace the arguments in the body with the expressions
  --  let es' = map (forceBinops k) es
    let e' = subst eRenamed (map (\((x,_),_) -> (x,_idx s)) args) es'
--    debug $ \v c -> "Body of function is:\n " ++ printExp v c e' 
    -- Finally call the semantics of the new body
    semantics e' w k'
  else error "Implement partial application"
-- TODO: Optimize. semantics (Case (Unknown u) alts) w k =
semantics e@(Fun _ _) PWild k = return (e, k)
semantics e@(Case d alts) w k = do
--  debug $ \v c -> "In Case\n" ++ printExp v c d ++ "\n" ++ (concat $ intersperse "\n" $ map (printAlt v c) alts)
  rs <- ask
  weights <- mapM (\(Alt _ ew _ _) -> do 
                      (e, _) <- semantics ew PWild k
                      return $ extractInt (_revVMap rs) e k
                  ) alts
  opts <- randomize $ zip weights
                    $ map (\(Alt _ _ pat e') -> do
                            let us = getUnknownsP pat
--                            debug $ \v c -> "Handling branch: \n" ++ printExp v c d ++ "\n" ++  printPat v c pat
                            (_, k') <- semantics d pat k  
--                            debug $ \v c -> "After semantics: \n" ++ printFor k' us v c
                            let e'' = subst e' us (map Unknown us)
                            semantics e'' w k'
                          ) alts
  backtrack (\v c -> "Backtracking... (CASE)" ++ printAltPats v c alts ) $ opts
semantics (Fix e) w k = error "implement fix"
semantics (FixN n e) w k 
    | n == 0 = return (e, k)
    | otherwise = do 
--       debug $ \v c -> "In Fix With:\n" ++ prettyPr k v c
       (_, k') <- semantics e w k 
--       debug $ \v c -> "After Semantics of Fix:\n" ++ prettyPr k' v c
       semantics (FixN (n-1) e) w k'
semantics (Inst e u) w k = do 
  (e', k') <- semantics e w k 
--  debug $ \v c -> "Instantiating:  \n" ++ printFor k' [u] v c
  -- Maybe Just is to harsh.. add backtracking?
  Just k' <- instantiate u k'
  return (e', k')
semantics (Fresh x n e) w k = do 
  s <- get 
  let e' = subst e [x] [Unknown x]
  (Lit n', k') <- semantics n PWild k
  let k'' = bind k' x n' -- why bind?
  semantics e' w k''
-- TRACE
-- Collect
semantics e w k = error $ "Unhandled" ++ show (e,w,k)

-- | Narrow: e . k -> Luck (v, k')
narrow :: Exp -> CtrSet -> Luck (Exp, CtrSet)
narrow (Var x) k  = return (Var x, k) -- should only happend for function ids
narrow e@(Unknown u) k = return (e, k)
narrow e@(Lit n) k = return (e,k)
narrow e@(Unop OpNeg e') k = do
  (v,k') <- narrow e' k
  case v of 
    Lit n -> return (Lit $ -n, k)
    _ -> error "impossible:narrow/opneg"
narrow (Binop e1 op2 e2) k = do
  (l1, k1) <- narrow e1 k 
  (l2, k2) <- narrow e2 k1
  case (l1,l2) of 
    (Lit n1, Lit n2) -> return (Lit $ (getOp op2) n1 n2, k2)
    (Unknown u1, Lit n2) -> do
       Just k' <- instantiate u1 k2 
       (Lit n1) <- luckNote "singleton after instantiation" $ fromSingleton k' (U u1)
       return (Lit $ (getOp op2) n1 n2, k')
    (Lit n1, Unknown u2) -> do
       Just k' <- instantiate u2 k2 
       (Lit n2) <- luckNote "singleton after instantiation" $ fromSingleton k' (U u2)
       return (Lit $ (getOp op2) n1 n2, k')
    (Unknown u1, Unknown u2) -> do
       Just k' <- instantiate u1 k2 
       Just k'' <- instantiate u2 k' 
       (Lit n1) <- luckNote "singleton after instantiation" $ fromSingleton k'' (U u1)
       (Lit n2) <- luckNote "singleton after instantiation" $ fromSingleton k'' (U u2)
       return (Lit $ (getOp op2) n1 n2, k'')
    _ -> error $ show (l1, l2)
narrow e@(If e1 e2 e3) k = do 
  (v, k') <- narrow e1 k 
  rs <- ask
  let (t, f) = (_conTrue rs, _conFalse rs)
  case v of 
    ADT cid _ -> narrow (if cid == t then e2 else e3) k'
    Unknown u -> error "implement unknown boolean narrowing"
    _ -> error $ show ("wtf: ", v)
narrow (ADT cid es) k = 
  first (ADT cid . reverse) 
  <$> foldM (\(res,k) e -> first (:res) <$> narrow e k) ([],k) es
narrow (Call (Var fid) es) k = do 
  rs <- ask
--  debug $ \v c -> "Calling function (narrow) " ++ v ! (fst fid, 0) ++ " : " ++ concat (intersperse "\n" $ map (\e -> printExp v c e) es)
  --  debug $ \v c -> prettyPr k v c 
  let (FItem args e) = _fMap rs ! (fst fid, 0)
  narrow (Call (Fun args e) es) k
narrow (Call (Fun args e) es) k =
  if length args == length es then do
    -- First rename ALL the variables in the body
    (es',k') <- first reverse <$> foldM (\(acc,k) e -> do 
                                          (v, k') <- narrow e k
                                          return (v:acc, k')
                                        ) ([],k) es
    increaseIdx
    s <- get
    let eRenamed = rename Set.empty (_idx s) e
    -- Then replace the arguments in the body with the expressions
  --  let es' = map (forceBinops k) es
    let e' = subst eRenamed (map (\((x,_),_) -> (x,_idx s)) args) es'
--    debug $ \v c -> "Body of function is:\n " ++ printExp v c e' 
    -- Finally call the narrow of the new body
    (rv,rk) <- narrow e' k'
--    debug $ prettyPr rk
    return (rv, rk)
  -- TODO: Optimize. narrow (Case (Unknown u) alts) w k =
  else error "Implement narrow for partial applications"
narrow e@(Fun _ _) k = return (e, k)
narrow e@(Case d alts) k = do
--  debug $ \v c -> "In Case\n" ++ printExp v c d ++ "\n" ++ (concat $ intersperse "\n" $ map (printAlt v c) alts)
  rs <- ask
  weights <- mapM (\(Alt _ ew _ _) -> do 
                      (e, _) <- narrow ew k
                      return $ extractInt (_revVMap rs) e k
                  ) alts
  opts <- randomize $ zip weights
                    $ map (\(Alt _ _ pat e') -> do
                            let us = getUnknownsP pat
--                            debug $ \v c -> "Handling branch: \n" ++ printExp v c d ++ "\n" ++  printPat v c pat
--                            debug $ \v c -> prettyPr k v c
                            (_, k') <- semantics d pat k  
--                            debug $ \v c -> "After narrow: \n" ++ printFor k' us v c
--                            debug $ \v c -> prettyPr k' v c
                            let e'' = subst e' us (map Unknown us)
                            (rv, rk) <- narrow e'' k'
--                            debug $ \v c -> prettyPr rk v c 
                            return (rv, rk)
                          ) alts
  -- not sure if backtracking is the correct choice here...
  backtrack (\v c -> "Backtracking... (CASE)" ++ printAltPats v c alts ) $ opts
--narrow (Fix e) w k = error "implement fix"
--narrow (FixN n e) w k 
--    | n == 0 = return (e, k)
--    | otherwise = do 
----       debug $ \v c -> "In Fix With:\n" ++ prettyPr k v c
--       (_, k') <- narrow e w k 
----       debug $ \v c -> "After Narrow of Fix:\n" ++ prettyPr k' v c
--       narrow (FixN (n-1) e) w k'
narrow (Inst e u) k = do 
  (e', k') <- narrow e k 
  Just k'' <- instantiate u k'
  return (e', k'')
narrow (Fresh x n e) k = do 
  s <- get 
  let e' = subst e [x] [Unknown x]
  (Lit n', k') <- narrow n k
  let k'' = bind k' x n' -- why bind?
  narrow e' k''
-- TRACE
-- Collect
narrow e k = error $ "Unhandled" ++ show (e,k)

forceBinops :: CtrSet -> Exp -> Exp
forceBinops k (Lit n) = Lit n
forceBinops k (Unknown u) 
    | Just (Lit n) <- fromSingleton k (U u) = Lit n
    | otherwise = Unknown u
forceBinops k (Binop e1 op e2) = Lit $ (getOp op) (extractInt undefined e1 k) (extractInt undefined e2 k)
forceBinops k e = e

extractInt :: Map VarId String -> Exp -> CtrSet -> Int
extractInt _ (Lit n) k = n
extractInt v (Unknown u@(uid,_)) k 
    | Just (Lit n) <- fromSingleton k (U u) = n
    | otherwise = error ("Not instantiated before arithmetic for : " ++ show (v ! (uid,0)))
extractInt v (Binop e1 op e2) k = 
    let n1 = extractInt v e1 k
        n2 = extractInt v e2 k
    in (getOp op) n1 n2 
extractInt _ e k = error $ "Incorrect type?" ++ show (e, k)

getUnknownsP :: Pat -> [Unknown]
getUnknownsP (PVar x) = [x]
getUnknownsP (PApp cid ps) = 
  concatMap getUnknownsP ps
getUnknownsP (PLit n) = []
getUnknownsP PWild = []

-- | Rename a body's variables except for <set> (should have no unknowns) to an index
rename :: Set Int -> Int -> Exp -> Exp
rename vars idx (Var (x,m)) | Set.member x vars = Var (x,m)
                            | otherwise = Var (x, m + idx) -- TODO: maybe add?
--rename vars idx (Var (x,m)) = Var (x, m + idx)
rename vars idx (Unknown (x,m)) = error $ "Should this happen " ++ show (x, m)
rename vars idx (Unop op e)  = Unop op (rename vars idx e)
rename vars idx (Binop e1 op e2) = 
    Binop (rename vars idx e1) op (rename vars idx e2)
rename vars idx (If e1 e2 e3) = 
    If (rename vars idx e1) (rename vars idx e2) (rename vars idx e3)
rename vars idx (ADT cid exps) = 
    ADT cid (map (rename vars idx) exps)
--rename vars idx (Call (Var fid) exps) = 
--    Call (Var fid) $ map (rename vars idx) exps
rename vars idx (Call f exps) = 
    Call (rename vars idx f) $ map (rename vars idx) exps
rename vars idx (Fun vs e) =
    let vars' = Set.union vars (Set.fromList (map (fst . fst) vs)) in
    Fun vs (rename vars' idx e)
rename vars idx (Case e alts) = 
    Case (rename vars idx e) (map (renameAlt vars idx) alts)
rename vars idx (Fix e) = 
    Fix (rename vars idx e)
rename vars idx (FixN n e) = 
    FixN n (rename vars idx e)
rename vars idx (Fresh (x,m) n e) = Fresh (x, m + idx) n (rename vars idx e)
--rename vars idx (Fresh _ _ _) = error "Should not happen"
rename vars idx (Inst e (x,m)) = Inst (rename vars idx e) (x, m + idx)
--rename vars idx (Inst e _) = error "Should *this* happen?"
rename _ _ (Lit x) = Lit x
rename vars idx (TRACE e e') = TRACE (rename vars idx e) (rename vars idx e')
--rename vars idx x = error $ "Core/Interpreter/rename error - unhandled: "  ++ show x

renameAlt :: Set Int -> Int -> Alt -> Alt
renameAlt vars idx (Alt loc w p e) =
    Alt loc (rename vars idx w) (renamePat idx p) (rename vars idx e)

renamePat :: Int -> Pat -> Pat
renamePat idx (PVar (x,m)) = PVar (x, m + idx)
--renamePat idx (PVar (x,n)) = error $ "shouldnothappend: " ++ show (x,n)
renamePat idx (PApp cid ps) = 
    PApp cid $ map (renamePat idx) ps
renamePat idx p = p

subst :: Exp -> [VarId] -> [Exp] -> Exp
subst e vs es = aux e 
  where m = Map.fromList $ zip vs es
        
        aux (Var x) =
--          traceShow ("aux/subst/var", x, m, Map.lookup x m) $
          case Map.lookup x m of 
            Just e' -> e'
            Nothing -> Var x 
        aux (Unknown u) = Unknown u
        aux (Lit n) = Lit n
        aux (Unop op e) = Unop op $ aux e
        aux (Binop e1 op e2) = Binop (aux e1) op (aux e2)
        aux (If e1 e2 e3) = If (aux e1) (aux e2) (aux e3)
        aux (ADT cid es) = ADT cid $ map aux es
        aux (Case e alts) = Case (aux e) $ map auxAlt alts
        aux (Inst e x) = 
          case Map.lookup x m of 
            Just (Unknown u') -> Inst (aux e) u'
            Nothing -> Inst (aux e) x
        aux (Fresh x e1 e2) = -- x is *never* an argument
          Fresh x (aux e1) (aux e2)
        aux (Fix e) = Fix (aux e)
        aux (FixN n e) = FixN n (aux e)
        aux (TRACE e1 e2) = TRACE (aux e1) (aux e2)
        aux (Collect e1 e2) = Collect (aux e1) (aux e2)
        aux (Call (Var fid) es) =
--          traceShow ("aux/subst", fid) $ 
          case Map.lookup fid m of 
            Just (Var f') -> Call (Var f') $ map aux es
            Just e -> Call e (map aux es)
            _ -> Call (Var fid) $ map aux es
        aux (Call f es) = Call f (map aux es)
        aux (Fun vs e) = Fun vs (aux e)

        auxAlt (Alt l ew p e) = Alt l (aux ew) p (aux e) -- Nothing should be substituted in a pat

--  
-- semantics e@(Conj e1 e2) w k = do 
--   (t, f) <- getTF -- OPT: if this was an actual argument and not looked up it could be faster
--   if | w == ADT t [] -> do -- Generate for True (chain the conjunctions)
--        (k1, e1') <- semantics e1 w k 
--        (k2, e2') <- semantics e2 w k1
--        return (k2, Conj e1' e2')
--      | w == ADT f [] -> do -- Generate for False (choice, potentially backtrack)
--        b <- uniform [True, False]
--        backtrack $ map (\e -> semantics e w k) 
--                  $ if b then [e1, e2] else [e2, e1]
--      | otherwise ->  -- w is an unknown (It can't be anything else)
--         error "What to do here"
-- -- Disj
