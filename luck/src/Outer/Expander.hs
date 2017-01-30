{-# LANGUAGE TupleSections, ViewPatterns, FlexibleContexts #-}
module Outer.Expander (expandWildcards) where

import Data.List (foldl', foldr, intercalate, transpose)
import Data.Maybe
import Common.Util
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad
import Control.Applicative

import Outer.AST
import Outer.Renamer (subsExp)
import Common.SrcLoc (noLoc)
import Common.Types hiding (TcType, TcEnv)
import Common.Error

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader

import Debug.Trace

import Control.Lens (over, _1, _2)

data Env = Env { tcEnv  :: OTcEnv
               , intMin :: Int
               , intMax :: Int
               }
         deriving (Eq, Show)

-- | A counter state allows to generate fresh variables.
type Expand = StateT Int (ReaderT Env (Either Message))

-- | Desugar case expressions @case e of {alts}@ to so that only PApp patterns
-- are left.
--
-- Pattern coverage is also checked. (Non-exhaustive/Unreachable patterns)
--
-- Desugaring introduces new variables. However, the environment is not
-- updated, but it doesn't appear to cause any problem in subsequent phases.
--
-- TODO (question) There may be a small issue with patterns consisting
-- of a single wildcard/variable:
--
-- @
-- case x of
-- | _ -> e
-- end
-- @
--
-- in which case we are simply desugaring that to @e@, but may this syntax
-- be a way to force evaluation of @x@?
--
expandWildcards :: Prg -> OTcEnv -> Int -> Int -> Either Message Prg
expandWildcards prg tcEnv iMin iMax
  = runReaderT
      (evalStateT (mapM expandDecl prg) 0)
      (Env tcEnv iMin iMax)

expandDecl :: Decl -> Expand Decl
expandDecl (FunDecl loc x xs e mt) = liftM (\e -> FunDecl loc x xs e mt) (expand e)
expandDecl d = return d

expand :: Exp -> Expand Exp
expand (Unop op e) = liftM (Unop op) (expand e)
expand (Conj e1 e2) = liftM2 Conj (expand e1) (expand e2)
expand (Disj w1 e1 w2 e2) = liftM3 (Disj w1) (expand e1) (pure w2) (expand e2)
expand (Binop e1 op e2) = liftM3 Binop (expand e1) (pure op) (expand e2)
expand (App e1 e2) = liftM2 App (expand e1) (expand e2)
expand (If e1 e2 e3) = liftM3 If (expand e1) (expand e2) (expand e3)
expand (Case e alts) = join $ liftM2 expandCase (expand e) (mapM expandAlt alts)
expand (Fun vs e) = Fun vs <$> expand e
expand (Fix e) = Fix <$> expand e
expand (FixN n e) = FixN n <$> expand e
expand (Fresh x t en e) = Fresh x t <$> expand en <*> expand e
expand (Inst e x) = liftM2 Inst (expand e) (pure x)
expand (TRACE v e) = TRACE v <$> expand e
expand (Collect e1 e2) = Collect e1 <$> expand e2
expand e@(Con _) = return e
expand e@(Var _) = return e
expand e@(Lit _) = return e
expand e = throwInternalE $ "Implement expand for " ++ show e

expandAlt :: Alt -> Expand Alt
expandAlt (Alt loc w p e) = liftM3 (Alt loc) w' (pure p) (expand e)
  where w' = Just <$> maybe (return $ litIntE 1) expand w

-- * Desugaring Nested Patterns (DNP)

type VSubstitution = Map VarId VarId
type Label = Int

-- | A @Label@led alternative being desugared (@Alt@),
-- with remaining patterns to desugar (@[Pat]@)
-- (on variables found from the context),
-- and a pending substitution (@VSubstitution@).
type PAlt = ([Pat], (Label, VSubstitution, Alt))

-- | This semi-transformer returns a request "upstream", the response is then
-- passed to the continuation to finish the computation purely.
-- @a@ could have been put in another monadic action but it's not needed here.
--
-- This is similar to the @Client@ type from the @pipes@ library,
-- with the main difference that exactly one query is allowed
-- (which prevents this to be a full-fledged transformer).
newtype Almost req rsp m a = Almost { runAlmost :: m (req, rsp -> a) }

-- | The @Almost@ semi-transformer is used to request the weights to assign to
-- alternatives from upstream: a request is the set of labels of reachable
-- alternatives, and the response is a map from those labels
-- to weight expressions.
type RequestingW = Almost (Set Label) (Map Label Exp) Expand

expandCase :: Exp -> [Alt] -> Expand Exp
-- This ignores the matched expression.
expandCase _ [Alt _ _ PWild e'] = return e'
-- @let' v = e in e'@
expandCase e alts@[Alt _ _ (PVar _) _] = return $ Case e alts
-- Actual pattern matching (or incorrect patterns).
expandCase e alts = do
    let (getVar, wrap) =
          case (e, findVar $ altPat <$> alts) of
            (Var (x,_), _) -> (return x, id)
            (_, Nothing) -> (freshDNPVar, substituteCase e)
            (_, Just v) -> (return v, letE v e)
    v <- getVar
    (activeAlts, finish) <- dnp v
    case filter (not . flip Set.member activeAlts . fst) enumAlts of
      [] -> return . wrap . finish
            . Map.fromList . (over _2 altWeight' <$>) $ enumAlts
      alts -> throwE . intercalate "\n"
         $ "Unreachable patterns:" : (show . altPat . snd <$> alts)
  where
    -- The two other cases for @expandCase@ should have caught other
    -- alternatives.
    substituteCase e (Case _ alts) = Case e alts
    substituteCase _ _ = error "Expender/substituteCase"
    dnp x = runAlmost $ dNP [x] pAlts
    enumAlts = zip [0..] alts
    pAlts = [ ([altPat alt], (l, Map.empty, alt)) | (l, alt) <- enumAlts ]

-- | Desugar pattern matching on the first variable and continue recursively.
-- Either all first patterns are defaults, then unwrap the single alternative
-- or at least one uses a constructor, from which we can derive all others.
dNP
  :: [VarId] -- ^ List of *variables* to pattern-match.
  -> [PAlt] -- ^ Alternatives with patterns on each variable.
  -> RequestingW Exp
  -- ^ Alternatives are fused, usually in a case expression,
  -- but reductions may take place.
-- When there are no more variables to match, the first alternative
-- gives the result expression. Other alts are discarded (but may end up
-- being used in other branches if they came from elaborated default patterns).
dNP [] ((_, (l, s, alt)) : _pAlts) = Almost $ return
    ( Set.singleton l -- This signals this alternative's being used.
    , const . subsExp s . altExp $ alt )
-- TODO Improve error message (give unmatched pattern).
dNP x [] = Almost $ throwE $ "Incomplete pattern: " ++ show x
dNP (v : vs) pAlts
  -- Variable patterns are turned into wildcards, with a substitution.
  = let pAlts' = clearPVar v . headFirst <$> pAlts
    in case findPApp $ fst <$> pAlts' of
      Nothing -> dNP vs $ snd <$> pAlts'
      Just c -> Almost $ do
        ctors <- getOtherCtors c
        (request, finish) <- runAlmost $ dNPPAlts vs ctors pAlts'
        return (request, Case (Var (v, Nothing)) . finish)

-- | We generalize the procedure to desugaring multiple patterns.
-- Unwrapping nested patterns queues them up in LIFO order.
dNPPAlts
  :: [VarId] -- ^ Variables that are left to pattern-match.
  -> [ConId] -- ^ Possible constructors at the root of the patterns.
  -> [(Pat, PAlt)]
  -- ^ The pattern tuple must be non-empty,
  -- which is enforced here by its first element (in fst)
  -- being separated from its tail (in snd).
  -> RequestingW [Alt]
dNPPAlts _ _ [] = error "dNPPAlts: empty list"
dNPPAlts vs ctors pAlts = Almost $ do
    gAlts <- groupByHead ctors pAlts
    finishers <- mapM desugar gAlts
    let request = Set.unions (fst <$> finishers)
        counts -- Count how many times each alternative is used. (> 0)
          = Map.fromSet
              (\l -> length . filter (Set.member l . fst) $ finishers)
              request
        countsLcm = Map.foldl lcm 1 counts
        -- Each alternative is copied with a weight inversely
        -- proportional to the number of copies.
        multipliers = Map.map (countsLcm `div`) counts
        reDistribute = Map.intersectionWith (times . litIntE) multipliers
        -- Each alternative group receives a submap restricted to its
        -- active subalternatives only.
        app ws req fin = fin (Map.intersection ws $ mapSet req)
        finish weights = uncurry (app $ reDistribute weights) <$> finishers
    return (request, simplWeights . finish)
  where
    desugar = runAlmost . (uncurry $ desugarAlt vs)
    mapSet = Map.fromSet (const ())

-- | Turn compatible alternatives into a single alternative.
--
-- Alternatives are compatible if the first @Pat@ component of each element
-- is either a wildcard or an application of the constructor represented by
-- the @ConId@ parameter.
--
-- @
--   | C x y z -> e1
--   | _ -> e2
-- @
--
-- In this context, the latter is considered equivalent to
-- (and turned into) @| C _ _ _ -> e2@.
--
-- The request from @Almost@ is the set of labels associated to
-- alternatives that are used at least once in this group.
--
-- The expected response is a map that assigns weights to these labels only
-- (i.e., no unused label).
--
desugarAlt :: [VarId] -> ConId -> [(Pat, PAlt)] -> RequestingW Alt
desugarAlt vs c pAlts = Almost $ do
    arity <- getNoArgs' c
    -- Remove subpatterns that do not need to be refined further.
    -- Gather by position instead of by alternative.
    let subPats = transpose $ expandPat arity <$> ps
    names <- mapM nameSubPats subPats
    let ps = nameToPat <$> names -- The list of Pats @c@ will be applied to
        (us, expanded') = unzip $ zipMaybe names subPats
        expanded = transpose expanded'
        vs' = us ++ vs
        pAlts' = case expanded of
          [] -> pAlts1 -- All subpatterns were wildcards
          _ -> zipWith (over _1 . (++)) expanded pAlts1
    (request, finish) <- runAlmost $ dNP vs' pAlts'
    let finish' ws = Alt noLoc (total ws) (PApp c ps) (finish ws)
    return (request, finish')
  where
    (ps, pAlts1) = unzip pAlts
    total = Just . sumE . Map.elems
    -- Extract the immediate subpatterns @C x y z --> [x, y, z]@.
    -- Convert wildcards @_ --> [_, _, _]@.
    expandPat n (PApp c qs) = qs
    expandPat n PWild = replicate n PWild
    expandPat _ p = error $ "desugarAlt: " ++ show p -- Should not happen
    -- Assign a name to a list of patterns if it contains at least one
    -- non-wildcard pattern (@PApp@ or @PVar@).
    -- For conciseness of the final output, if a pattern is a variable,
    -- its name is reused.
    nameSubPats ps
      | all (== PWild) ps = return Nothing
      | otherwise = Just <$>
          case findVar ps of
            Nothing -> freshDNPVar
            Just v -> return v
    nameToPat Nothing = PWild
    nameToPat (Just v) = PVar v

-- | Simplify weight constants.
simplWeights :: [Alt] -> [Alt]
simplWeights alts = simpl <$> alts
  where
    simpl (Alt l w p e) = Alt l ((`divE` gcdW) <$> w) p e
    gcdW = foldl' gcd' 0 (altWeight' <$> alts)
    gcd' n (Lit (LitInt m)) = gcd n m
    gcd' n (Binop (Lit (LitInt m)) OpTimes e) = gcd n m
    gcd' _ _ = 1
    (Lit (LitInt n)) `divE` d | n `mod` d == 0 = litIntE (n `div` d)
    (Binop (Lit (LitInt n)) OpTimes e) `divE` d
      | n `mod` d == 0 = Binop (litIntE (n `div` d)) OpTimes e
    e `divE` 1 = e
    e `divE` d = Binop e OpDiv (litIntE d)

-- * Small helper functions

-- | Fresh variable for DNP.
freshDNPVar :: Expand VarId
freshDNPVar = state $ \i -> ( "dnp" ++ show i, i + 1 )

-- | Convert variable patterns into wildcards, noting the substitution
-- by the *variable* being matched.
clearPVar :: VarId -> (Pat, PAlt) -> (Pat, PAlt)
clearPVar v (PVar w, pAlt) = (PWild, over (_2 . _2) (Map.insert w v) pAlt)
clearPVar _ pAlt' = pAlt'

-- | Separate the head of the fst element.
headFirst :: ([a], b) -> (a, ([a], b))
headFirst ((a : as), b) = (a, (as, b))
headFirst _ = error "headFirst: empty list"

-- | Find some @PVar@ and get its ID.
findVar :: [Pat] -> Maybe VarId
findVar = findMaybe fromPVar

-- | Get the first image that is not @Nothing@, if any.
findMaybe :: (a -> Maybe b) -> [a] -> Maybe b
findMaybe _ [] = Nothing
findMaybe f (h : t)
  = case f h of
      Nothing -> findMaybe f t
      found -> found

-- | Safely extract the @VarId@ from a @PVar@.
fromPVar :: Pat -> Maybe VarId
fromPVar (PVar v) = Just v
fromPVar _ = Nothing

-- | @zipMaybe [Just x, Nothing, Just z] [a, b, c] == [(x, a), (z, c)]@
zipMaybe :: [Maybe a] -> [b] -> [(a, b)]
zipMaybe vs ps = catMaybes $ zip' vs (pure <$> ps)
  where zip' = zipWith (liftM2 (,))

type Assoc a b = [(a, b)]

-- | Group alternatives by their "head constructor"
groupByHead :: [ConId] -> [(Pat, a)] -> Expand (Assoc ConId [(Pat, a)])
groupByHead ctors alts
  = Map.toList . Map.map reverse <$> foldM addAlt empty alts
  where
    addAlt altsByCtor alt@(p@(PApp c _), _)
      = return $ Map.adjust (alt :) c altsByCtor
    addAlt altsByCtor alt@(p, _)
      | isDefaultPat p = return $ Map.map (alt :) altsByCtor
      | otherwise = throwE $ "Invalid argument" ++ show p
    empty = Map.fromList [ (c, []) | c <- ctors ]

-- | Find a pattern that is a constructor application
-- (as opposed to a wildcard or a variable pattern).
findPApp :: [Pat] -> Maybe ConId
findPApp (PApp c _ : _) = Just c
findPApp (_ : ps) = findPApp ps
findPApp [] = Nothing

-- | Obtain the list of constructors of a datatype that the parameter
-- belongs to.
getOtherCtors :: ConId -> Expand [ConId]
getOtherCtors c = do
    env <- tcEnv <$> ask
    case Map.lookup c (conEnv env) of
      Just (Forall _ (resultType -> TcCon tyConId _ _)) ->
        case flip Map.lookup (tyConEnv env) tyConId of
          Nothing -> throwInternalE $ show (tyConId, tyConEnv env)
          Just (_, n) -> return n
      e -> throwInternalE $ "(getOtherCtors): " ++ show c ++ " : " ++ show e

getNoArgs :: ConId -> OTcEnv -> Int
getNoArgs cid tEnv =
    case (conEnv tEnv) ! cid of
      Forall _empty tcType -> (aux tcType) - 1
          where aux (TcCon _ _ _) = 1
                aux (TcFun _ y) = 1 + aux y
                aux (TcVar _) = 1

-- | Get the number of arguments of a constructor.
getNoArgs' :: ConId -> Expand Int
getNoArgs' c = getNoArgs c . tcEnv <$> ask

