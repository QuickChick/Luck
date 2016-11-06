{- | Automatic generators for ADTs.
 -
 - Cf. A PropEr Integration of Types and Function Specifications with PBT,
 - by Manolis Papadakis and Konstantinos Sagonas.
 -
 - Naming conventions:
 - - @v@, variables; @c@: constructors; (value level)
 - - @tc@, type constructors; @tv@: type variables;
 - - @funNameS@, action within a state monad.
 -
 - TODO: add weights to alternatives
 -
 - Possible extension: higher kinded types (kind <-> generator type),
 -}
{-# LANGUAGE RecordWildCards, TemplateHaskell, RankNTypes, DeriveFunctor, FlexibleContexts #-}
module Core.Types.Generator where

import Control.Applicative
import Control.Lens hiding (Choice)
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Random

import Data.Either
import Data.Function
import Data.List
import Data.Ratio
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Map as Map

import Common.Types
import Common.Util

-- * Types

data Void

newtype TyVarId = TyVarId Int deriving (Eq, Ord, Show)

type Type = TcType

-- | Partial values with typed holes.
-- TODO merge with ZCSet
data DataPat' c b
  = DPCon c [DataPat' c b]
  | DPLeaf b
  deriving (Eq, Ord, Show, Functor)

type DataPat c tc tv = DataPat' c (Type tc tv)

-- | Fully defined values.
data DataTree c
  = DCon c [DataTree c]
  | DInt Int
  deriving (Eq, Ord, Show, Functor)

-- | Generators (wrapped in a monadic action)
-- parameterized by other generators, indexed by type @i@.
type GenWithSubGen i m x = Map i (m x) -> m x
type DataGen' c tv m = GenWithSubGen tv m (DataTree c)

-- | Generators of fully defined values, that act in the monad @m@.
data DataGen c tv m = DataGen
  { genArgs :: [tv] -- ^ Sorted list of type variables (indices expected to map to a generator).
  , genData :: DataGen' c tv m
  }

-- | Mapping from type constructors @tc@ to data generators.
type DataGenMap c tc tv m = Map tc (DataGen c tv m)

-- * "Sized" actions

type Sized = ReaderT Int

unsized :: Monad m => m a -> Sized m a
unsized = lift

scale :: Monad m => (Int -> Int) -> Sized m a -> Sized m a
scale = local

resize :: Monad m => Int -> Sized m a -> Sized m a
resize = local . const

sized :: Monad m => (Int -> m a) -> Sized m a
sized = ReaderT

sized' :: Monad m => (Int -> Sized m a) -> Sized m a
sized' = (ask >>=)

runSized :: Monad m => Int -> Sized m a -> m a
runSized = flip runReaderT

countLeaves :: DataPat c tc tv -> Int
countLeaves (DPCon _ ts) = sum (countLeaves <$> ts)
countLeaves (DPLeaf _) = 1

-- * Weighted choices

-- | All inliner functions assume the sum of the weights to be 1
-- (simplifying intermediate explicit renormalization).
type Weight = Ratio Int

-- Take the product of weights.
combine :: ([a] -> b) -> [(Weight, a)] -> (Weight, b)
combine f was =
  let (ws, as) = unzip was
  in (product ws, f as)

scaleWeights :: Weight -> [(Weight, a)] -> [(Weight, a)]
scaleWeights s = map (\(w, a) -> (s * w, a))

intWeights :: [(Weight, a)] -> [(Int, a)]
intWeights was =
  let (ws, as) = unzip was
      wLCM = foldl' lcm 1 . map denominator $ ws
  in zip ((\w -> numerator w * (wLCM `div` denominator w)) <$> ws) as

always :: a -> [(Weight, a)]
always a = [(1, a)]

-- * Create generators from partial values with typed holes

-- | Create a parameterized generator for a type constructor,
-- given a view of generators of all types in the program to handle recursive
-- calls.
--
-- The generator chooses a partial value and recursively fills in the holes.
mkDataGen :: (MonadRandom m, Ord tc, Ord tv)
  => DataGenMap c tc tv (Sized m) -- ^ Sized generators
  -> tc -> DataGen c tv m
  -> [tv] -- ^ @T::tc, [u,v,w]::[tv]@ represents of the type "@T u v w@".
  -> Choice (Int, DataPat c tc tv)
  -- ^ Alternatives tagged with number of revursive references.
  -> DataGen c tv (Sized m)
mkDataGen g tc baseGen vs alts = mkDataGenM g k tc alts asTree localGen
  where
    k gen = DataGen vs $ \argGen -> sized $ \size ->
      if size == 0
      then genData baseGen $ Map.map (runSized 0) argGen
      else runSized size (gen argGen)
    asTree = snd
    localGen (0, _) = id
    localGen (1, _) = scale (subtract 1)
    localGen (leafCount, _) = scale (`div` leafCount)

-- | Create a base generator, same method.
mkBaseGen :: (MonadRandom m, Ord tc, Ord tv)
  => DataGenMap c tc tv m
  -> tc -> [tv]
  -> Choice (DataPat c tc tv)
  -> DataGen c tv m
mkBaseGen baseg tc vs alts = mkDataGenM baseg k tc alts id (const id)
  where
    k gen = DataGen vs gen

-- | An implementation shared by the two functions above.
mkDataGenM :: (MonadRandom m, Ord tc, Ord tv)
  => DataGenMap c tc tv m
  -> (DataGen' c tv m -> DataGen c tv m)
  -> tc
  -> Choice a -- ^ A @DataTree c@ with auxiliary information.
  -> (a -> DataPat c tc tv)
  -> (a -> m (DataTree c) -> m (DataTree c))
  -- ^ Use that information to update parameters (e.g., size) of recursive calls
  -> DataGen c tv m
mkDataGenM g k tc alts asTree localGen = k $ \ argGen -> do
  choose alts >>= \a -> localGen a (dataPatToGen (typedGen g argGen) (asTree a))

-- | Helper.
dataPatToGen :: MonadRandom m
  => (b -> m (DataTree c)) -- ^ what to do at the leaves
  -> DataPat' c b -> m (DataTree c)
dataPatToGen leafGen (DPCon c args) =
  liftM (DCon c) $ mapM (dataPatToGen leafGen) args
dataPatToGen leafGen (DPLeaf b) = leafGen b

-- | Generate a value of a given type.
typedGen :: (MonadRandom m, Ord tc, Ord tv)
  => Map tc (DataGen c tv m) -> Map tv (m (DataTree c))
  -> Type tc tv -> m (DataTree c)
typedGen g argGen (TcVar v) = argGen Map.! v
typedGen g argGen (TcCon c _ args) =
  let cGen = g Map.! c
      cArgGen = Map.fromList
        . zip (genArgs cGen) $ typedGen g argGen <$> args
  in genData cGen cArgGen

-- * Inlining

-- Each type is inlined with a separate initial state from others.

-- | Our specialization of the state monad with exceptions.
type Inliner tc a = ExceptT tc (State (InlState tc)) a

-- | The state keeps track of recursive types that we have failed
-- to inline, so we do not need to recheck.
data InlState tc = InlState { _noInline :: Set tc }

makeLenses ''InlState

inlineData :: (Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv -> Set tc -> Map tc [(Int, DataPat c tc tv)]
inlineData env baseTcs =
  Map.map intWeights . Map.mapWithKey (inlineTc env baseTcs) $ tyConEnv env

-- | Inline a type definition.
--
-- By this, we mean to unfold partial values as much as possible,
-- potentially increasing their number, but decreasing the number of
-- lookups of auxiliary generators as well as calls to a RNG.
inlineTc :: (Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv -> Set tc -> tc -> ([tv], [c]) -> [(Weight, DataPat c tc tv)]
inlineTc env baseTcs tc (vs, _) =
  let targs = TcVar <$> vs
      Right r = evalState
        (runExceptT $ inlineS' env Set.empty tc targs)
        (InlState (Set.insert tc baseTcs))
  in r

-- | Try to inline a definition.
inlineS :: (Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv -> Set tc -> Type tc tv -> Inliner tc [(Weight, DataPat c tc tv)]
inlineS _env _stack ty@(TcVar _) = return $ always (DPLeaf ty)
inlineS env stack ty@(TcCon tc _ targs) = do
  s <- get
  -- This needs to be checked first, to treat correctly
  -- references to the root type we are inlining.
  if tc `Set.member` _noInline s then return $ always (DPLeaf ty)
  -- An attempt at unfolding of a recursive type has been detected.
  -- Unwind back the the previous call on that type.
  else if tc `Set.member` stack then throwError tc
  else do
    let stack' = Set.insert tc stack
    catchError (inlineS' env stack' tc targs) $ \ tc' ->
      if tc == tc' then do
        noInline %= Set.insert tc
        return $ always (DPLeaf ty)
      else throwError tc'
inlineS _ _ _ = error "inlineS: Not implemented."

-- | Helper.
inlineS' :: (Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv -> Set tc
  -> tc -> [Type tc tv] -> Inliner tc [(Weight, DataPat c tc tv)]
inlineS' env stack tc targs = do
  let (vs, cs) = tyConEnv env Map.! tc
      sub = mkSub vs targs
  alts' <- forM cs $ \c -> do
    let Forall _ ty = conEnv env Map.! c
        cargsTy = fst (unFun $ subst sub ty)
    cargs' <- forM cargsTy $ inlineS env stack
    return $ combine (DPCon c) <$> sequence cargs'
  return . scaleWeights (1 % length cs) $ concat alts'

-- * Inlining for base cases

-- Base cases are also inlined, but within the same state instance,
-- to preserve "consistency" of base cases.

-- | Types are ranked depending on how well founded their base cases are.
data TypeRank
  = Simple -- ^ The type has clear base cases, is built-in, or can
           -- rely just on other @Simple@ types (inductively).
  | DependsVar -- ^ Clauses depend on some of the type variables.
  | Cyclic -- ^ Cyclic type dependency with no base case.
  deriving (Eq, Ord, Show)

-- | Specialized state monad.
type BaseInliner c tc tv = State (BaseInlState c tc tv)
-- | Remember inlinings and ranks.
data BaseInlState c tc tv
  = BaseInlState { _inlined :: Map tc (TypeRank, [(Weight, DataPat c tc tv)]) }

makeLenses ''BaseInlState

-- | Inline all type definitions at once.
inlineBase :: (Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv -> BaseInlState c tc tv
  -> Map tc [(Int, DataPat c tc tv)]
inlineBase env initState =
  let inl tc (vs, _) = inlineBaseS' env Set.empty tc (TcVar <$> vs)
      inlined = evalState (Map.traverseWithKey inl (tyConEnv env)) initState
  in Map.map (intWeights . snd) inlined

-- | Inline the definition of a type constructor applied to variables,
-- adding the result to the environment if it succeeds.
inlineBaseTcS :: (Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv -> Set tc -> tc
  -> BaseInliner c tc tv (TypeRank, [(Weight, DataPat c tc tv)])
inlineBaseTcS env stack tc = do
  s <- get
  remember s $ do
    let stack' = Set.insert tc stack
        (vs, cs) = tyConEnv env Map.! tc
    mixedAlts <- forM cs $ \c -> do
      let Forall _ ty = conEnv env Map.! c
          (cargs, _) = unFun ty
      case cargs of
        -- Failed attempts are left unrecorded, as they may later succeed
        -- when the corresponding type constructor is at the root instead.
        [] -> return (Simple, always (DPCon c []))
        _ -> do
          cargs' <- forM cargs $ inlineBaseS env stack'
          return $ priorityCon c cargs'
    return $ filterSimplest mixedAlts
  where
    -- If it has already been inlined previously, return the memoized value.
    remember s m =
      case Map.lookup tc (_inlined s) of
        Just alts -> return alts
        Nothing -> do
          alts <- m
          case fst alts of
            Cyclic -> return ()
            _ -> inlined %= Map.insert tc alts
          return alts

-- | Combine all alternatives of constructor arguments.
priorityCon :: c -> [(TypeRank, [(Weight, DataPat c tc tv)])]
  -> (TypeRank, [(Weight, DataPat c tc tv)])
priorityCon c cargs =
  (maximum (fst <$> cargs), combine (DPCon c) <$> sequence (snd <$> cargs))

-- | Keep the alternatives of lowest rank.
filterSimplest :: [(TypeRank, [(Weight, DataPat c tc tv)])]
  -> (TypeRank, [(Weight, DataPat c tc tv)])
filterSimplest alts =
  let rank = minimum $ fst <$> alts
      alts' = snd <$> filter ((rank ==) . fst) alts
  in (rank, scaleWeights (1 % length alts') . concat $ alts')

inlineBaseS :: (Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv -> Set tc -> Type tc tv
  -> BaseInliner c tc tv (TypeRank, [(Weight, DataPat c tc tv)])
inlineBaseS _env _stack ty@(TcVar v)
  = return (DependsVar, always (DPLeaf ty))
inlineBaseS env stack ty@(TcCon tc _ targs)
  = inlineBaseS' env stack tc targs

inlineBaseS' :: (Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv -> Set tc -> tc -> [Type tc tv]
  -> BaseInliner c tc tv (TypeRank, [(Weight, DataPat c tc tv)])
inlineBaseS' env stack tc targs = do
  if tc `Set.member` stack
  then return (Cyclic, [])
  else do
    r@(rk, alts) <- inlineBaseTcS env stack tc
    case rk of
      Simple -> return r
      Cyclic -> return (Cyclic, [])
      DependsVar -> do
        let (vs, _) = tyConEnv env Map.! tc
            sub = mkSub vs targs
        (filterSimplest <$>) . forM alts $ \(w, alt) ->
          (scaleWeights w <$>) <$> inlineBaseDataS env stack sub alt

-- | Unfold holes in a partial value.
inlineBaseDataS env stack sub (DPCon c cargs) =
  priorityCon c <$> mapM (inlineBaseDataS env stack sub) cargs
inlineBaseDataS env stack sub (DPLeaf ty) =
  inlineBaseS env stack (subst sub ty)

-- | Create generators for user-defined types, provided via the environment.
-- Generators for built-in types must be given from outside.
createDataGen :: (MonadRandom m, Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv
  -> Map tc (DataGen c tv (Sized m)) -- ^ Built-in generators
  -> Map tc (DataGen c tv m) -- ^ Base case generators
  -> (Map tc [(Int, DataPat c tc tv)], Map tc [(Int, DataPat c tc tv)]) -- ^ Inlinings
  -> Map tc (DataGen c tv (Sized m))
createDataGen env g baseGen (inlined, inlinedBase) = fix $ \g' ->
  Map.union g
    $ Map.mapWithKey (mkGen g') (baseGen `mapZip` (tyConEnv env `mapZip'` inlined))
  where
    mkGen g' tc (baseGen, (vs, alts)) =
      let alts' = map (\(w, a) -> (w, (countLeaves a, a))) alts
      in mkDataGen g' tc baseGen vs alts'

-- | Base generators.
createBaseGen :: (MonadRandom m, Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv -> DataGenMap c tc tv (Sized m)
  -> Map tc [(Int, DataPat c tc tv)]
  -> DataGenMap c tc tv m
createBaseGen env g inlinedBase = fix $ \g' ->
  Map.union (size0 g)
    $ Map.mapWithKey (uncurry . mkBaseGen g') (tyConEnv env `mapZip'` inlinedBase)
  where
    size0 = Map.map $ \DataGen{..} ->
      DataGen genArgs $ runSized 0 . genData . (unsized <$>)

-- | Inline definitions
inlineDataGen :: (Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv -> Map tc (DataGen c tv (Sized m))
  -> (Map tc [(Int, DataPat c tc tv)], Map tc [(Int, DataPat c tc tv)])
inlineDataGen env g =
  let inlinedBase = inlineBaseGen env g
      inlined = inlineData env (Map.keysSet g)
  in (inlined, inlinedBase)

inlineBaseGen :: (Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv -> Map tc (DataGen c tv m)
  -> Map tc [(Int, DataPat c tc tv)]
inlineBaseGen env g =
  let initState = BaseInlState . flip Map.mapWithKey g $ \ tc _ ->
        let (vs, _) = tyConEnv env Map.! tc
        in (Simple, always (DPLeaf (TcCon tc (length vs) (TcVar <$> vs))))
  in inlineBase env initState

make :: (MonadRandom m, Ord c, Ord tc, Ord tv)
  => TcEnv v c tc tv -> BuiltIn c tc tv
  -> ( DataGenMap c tc tv (Sized m), DataGenMap c tc tv m
     , Map tc [(Int, DataPat c tc tv)], Map tc [(Int, DataPat c tc tv)] )
make env bi = (gen, baseGen, inlined, inlinedBase)
  where
    gBuiltIn = mkGBuiltIn bi
    inl@(inlined, inlinedBase) = inlineDataGen env gBuiltIn
    baseGen = createBaseGen env gBuiltIn inlinedBase
    gen = createDataGen env gBuiltIn baseGen inl

mkGBuiltIn BuiltIn{..} = Map.fromList
  [ (biInt, DataGen [] (const . sized $ \n -> getRandomR (-n, n) >>= return . DInt))
  , (biList, DataGen [biListArg] (\subgen -> sized' $ \n -> do
      let m = intSquareRoot n
      l <- getRandomR (0, m)
      xs <- replicateM l $ resize m (subgen Map.! biListArg)
      return $ foldl' (\ t x -> DCon biListCons [x, t]) (DCon biListNil []) xs))
  ]

countNodes :: DataTree c -> Int
countNodes (DCon _ ts) = 1 + sum (map countNodes ts)
countNodes (DInt _) = 1

