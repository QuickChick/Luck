{-# LANGUAGE TupleSections, RecordWildCards, TemplateHaskell #-}
module Outer.Types where

import Data.Data
import Data.Functor
import Data.List
import Data.Foldable (foldlM)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Writer

import Control.Lens

import Outer.AST
import Common.Pretty (PP(..), (<+>))
import qualified Common.Pretty as PP
import Common.SrcLoc
import Common.Error
import Common.Types

import Debug.Trace

instance PP TyVarId' where
  pp (Flexible v) = pp v
  pp (Rigid v) = PP.text "R!" <> pp v

unPrimeTyVarId :: TyVarId' -> TyVarId
unPrimeTyVarId (Flexible v) = v 
unPrimeTyVarId (Rigid v) = v

-- * Type checking state monad

-- | Assumes ALL variables have different IDs (Rewriting phase needed!)
type TcMonad a = WriterT [Constraint]
                  (StateT TcState
                   (Either Message)) a

data Constraint = Equal OTcType' OTcType' String deriving (Eq, Show)

data TcState = TcState { freshNum :: !Int
                       , _tcEnv   :: OTcEnv' 
                       }
             deriving (Eq, Show)

makeLenses ''TcState

runTc :: OTcEnv' -> TcMonad a -> Either Message (a, [Constraint])
runTc tcEnv m = evalStateT (runWriterT m) (TcState 0 tcEnv)

getTc :: TcMonad OTcEnv'
getTc = liftM _tcEnv get

putTc :: OTcEnv' -> TcMonad ()
putTc = modifyTc . const

modifyTc :: (OTcEnv' -> OTcEnv') -> TcMonad ()
modifyTc = modify . over tcEnv


-- | Runs a computation, then resets the state to its initial value.
localTc :: TcMonad a -> TcMonad a
localTc m = do
  env <- getTc
  x <- m
  putTc env
  return x

tcLookupVar :: VarId -> TcMonad OScheme'
tcLookupVar x = do
  TcEnv{varEnv = m} <- getTc
  case Map.lookup x m of
    Just ty -> return ty
    Nothing -> throwTypeE noLoc "Unbound Variable" x

tcLookupCon :: ConId -> TcMonad OScheme'
tcLookupCon x = do
  TcEnv{conEnv = m} <- getTc
  case Map.lookup x m of
    Just ty -> return ty
    Nothing -> throwTypeE noLoc "Unknown Constructor" x

fresh :: TcMonad TyVarId
fresh = do
  i@TcState{freshNum = s} <- get
  put $ i{freshNum = succ s}
  return $ "@" ++ show s

equate :: OTcType' -> OTcType' -> String -> TcMonad ()
equate t1 t2 s | t1 == t2  = return ()
               | otherwise = tell [Equal t1 t2 s]

equateTyMaybe :: Maybe Exp -> TcMonad (Maybe Exp)
equateTyMaybe Nothing = return Nothing
equateTyMaybe (Just e) = do
  (e',t) <- inferTy e
  -- TODO: Should this return updated exp? Disallowing typeclasses in weights seems ok
  equate tc_int_tycon t $ show ("Disj/weight", e)
  return (Just e')

inferTy :: Exp -> TcMonad (Exp, OTcType')
inferTy (Var (x, _)) = do 
  tx <- tcLookupVar x >>= instantiate
  return (Var (x, Just tx), tx)
inferTy (Con c) = tcLookupCon c >>= (((Con c,) <$>) . instantiate)
inferTy (Lit lit) = (Lit lit,) <$> inferLit lit
inferTy (Unop op e) = do
  to <- inferOp1 op
  (e', te) <- inferTy e
  equate to te $ show ("Unop", op, e)
  return (Unop op e', to)
inferTy (Conj e1 e2) = do
  (e1', t1) <- inferTy e1
  (e2', t2) <- inferTy e2
  equate tc_bool_tycon t1 $ show ("Conj-1", e1)
  equate tc_bool_tycon t2 $ show ("Conj-2", e2)
  return (Conj e1' e2', tc_bool_tycon)
inferTy (Disj ne1 e1 ne2 e2) = do
  ne1' <- equateTyMaybe ne1
  ne2' <- equateTyMaybe ne2
  (e1', t1) <- inferTy e1
  (e2', t2) <- inferTy e2
  equate tc_bool_tycon t1 $ show ("Disj-1", e1)
  equate tc_bool_tycon t2 $ show ("Disj-2", e2)
  return (Disj ne1' e1' ne2' e2', tc_bool_tycon)
inferTy (Binop e1 op e2) = do
  (t1, t2, tr) <- inferOp2 op
  (e1', t1') <- inferTy e1
  (e2', t2') <- inferTy e2
  equate t1 t1' $ show ("Binop", op, e1)
  equate t2 t2' $ show ("Binop", op, e2)
  return (Binop e1' op e2', tr)
inferTy (Fun vs e) = do
  m <- getTc
  tvs <- mapM (const $ Flexible <$> fresh) vs
  tr <- Flexible <$> fresh
  let assoc = Map.fromList . zip (map fst vs) $ Forall Set.empty <$> TcVar <$> tvs
  (e', tr') <- localTc $ do
    putTc m{varEnv = assoc `Map.union` varEnv m}
    inferTy e
  equate (TcVar tr) tr' $ "unnamed fun " ++ show (vs, e)
  putTc m
  return (Fun vs e', funify tvs tr)
inferTy (App e1 e2) = do
  (e1', t1) <- inferTy e1
  (e2', t2) <- inferTy e2
  tv <- TcVar <$> Flexible <$> fresh
  equate t1 (TcFun t2 tv) $ show ("App", e1, e2)
  return (App e1' e2', tv)
inferTy (If e1 e2 e3) = do
  (e1', t1) <- inferTy e1
  (e2', t2) <- inferTy e2
  (e3', t3) <- inferTy e3
  equate t1 tc_bool_tycon $ show ("If1", e1)
  equate t2 t3 $ show ("If23", e2, e3)
  return (If e1' e2' e3', t2)
inferTy (Case e alts) = do
  (e', t) <- inferTy e
  (alts', ts) <- unzip <$> mapM (inferTyAlt t) alts
  case ts of
    x:xs -> do
      forM_ xs $ \x' -> equate x x' $ show ("Pat Res", x, x')
      return (Case e' alts', x)  
    _    -> error "Empty branch"
--inferTy (Let binds e) = localTc $ do
--    inferTyDecls binds
--    inferTy e
--inferTy (Fix e) = inferTy e 
--inferTy (FixN n e) = inferTy e 
inferTy (Fresh x t en e) = do
  -- en denotes an integer expression
  (en', tn) <- inferTy en
  equate tn tc_int_tycon $ show ("Fresh", en, "Int")
  -- x is a fresh variable of type t. 
  -- TODO: What about polymorphic/rigid/flexible?
  modifyTc $ \m -> m{varEnv = Map.insert x (Forall Set.empty $ Rigid <$> t) (varEnv m)}
  (e', t') <- inferTy e 
  return (Fresh x t en' e', t')
inferTy (Inst e x) = do 
  (e', t) <- inferTy e 
  tx <- tcLookupVar x >>= instantiate 
  equate tx tc_int_tycon $ show ("Inst", x, tx)
  return (Inst e' x, t)
inferTy (Collect e1 e2) = do 
  (e1', _)  <- inferTy e1 
  (e2', t2) <- inferTy e2
  return (Collect e1' e2', t2)
inferTy (TRACE x e) = do 
  (e',t)  <- inferTy e
  return (TRACE x e', t)

inferTyAlt :: OTcType' -> Outer.AST.Alt -> TcMonad (Outer.AST.Alt, OTcType')
inferTyAlt t (Outer.AST.Alt loc weight p e) = localTc $ do
  inferTyPat t p
  (e', t) <- inferTy e
  return (Outer.AST.Alt loc weight p e', t)

inferTyPat :: OTcType' -> Pat -> TcMonad ()
inferTyPat t (PVar x) = modifyTc $ \m ->
  m{varEnv = Map.insert x (Forall Set.empty t) (varEnv m)}
inferTyPat t (PLit lit) = do
  t' <- inferLit lit
  equate t t' $ show ("PLit", lit)
inferTyPat t (PApp x pats) = do
  t' <- tcLookupCon x >>= instantiate
  equate t (resultType t') $ show ("PatApp", x, t)
  let go (TcCon _ _ _) [] = return ()
      go (TcFun t1 t2) (p:ps) = do
        inferTyPat t1 p
        go t2 ps
      go p _ = throwTypeE noLoc "Mismatch in pattern types" (show p)
  go t' pats
inferTyPat _t PWild = return ()

-- | @tcAppify C [v1 .. vn] [t1 .. tn] := t1 -> .. -> tn -> C v1 .. vn@
tcAppify :: c -> [v] -> [TcType c v] -> TcType c v
tcAppify cid vars ts = mkFun ts $ TcCon cid (length vars) (map TcVar vars)

-- | @funify [v1 .. vn] v := v1 -> .. -> vn -> v@
funify :: [v] -> v -> TcType c v
funify xs r = mkFun (TcVar <$> xs) (TcVar r)

dataDecl, sigDecl, classDecl :: Decl -> TcMonad ()

-- | Add user-defined types to the environment.
-- TODO: Check well-formedness of type definitions.
dataDecl (DataDecl loc cid vars cdecls) = do
  tcEnv <- getTc
  when (Map.member cid $ tyConEnv tcEnv)
    $ throwTypeE loc "Multiple type definitions with the same name." cid
  case let vs = sort vars
       in find (uncurry (==)) $ zip vs (tail vs) of
    Nothing -> return ()
    Just (v, _) -> throwTypeE loc "Duplicate type variable in type definition."
      $ "At type " ++ cid ++ ", duplicate " ++ v
  let vars' = Rigid <$> vars
      conEnv' = foldl' (\m (ConDecl dcid t) ->
                          Map.insert dcid
                            (Forall (Set.fromList vars')
                                    (tcAppify cid vars' ((<$>) Rigid <$> t))) m
                       ) (conEnv tcEnv) cdecls
      tyConEnv' = Map.insert cid (vars', conId <$> cdecls) (tyConEnv tcEnv)
      conIndices' = Map.union (conIndices tcEnv) $
        Map.fromList $ zipWith (\(ConDecl dcid _) i -> (dcid, i)) cdecls [1 ..]
  putTc $ tcEnv
    { conEnv = conEnv'
    , tyConEnv = tyConEnv'
    , conIndices = conIndices' }
  where
    conId (ConDecl c _) = c
dataDecl _ = return ()

-- | Add all functions to the environment, with their signature whenever
-- it is provided. Functions that do not have a signature can
-- be recognized from their type @Forall [] v@ where @v@ is just a
-- /flexible/ type variable.
-- | TODO: should it do something about class constraints?
sigDecl (TypeSig loc f bindings ty) = do
  tcEnv <- getTc
  case Map.lookup f $ varEnv tcEnv of
    Just (Forall _ (TcVar (Flexible _))) ->
      throwTypeE loc "Function signature must appear before its definition." f
    Just _ -> throwTypeE loc "More than one signature for one identifier." f
    Nothing -> do
      let ty' = Rigid <$> ty
          vs = fv ty'
          sch = Forall vs ty'
      putTc $ tcEnv{varEnv = Map.insert f sch $ varEnv tcEnv}
sigDecl (FunDecl _ f _ _ _) = do
  tcEnv <- getTc
  case Map.lookup f $ varEnv tcEnv of
    Just _ -> return ()
    Nothing -> do
      tv <- TcVar <$> Flexible <$> fresh
      let sch = Forall Set.empty tv
      putTc $ tcEnv{varEnv = Map.insert f sch $ varEnv tcEnv}
sigDecl _ = return ()

-- Handle a class (basically signatures for the bindings)
classDecl (ClassDecl loc cid cty binds) = 
  forM_ binds $ \(fid, ty) -> do 
    tcEnv <- getTc
    -- check that fv cty = fv ty'?
    let ty' = Flexible <$> ty
        vs = fv ty'
        sch = Forall vs ty'
--    traceShowM ("Registering ", fid, sch)
    putTc $ tcEnv{varEnv = Map.insert fid sch $ varEnv tcEnv}
    -- Add an empty binding for the function "fid" in the REnv
    -- (Ensures that we can identify which functions are typeclass-based, fast)
--    registerClassFun fid
classDecl _ = return ()

instanceDecl, funDecl :: Decl -> TcMonad Decl
-- | Do type inference on instance definitions
-- Before handling exactly as a function need to unify 
-- tyvar in   class X tyvar
-- with
-- ty in      instance {... =>} X ty
instanceDecl (InstanceDecl loc cid ty ctrs binds) = do
  binds' <- forM binds $ \(fid, args, exp,_) -> do
    tcEnv <- getTc
    -- simulating instantiation
    let (Forall vs fty') = varEnv tcEnv Map.! fid
        [v] = Set.toList vs
    w <- (const $ TcVar <$> Flexible <$> fresh) v
    equate w (Rigid <$> ty) $ "instance " ++ cid
    let fty = subst (mkSub [v] [w]) fty'
    tvs <- mapM (const $ Flexible <$> fresh) args
    tr <- Flexible <$> fresh
    equate fty (funify tvs tr) $ "fun " ++ fid
    let assoc = Map.fromList . zip (map fst args) $ Forall Set.empty <$> TcVar <$> tvs
    (exp', tr') <- localTc $ do
      putTc tcEnv{varEnv = assoc `Map.union` varEnv tcEnv}
      inferTy exp
    equate (TcVar tr) tr' $ "fun " ++ fid
    -- Restore type environment
    putTc tcEnv
    return (fid, args, exp', Just fty)
  return (InstanceDecl loc cid ty ctrs binds')
    -- Register new type in REnv (sticks after restore!) 
    -- The expression should also be class/inlined
--    registerInstance fid args exp' fty
instanceDecl d = return d

-- | Do type inference on a (recursive) function declaration
-- Get fresh variables for all arguments and result
-- Equate function with the functional type comprised of the fresh variables
-- Fully extend the environment to infer the type of e
-- Equate the result with the fresh variable for the result
-- Return the type variable that corresponds to the function
funDecl d@(FunDecl loc f args e _) = do
  m <- getTc
  fty <- rigidify $ varEnv m Map.! f
  tvs <- mapM (const $ Flexible <$> fresh) args
  tr <- Flexible <$> fresh
  equate fty (funify tvs tr) $ "fun " ++ f
  let assoc = Map.fromList . zip (map fst args) $ Forall Set.empty <$> TcVar <$> tvs
  (e',tr') <- localTc $ do
    putTc m{varEnv = assoc `Map.union` varEnv m}
    inferTy e
  equate (TcVar tr) tr' $ "fun " ++ f
  putTc m
  return (FunDecl loc f args e' (Just fty))
funDecl d = return d

-- | Work in several passes, so that functions can all call each other
-- and have access to all defined types.
inferTyDecls :: [Decl] -> TcMonad [Decl]
inferTyDecls prg = do
  mapM_ dataDecl prg
  mapM_ sigDecl prg
  mapM_ classDecl prg
  prg' <- mapM instanceDecl prg
  mapM funDecl prg'

-- | Returns the type of the literal
inferLit :: Literal -> TcMonad OTcType'
inferLit (LitInt _) = return tc_int_tycon

-- | Returns the type of the unary operator. Assumes type is preserved
inferOp1 :: Op1 -> TcMonad OTcType'
inferOp1 OpNeg = return tc_int_tycon
inferOp1 OpNot = return tc_bool_tycon

-- | Returns the argument types and result type for a binop.
inferOp2 :: Op2 -> TcMonad (OTcType', OTcType', OTcType')
inferOp2 OpPlus  = return (tc_int_tycon, tc_int_tycon, tc_int_tycon)
inferOp2 OpMinus = return (tc_int_tycon, tc_int_tycon, tc_int_tycon)
inferOp2 OpTimes = return (tc_int_tycon, tc_int_tycon, tc_int_tycon)
inferOp2 OpDiv   = return (tc_int_tycon, tc_int_tycon, tc_int_tycon)
inferOp2 OpMod   = return (tc_int_tycon, tc_int_tycon, tc_int_tycon)
inferOp2 OpEq    = return (tc_int_tycon, tc_int_tycon, tc_bool_tycon)
inferOp2 OpNe    = return (tc_int_tycon, tc_int_tycon, tc_bool_tycon)
inferOp2 OpLt    = return (tc_int_tycon, tc_int_tycon, tc_bool_tycon)
inferOp2 OpGt    = return (tc_int_tycon, tc_int_tycon, tc_bool_tycon)
inferOp2 OpLe    = return (tc_int_tycon, tc_int_tycon, tc_bool_tycon)
inferOp2 OpGe    = return (tc_int_tycon, tc_int_tycon, tc_bool_tycon)

-- | Pretty Printing
instance PP Constraint where
    pp (Equal t1 t2 err) = pp t1 <+> PP.text "=" <+> pp t2 <+> PP.text "AT" <+> PP.text err

type Substitution = TSubstitution TyConId TyVarId'

mgu :: OTcType' -> OTcType' -> String -> Either Message Substitution
mgu (TcFun l1 r1) (TcFun l2 r2) err = do
  s1 <- mgu l1 l2 err
  s2 <- mgu (subst s1 r1) (subst s1 r2) err
  return $ s1 `after` s2
mgu (TcVar a@(Flexible _)) t _err = varAsgn a t
mgu t (TcVar a@(Flexible _)) _err = varAsgn a t
mgu (TcVar (Rigid a)) (TcVar (Rigid b)) _err | a == b = return emptySub
mgu (TcCon c1 n1 ts1) (TcCon c2 n2 ts2) err
    | c1 == c2 && n1 == n2 =
--        traceShow ("Here", c1, n1, "Folding over", ts1, ts2) $
        foldM (\s (t1,t2) -> do
                 s' <- mgu (subst s t1) (subst s t2) err
                 return $ s `after` s'
              ) emptySub (zip ts1 ts2)
    | otherwise = throwTypeE noLoc "Mismatched constructors"
        (show (c1,n1) ++ " - " ++ show (c2,n2) ++ " AT " ++ err)
mgu t1 t2 err =
    throwTypeE noLoc "Types do not unify"
      (show t1 ++ " - " ++ show t2 ++ " AT " ++ err)

fv :: Ord v => TcType c v -> Set v
fv (TcVar v)     = Set.singleton v
fv (TcFun t1 t2) = (fv t1) `Set.union` (fv t2)
fv (TcCon _ _ ts) = Set.unions (map fv ts)

varAsgn :: TyVarId' -> OTcType' -> Either Message Substitution
varAsgn a t
    | t == TcVar a = return emptySub
    | a `Set.member` (fv t) =
       throwTypeE noLoc "Occur check fails" (show a ++ " in " ++ show t)
    | otherwise = return $ mkSub [a] [t]

instantiate :: OScheme' -> TcMonad OTcType'
instantiate (Forall vs ty) = do
  let vs' = Set.toList vs
  ws <- mapM (const $ TcVar <$> Flexible <$> fresh) vs'
  return $ subst (mkSub vs' ws) ty

-- | Turn a type scheme into a type, universally quantified variables
-- become rigid variables.
rigidify :: OScheme' -> TcMonad OTcType'
rigidify (Forall vs ty) = do
  let vs' = Set.toList vs
  ws <- mapM (const $ TcVar <$> Rigid <$> fresh) vs'
  return $ subst (mkSub vs' ws) ty

{-
generalize :: OTcType' -> [Constraint] -> TcMonad OScheme'
generalize ty constraints = do
  case solve constraints of
    Left err -> throwError err
    Right s  -> do
      env <- getTc
      let fvs = fv (subst s ty) `minus` fvEnv (substEnv s (varEnv env))
      return $ Forall fvs ty

fvEnv :: Map VarId OScheme' -> Set TyVarId'
fvEnv m = Map.foldr gather Set.empty m where
    gather (Forall vs ty) s = (fv ty `minus` vs) `Set.union` s

minus :: Ord a => Set a -> Set a -> Set a
minus = Set.foldr Set.delete
-}

-- | Generalize the type of functions that do not have an explicit signature.
substEnv :: Substitution -> Map VarId OScheme' -> Map VarId OScheme'
substEnv s env = Map.map (substs s) env where
   substs sub (Forall _ ty@(TcVar (Flexible _))) =
     let ty' = subst sub ty
         vs' = fv ty'
     in Forall vs' ty'
   substs _sub scheme = scheme -- Explicit type signature.

solve :: [Constraint] -> Either Message Substitution
solve cs =
    foldM (\s1 (Equal t1 t2 err) -> do
              s2 <- mgu (subst s1 t1) (subst s1 t2) err
              return (s2 `after` s1)
          ) emptySub cs

substExp :: Substitution -> Exp -> Exp
substExp s (Var (x, Just t)) = Var (x, Just $ subst s t)
substExp s (Var (x, Nothing)) = Var (x, Nothing)
substExp s (Con c) = Con c
substExp s (Lit l) = Lit l
substExp s (Unop op e) = Unop op $ substExp s e
substExp s (Conj e1 e2) = Conj (substExp s e1) (substExp s e2)
substExp s (Disj me1 e1 me2 e2) = Disj (substExp s <$> me1) (substExp s e1)
                                       (substExp s <$> me2) (substExp s e2)
substExp s (Binop e1 op e2) = Binop (substExp s e1) op (substExp s e2)
substExp s (App e1 e2) = App (substExp s e1) (substExp s e2)
substExp s (If e1 e2 e3) = If (substExp s e1) (substExp s e2) (substExp s e3)
substExp s (Case e alts) = Case (substExp s e) (map (substAlt s) alts)
substExp s (Fun vars e) = Fun vars (substExp s e) 
substExp s (Fresh x t e1 e2) = Fresh x t (substExp s e1) (substExp s e2)
substExp s (Inst e x) = Inst (substExp s e) x
substExp s (TRACE x e) = TRACE x (substExp s e)
substExp s (Collect e1 e2) = Collect (substExp s e1) (substExp s e2)

substAlt s (Outer.AST.Alt loc weight pat e) = Outer.AST.Alt loc weight pat (substExp s e)

substDcl :: Substitution -> Decl -> Decl
substDcl s (FunDecl loc f args e mt) = FunDecl loc f args (substExp s e) (subst s <$> mt)
substDcl s (InstanceDecl loc cid ty ctrs binds) = 
    InstanceDecl loc cid ty ctrs (map (\(a,b,e,mt) -> (a,b, substExp s e, subst s <$> mt)) binds)
substDcl s d = d

typeInference :: Prg -> Either Message (Prg, OTcEnv)
typeInference p =
    case runTc initOTcEnv (inferTyDecls p >>= (\p' -> (p',) <$> getTc)) of
      Left err -> Left err
      Right ((p', tcEnv), c) -> do
        s <- solve c
        let p'' = map (substDcl s) p'
        let TcEnv varEnv' conEnv' conIxs tyConEnv' = tcEnv
        return $ (p'', TcEnv
          { varEnv = generalizeMap $ substEnv s varEnv'
          , conEnv = generalizeMap conEnv'
          , conIndices = conIxs
          , tyConEnv = generalizeMap' tyConEnv' })
  where
    generalizeVar (Flexible v) = v
    generalizeVar (Rigid v) = v
    generalizeMap = Map.map (\(Forall vs ty) ->
                               Forall (Set.map generalizeVar vs)
                                      (generalizeVar <$> ty))
    generalizeMap' = Map.map (over _1 $ map generalizeVar)

-- | Builtin OTcEnv

initOTcEnv :: OTcEnv'
initOTcEnv = TcEnv Map.empty cE cIxs tcE where
    list_tyvar = Rigid "@@0"
    list_quant = Forall (Set.singleton list_tyvar)
    list_type  = TcCon list_tycon_name 1 [TcVar list_tyvar]

    bool_type  = Forall Set.empty (TcCon "Bool" 0 [])

    unit_type  = Forall Set.empty (TcCon "Unit" 0 [])

    -- Tuple types
    mkTuple n =
      let vars = tuple_vars n
          tcVars = TcVar `map` vars
      in
        ( tuple_con_name n
        , tuple_quant vars . foldr TcFun (tuple_type n tcVars) $ tcVars)
    tuple_vars n = [ Rigid $ "@@" ++ show i | i <- [1 .. n] ]
    tuple_quant = Forall . Set.fromList
    tuple_type n tcVars = TcCon (tuple_tycon_name n) n tcVars
    max_arity = 9

    cE = Map.fromList $
           [("Nil" , list_quant list_type)
           ,("Cons", list_quant (TcFun (TcVar list_tyvar)
                                       (TcFun list_type list_type)))
           ,("True" , bool_type)
           ,("False", bool_type)
           ,("()", unit_type)
           ] ++ [ mkTuple i | i <- [2 .. max_arity] ]
    tcE = Map.fromList $
            [("List", ([list_tyvar], ["Nil" , "Cons" ]))
            ,("Bool", ([], ["True", "False"]))
            ,("Int", ([], [])) -- TODO: Should be indicated as built-in type
            ,("Unit", ([], ["()"]))
            ] ++ [ (tuple_tycon_name i, (tuple_vars i, [tuple_con_name i]))
                 | i <- [2 .. max_arity] ]
    cIxs = Map.fromList $
            [("Nil", cIx ([] :: [()])), ("Cons", cIx [()])
            ,("False", cIx False), ("True", cIx True)
            ,("()", cIx ())
            ] ++ [ (tuple_con_name i, 1) | i <- [2 .. max_arity] ]
    cIx :: Data a => a -> ConIndex
    cIx = constrIndex . toConstr

oBuiltIn :: BuiltIn ConId TyConId TyVarId
oBuiltIn = BuiltIn
  { biInt = "Int"
  , biList = "List"
  , biListArg = "@@0"
  , biListCons = "Cons"
  , biListNil = "Nil"
  , biUnit = "()"
  }

removeClassBindings :: Prg -> OTcEnv -> OTcEnv
removeClassBindings prg (TcEnv ve ce ci tce) = TcEnv ve' ce ci tce 
  where ve' = foldr handleDecl ve prg
        handleDecl (ClassDecl _ _ _ binds) ve = 
            foldr (\(fid, _) acc -> Map.delete fid acc) ve binds
        handleDecl _ ve = ve
