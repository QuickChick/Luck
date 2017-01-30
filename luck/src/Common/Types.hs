{-# LANGUAGE DeriveFunctor #-}
module Common.Types where

import Data.Data (ConIndex)
import Control.Arrow(first)
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map

import Common.Pretty (PP(..), Doc, (<+>))
import qualified Common.Pretty as PP

data TcType tyconid tyvarid = TcCon tyconid  Int [(TcType tyconid tyvarid)] 
                          | TcFun (TcType tyconid tyvarid) (TcType tyconid tyvarid)
                          | TcVar tyvarid
              deriving (Eq, Ord, Show, Functor)

fmap_tyvarid :: (tyvarid -> tyvarid') -> TcType tyconid tyvarid -> TcType tyconid tyvarid'
fmap_tyvarid f (TcCon c n lst) = TcCon c n (map (fmap_tyvarid f) lst)
fmap_tyvarid f (TcFun t1 t2) = TcFun (fmap_tyvarid f t1) (fmap_tyvarid f t2)
fmap_tyvarid f (TcVar x) = TcVar (f x)

data Scheme tyconid tyvarid = Forall (Set tyvarid) (TcType tyconid tyvarid)
            deriving (Eq, Show)

data TcEnv varid conid tyconid tyvarid = 
    TcEnv { varEnv :: Map varid (Scheme tyconid tyvarid)
          -- ^ maps variables to their types
          , conEnv :: Map conid (Scheme tyconid tyvarid)
          -- ^ maps data constructors to their types
          , conIndices :: Map conid ConIndex
          -- ^ maps data constructors to their indices in the datatype
          -- definition counting from 1,
          -- see Data.Data.ConIndex (base package)
          -- 
          -- > data List a = Nil -- 1
          -- >             | Cons a (List a) -- 2
          , tyConEnv :: Map tyconid ([tyvarid], [conid])
          -- ^ maps type constructors to their type arguments and data constructors
          } deriving (Eq, Show)

data BuiltIn c tc tv = BuiltIn
  { biInt :: tc
  , biList :: tc
  , biListArg :: tv
  , biListCons :: c
  , biListNil :: c 
  , biUnit :: c }

-- | Get the rightmost type in a function type.
resultType :: TcType c v -> TcType c v
resultType (TcFun _ r) = resultType r
resultType t = t

-- | Construct a function type
mkFun :: [TcType c v] -> TcType c v -> TcType c v
mkFun ts r = foldr TcFun r ts

unFun :: TcType c v -> ([TcType c v], TcType c v)
unFun (TcFun t1 t2) = first (t1 :) (unFun t2)
unFun t = ([], t)

resultTypeScheme :: Scheme c v -> TcType c v
resultTypeScheme (Forall _ t) = resultType t

newtype TSubstitution c v = Subs { unSubs :: Map v (TcType c v) }

substVar :: Ord v =>  TSubstitution c v -> v -> Maybe (TcType c v)
substVar = flip Map.lookup . unSubs

emptySub :: TSubstitution c v
emptySub = Subs Map.empty

mkSub :: Ord v => [v] -> [TcType c v] -> TSubstitution c v
mkSub vs ts = Subs . Map.fromList $ zip vs ts

subst :: Ord v => TSubstitution c v -> TcType c v -> TcType c v
subst s t@(TcVar y) = 
    case substVar s y of
      Just t' -> t'
      Nothing -> t
subst s (TcFun t1 t2) = TcFun (subst s t1) (subst s t2)
subst s (TcCon c n ts) = TcCon c n (map (subst s) ts)

after :: Ord v => TSubstitution c v -> TSubstitution c v -> TSubstitution c v
s2 `after` s1 = Subs $ fmap (subst s2) (unSubs s1) `Map.union` unSubs s2

instance (PP tc, PP tv) => PP (TcType tc tv) where
  pp = ppTy 0

ppTy :: (PP tc, PP tv) => Int -> TcType tc tv -> Doc
ppTy _ (TcVar v) = pp v
ppTy _ (TcCon tc _ []) = pp tc
ppTy n (TcCon tc _ targs) =
  par n conPrec . PP.hang (pp tc) 2 $ PP.sep (ppTy conPrec `fmap` targs)
ppTy n (TcFun t1 t2) =
  par n funPrec . PP.hang (ppTy funPrec t1) 2 $ PP.text "->" <+> ppTy funPrec t2

par n s = if n > s then PP.parens else id
conPrec = 2
funPrec = 1

instance (PP c, PP t) => PP (Scheme c t) where
    pp (Forall fvs ty) =
      ( if Set.null fvs then id
        else PP.hang (PP.text "forall" <+> PP.hsep (map pp (Set.toList fvs)) <+> PP.text ".") 2
        ) (pp ty)

