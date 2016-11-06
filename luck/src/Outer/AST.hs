-----------------------------------------------------------------------------
-- |
-- Module      :  Core.AST
-- Copyright   :  (c) Leonidas Lampropoulos, 2016,
-- 
-- License     :  ??
--
-- Standard AST for the Core language for generators. 
-- Heavily influenced by Language.Haskell.Src
--
-----------------------------------------------------------------------------
{-# LANGUAGE ViewPatterns #-}
module Outer.AST where

import Common.SrcLoc
import qualified Common.Types as CT

import Data.List

-- | Types of Identifiers
type ConId   = String
type TyConId = String
type VarId   = String
type TyVarId = String

type OTcType = CT.TcType TyConId VarId 
type OScheme = CT.Scheme TyConId TyVarId
type OTcEnv  = CT.TcEnv VarId ConId TyConId TyVarId

-- | Program is a list of top-level declarations
type Prg = [Decl] 

-- | Constructor declaration
data ConDecl = ConDecl ConId [OTcType]          -- ^ ordinary data constructor
               deriving (Eq, Ord, Show)

-- | A top level declaration 
data Decl = DataDecl SrcLoc TyConId [TyVarId] [ConDecl] 
            -- ^ Datatype declaration
          | TypeSig SrcLoc VarId OTcType                      
            -- ^ TcType signature declaration
          | FunDecl SrcLoc VarId [(VarId,Maybe Int)] Exp
            -- ^ Function declaration. 
            deriving (Eq, Ord, Show)

-- | Core Language Expressions. Expose boolean primitives
data Exp = Var VarId               -- ^ variable 
         | Con ConId               -- ^ data constructor
         | Lit Literal             -- ^ literal constant
         | Unop Op1 Exp            -- ^ unary operators
         | Conj Exp Exp            -- ^ conjunction
         | Disj (Maybe Exp) Exp (Maybe Exp) Exp -- ^ disjunction
         | Binop Exp Op2 Exp       -- ^ infix application
         | App Exp Exp             -- ^ function application
         | If Exp Exp Exp          -- ^ if expression
         | Case Exp [Alt]          -- ^ case expression
         | Let Binds Exp           -- ^ local declarations let ... in ...
         | Fix Exp                 -- ^ Fixpoint
         | FixN Int Exp            -- ^ Indexed fixpoint
         | Fresh VarId OTcType Exp Exp -- ^ Generate Fresh Variable of some type with some depth limit
         | Inst Exp VarId          -- ^ Post-fix Instantiation point
         | TRACE VarId Exp         -- ^ Trace a variable (debugging)
         | Collect Exp Exp         -- ^ Collect statistics
           deriving (Eq, Ord, Show)

-- | Binding groups are just lists of declarations
type Binds = [Decl] 

-- | Alternatives in a case expression
data Alt = Alt
  { altLoc :: SrcLoc
  , altWeight :: Maybe Exp
  , altPat :: Pat
  , altExp :: Exp
  } -- ^ A possibly weighted alternative in a case expression
  deriving (Eq, Ord, Show)

-- | Implicit weights are equal to 1.
altWeight' :: Alt -> Exp
altWeight' (altWeight -> Just n) = n
altWeight' _ = litIntE 1

-- | Helper constructor for literal expressions.
litIntE :: Int -> Exp
litIntE = Lit . LitInt

-- | let' x = e in e'
letE :: VarId -> Exp -> Exp -> Exp
letE x e e' = Case e [Alt noLoc (Just $ litIntE 1) (PVar x) e']

-- | Constant literals
data Literal = LitInt Int -- ^ integer literals
               deriving (Eq, Ord, Show)

-- | Patterns for case expressions
data Pat = PVar VarId -- ^ variable
         | PLit Literal -- ^ literal constant
         | PApp ConId [Pat] -- ^ constructor and argument patterns
         | PWild -- ^ wildcard pattern
           deriving (Eq, Ord, Show)

isDefaultPat :: Pat -> Bool
isDefaultPat (PVar _) = True
isDefaultPat PWild = True
isDefaultPat _ = False

-- | Binary operators
data Op2 = OpPlus
         | OpMinus
         | OpTimes
         | OpDiv
         | OpMod
         | OpEq
         | OpNe
         | OpLt
         | OpGt
         | OpLe
         | OpGe
           deriving (Eq, Ord, Show)

-- | Unary operators 
data Op1 = OpNeg 
         | OpNot 
           deriving (Eq, Ord, Show)

-- | Pre-defined constructors
list_tycon_name :: TyConId 
list_tycon_name = "List"

nil_con_name, cons_con_name :: ConId 
nil_con_name  = "Nil"
cons_con_name = "Cons"

tuple_tycon_name :: Int -> TyConId
tuple_tycon_name n = "Tuple " ++ show n

tuple_con_name :: Int -> ConId
tuple_con_name n = "#" ++ show n

tc_int_tycon, tc_bool_tycon, tc_unit_tycon :: CT.TcType TyConId v
tc_int_tycon  = CT.TcCon "Int"  0 []
tc_bool_tycon = CT.TcCon "Bool" 0 []
tc_unit_tycon = CT.TcCon "Unit" 0 []

-- | Smart constructor that simplifies constants.
times :: Exp -> Exp -> Exp
times (Binop e1 OpTimes e2) e3 = times e1 . times e2 $ e3
times (Lit (LitInt n)) (Lit (LitInt m)) = litIntE (n * m)
times (Lit (LitInt n)) (Binop (Lit (LitInt m)) OpTimes e3)
  = Binop (litIntE (n * m)) OpTimes e3
times (Lit (LitInt 1)) e3 = e3
times e1 (Binop (Lit (LitInt n)) OpTimes e2)
  = Binop (litIntE n) OpTimes (Binop e1 OpTimes e2)
times e1 e2 = Binop e1 OpTimes e2

-- | Smart constructor that simplifies constants.
plus :: Exp -> Exp -> Exp
plus (Lit (LitInt n)) (Lit (LitInt m)) = litIntE (n + m)
plus e1 e2 = Binop e1 OpTimes e2

-- | Expression of a long sum.
sumE :: [Exp] -> Exp
sumE es = foldl1' plus es

