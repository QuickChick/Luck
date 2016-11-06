-----------------------------------------------------------------------------
-- |
-- Module      :  Core.AST
-- Copyright   :  (c) Leonidas Lampropoulos, 2014,
-- 
-- License     :  ??
--
-- Standard AST for the Core language for generators. 
-- Heavily influenced by Language.Haskell.Src
--
-----------------------------------------------------------------------------
module Core.AST where

import Common.SrcLoc
import Common.Pretty
import qualified Common.Types as CT

import Text.PrettyPrint.HughesPJ (Doc, (<+>))
import qualified Text.PrettyPrint.HughesPJ as PP

import Data.Map.Strict(Map)
import qualified Data.Map as Map

-- | Types of Identifiers
type ConId   = Int
type TyConId = String
type VarId   = (Int, Int) 
-- ^ First identifier is the unique translation from source
-- string. Second is recursion depth.  This approach retains type
-- information (via the first) and allows sharing it across all
-- "fresh" ones.
type TyVarId = String
type Unknown = (Int, Int)

type TcType = CT.TcType TyConId TyVarId 
type Scheme = CT.Scheme TyConId TyVarId
type TcEnv  = CT.TcEnv VarId ConId TyConId TyVarId

-- | Program is a list of top-level declarations
type Prg = [Decl] 

-- | A function level declaration (types are already enforced at core level)
data Decl = FunDecl SrcLoc VarId [(VarId,Int)] Exp
            deriving (Eq, Ord, Show)

-- | Core Language Expressions. 
data Exp = Var {unVar :: VarId}    -- ^ variable 
         | Unknown {unUnknown :: Unknown}         -- ^ unknowns
         | Lit Int                 -- ^ literal constant
         | Unop Op1 Exp            -- ^ unary operators
         | Binop Exp Op2 Exp       -- ^ infix application
         | If Exp Exp Exp          -- ^ conditionals
         | ADT ConId [Exp]         -- ^ fully applied constructor
         | Case Exp [Alt]          -- ^ case expression
         | Inst Exp Unknown        -- ^ instantiate an unknown after the expression
         | Fresh Unknown Exp Exp   -- ^ fresh unknown at some depth. TODO: Include type info?
         | Fix Exp                 -- ^ fix a transformer on some unknowns
         | FixN Int Exp            -- ^ fix a transformer a certain number of times (opt)
         | TRACE Exp Exp
         | Collect Exp Exp 
         | Call VarId [Exp]        -- ^ Fully applied function calls. TODO: Rethink
           deriving (Eq, Ord, Show)

-- | Alternatives in a case expression
data Alt = Alt SrcLoc Exp Pat Exp
          -- ^ A possibly weighted alternative in a case expression
         deriving (Eq, Ord, Show)

-- | Patterns for case expressions
data Pat = PVar Unknown -- ^ variable
         | PLit Int     -- ^ literal constant
         | PApp ConId [Pat] -- ^ constructor and argument patterns
         | PWild -- ^ wildcard pattern
           deriving (Eq, Ord, Show)

-- | Binary operators
data Op2 = OpPlus
         | OpMinus
         | OpTimes
         | OpDiv
         | OpMod
         -- Booleans from now on :)
         | OpEq
         | OpNe
         | OpLt
         | OpGt
         | OpLe
         | OpGe
           deriving (Eq, Ord, Show)

boolBinop :: Op2 -> Bool
boolBinop x = x >= OpEq

getOp :: Op2 -> Int -> Int -> Int
getOp OpPlus  = (+)
getOp OpMinus = (-)
getOp OpTimes = (*)
getOp OpDiv   = div
getOp OpMod   = mod

-- | Unary operators 
data Op1 = OpNeg 
           deriving (Eq, Ord, Show)

-- | Gather all top level function definitions
gatherTopFuns :: Prg -> [(VarId, [(VarId,Int)], Exp)]
gatherTopFuns [] = []
gatherTopFuns (FunDecl _ x args e : xs) = (x,args,e) : gatherTopFuns xs

-- | Information for a single function
data FItem = FItem { _fArgs :: [(VarId, Int)]
                   , _fExp  :: !Exp
                   } deriving (Eq, Show)


-- | Maps from function identifiers to function information
type FMap = Map VarId FItem 

