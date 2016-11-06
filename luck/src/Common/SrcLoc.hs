module Common.SrcLoc where

import Data.Word8
import Data.Char

import Common.Pretty
import qualified Text.PrettyPrint.HughesPJ as PP

-- | Source location information
data SrcLoc = SrcLoc { srcFilename :: String
                     , srcLine     :: !Int
                     , srcColumn   :: !Int }
              -- ^ A single position in the source 
            | UnknownLoc String 
              -- ^ Generic indication of the position
              deriving (Eq, Ord)
            
instance Show SrcLoc where
    show (SrcLoc f l c) = f ++ ":" ++ show l ++ ":" ++ show c
    show (UnknownLoc s) = "Unknown Location: " ++ s

instance PP SrcLoc where 
    pp = PP.text . show

noLoc :: SrcLoc 
noLoc = UnknownLoc "-"

-- | Move the source location by one word
advanceSrcLoc :: SrcLoc -> Word8 -> SrcLoc
advanceSrcLoc loc@(SrcLoc f l c) w
    | w >= 0x80 && w < 0xC0        = loc
    | w == fromIntegral (ord '\n') = SrcLoc f (l+1) 1
    | w == fromIntegral (ord '\r') = SrcLoc f l     1
    | otherwise = SrcLoc f l (c+1)
advanceSrcLoc loc _ = loc 

data Located e = L { getLoc :: SrcLoc 
                   , unLoc  :: e }
                 deriving (Eq, Ord)

instance Show a => Show (Located a) where
    show (L _loc e) = show e


