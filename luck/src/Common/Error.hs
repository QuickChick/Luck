{-# LANGUAGE FlexibleContexts #-}
module Common.Error where

import Common.SrcLoc 
import Common.Pretty 

import Data.Monoid

import Text.PrettyPrint.HughesPJ ((<+>))
import qualified Text.PrettyPrint.HughesPJ as PP

import System.Random
import Control.Monad.Except ( MonadError (throwError) )


data MsgCode = LexerError String
             | ParseError String
             | TypeError  String
             | InternalError String
             | UnSat String 
             | BacktrackMax 
             | GenericError String
               deriving (Show)

instance PP MsgCode where
    pp (LexerError s) = PP.text "Lexical error:" <+> PP.text s
    pp (ParseError s) = PP.text "Parse error:" <+> PP.text s
    pp (TypeError  s) = PP.text "Type error: " <+> PP.text s
    pp (InternalError s) = PP.text "Internal error: " <+> PP.text s
    pp (UnSat s) = PP.text "Not satisfiable: " <+> PP.text s
    pp (BacktrackMax) = PP.text "Maximum Backtracking Reached"
    pp (GenericError s) = PP.text s

isUnSat :: Message -> Bool
isUnSat (Message (UnSat _) _ _) = True
isUnSat _ = False

-- | Generic message datatype (fix later)
data Message = Message { msgCode :: MsgCode
                       , msgLoc  :: SrcLoc
                       , msgInfo :: String }
             deriving (Show)

instance PP Message where
    pp (Message c l info) = 
        PP.vcat [ pp c
               , PP.text "Starting at location:" <+> pp l
               , PP.text info ]

mkInternalError :: String -> Message
mkInternalError s = Message (InternalError s) noLoc ""

mkLexerError :: String -> SrcLoc -> String -> Message
mkLexerError s loc info = Message (LexerError s) loc info

mkParseError :: String -> SrcLoc -> String -> Message
mkParseError s loc info = Message (ParseError s) loc info

-- | No locations for type errors is stupid
mkTypeError :: String -> SrcLoc -> String -> Message
mkTypeError s loc info = Message (TypeError s) loc info

-- | UnSatisfiable errors
mkUnSat :: String -> Message
mkUnSat s = Message (UnSat s) noLoc ""

mkBacktrackMax :: Message
mkBacktrackMax = Message BacktrackMax noLoc ""

mkError :: String -> Message 
mkError s = Message (GenericError s) noLoc ""

-- | This is horrible :D
instance Monoid Message where
    mempty = Message (GenericError "mempty") noLoc ""
    mappend _m1 _m2 = error "Monoid message"

--instance Error Message where
--    strMsg s = Message (GenericError s) noLoc ""

throwInternalE :: MonadError Message m => String -> m a
throwInternalE = throwError . mkInternalError

throwParseE :: MonadError Message m => SrcLoc -> String -> String -> m a
throwParseE loc s info = throwError $ mkParseError s loc info

throwTypeE :: MonadError Message m => SrcLoc -> String -> String -> m a
throwTypeE loc s info = throwError $ mkTypeError s loc info

throwE :: MonadError Message m => String -> m a
throwE = throwError . mkError

