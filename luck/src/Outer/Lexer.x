{
-- Turn off warnings in generated code
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -funbox-strict-fields -fno-warn-tabs #-}

module Outer.Lexer where

import Common.SrcLoc
import Common.Error
import Outer.ParseMonad

import Control.Monad.Except

import Data.Char
import Data.Int
import Data.Word (Word8)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.UTF8 as BSU

}

$digit    = 0-9
$lower    = [a-z]
$upper    = [A-Z]
$alpha    = [a-z A-Z]

@lid      = $lower [$alpha \_ \' \. $digit]*
@uid      = $upper [$alpha \_ \' \. $digit]*
@str      = \" .* \"

tokens :-

$white+         ;

<0> {
  case          { token TCase }
  of            { token TOf }
  end           { token TEnd }
  let           { token TLet }
  let'          { token TLetPrime }                             
  in            { token TIn }
  if            { token TIf }
  then          { token TThen }
  else          { token TElse }
  not           { token TNot }
  data          { token TData }
  sig           { token TSig } 
  fun           { token TFun }
  fix           { token TFix }
  fresh         { token TFresh }
  collect       { token TCollect }
  include       { token TInclude }
  class         { token TClass }
  instance      { token TInstance }
  where         { token TWhere }
  record        { token TRecord }

  @str          { lexStr }
  @lid          { lexLid }
  @uid          { lexUid }
  $digit+       { lexInt }

  "#TRACE"      { token TTRACE }
  "="           { token TAssign }
  "()"          { token TUnit }
  "("           { token TLParen }
  ")"           { token TRParen }
  "[|"          { token TLDelBracket }
  "|]"          { token TRDelBracket }
  "["           { token TLBracket }
  "]"           { token TRBracket }
  "{"           { token TLCurBracket }
  "}"           { token TRCurBracket }
  "_"           { token TUnd }
  "!"           { token TBang }
  ","           { token TComma }
  ":"           { token TColon } 
  "::"          { token TCons }
  "+"           { token TPlus }
  "-"           { token TMinus }
  "*"           { token TTimes }
  "/"           { token TDiv }
  "%"           { token TPercent }
  "&&"          { token TLAnd }
  "||"          { token TLOr }
  "=="          { token TEq }
  "/="          { token TNe }
  "<"           { token TLt }
  ">"           { token TGt }
  "<="          { token TLe }
  ">="          { token TGe }
  "->"          { token TArrow }
  "|"           { token TBar }
  "=>"          { token TFatArrow }
  ";"           { token TSemiColon }
  "."           { token TDot }

  "*)"          { mkLexerErrorP "Trying to close an unstarted comment" }
}

"--" .*         ;
"(*"            { embedComment }
<comments> {
  "*)"          { unembedComment }
  .             ;
}

.               { unknownChar }

{
data Token 
    = TAssign
    | TInt Int
    | TVar String
    | TCon String
    | TStr String
    | TUnit
    | TLParen
    | TRParen
    | TLBracket
    | TRBracket
    | TLDelBracket
    | TRDelBracket
    | TLCurBracket
    | TRCurBracket
    | TBang
    | TInclude
    | TCase
    | TOf
    | TEnd
    | TLet
    | TLetPrime
    | TIn
    | TIf
    | TThen
    | TElse
    | TData
    | TSig
    | TFun
    | TClass
    | TInstance
    | TRecord
    | TWhere
    | TInp
    | TUnd
    | TCons
    | TColon
    | TComma
    | TNot
    | TPlus
    | TMinus
    | TTimes
    | TDiv
    | TPercent
    | TLAnd
    | TLOr
    | TEq
    | TNe
    | TLt
    | TGt
    | TLe
    | TGe
    | TArrow
    | TFatArrow
    | TBar
    | TEof
    | TTRACE
    | TFix
    | TFresh 
    | TCollect
    | TSemiColon
    | TDot
  deriving (Eq, Show)

-- | Lexer actions :: Position -> Buffer -> Length -> P (Located Token)
type Action = SrcLoc -> BS.ByteString -> Int -> P (Located Token)

-- | Create a token at a given location
token :: Token -> Action
token t loc _buf _len = return (L loc t)

-- | Skip
skip :: Action
skip _loc _buf _len = lexToken

-- | Chain actions
chain :: Action -> Int -> Action
chain act code loc buf len = do {setLexState code ; act loc buf len}

-- | Begin a specific code action
begin :: Int -> Action
begin code = skip `chain` code

-- | Lex a string
lexStr :: Action
lexStr loc buf len = do
    let _:str = BSU.toString $ BSU.take (fromIntegral (len-1)) buf
    str `seq` return $ L loc (TStr str)

-- | Lex a lowercase identifier
lexLid :: Action
lexLid loc buf len = do
    let id = BSU.toString $ BSU.take (fromIntegral len) buf
    id `seq` return $ L loc (TVar id)

-- | Lex an uppercase identifier
lexUid :: Action
lexUid loc buf len = do
    let id = BSU.toString $ BSU.take (fromIntegral len) buf
    id `seq` return $ L loc (TCon id)

-- | Lex an integer literal
lexInt :: Action
lexInt loc buf len = do
    case BSC.readInteger buf of
        Just (num, _) -> num `seq` return $ L loc (TInt $ fromInteger num)
        Nothing -> throwError $ mkInternalError "lexInt"

-- | Start a new nested comment
embedComment :: Action
embedComment loc buf len = do
    incCommState
    begin comments loc buf len

-- | End a possibly nested comment
unembedComment :: Action
unembedComment loc buf len = do
    decCommState
    status <- getCommState
    if status == 0
        then begin 0 loc buf len
        else lexToken

-- | Unknown character.. error 
unknownChar :: Action
unknownChar loc buf len = do
    case BSU.decode buf of
        Just (c,_) ->
            c `seq` mkLexerErrorP ("Unknown character `" ++ [c] ++ "'") loc buf len
        Nothing -> throwError $ mkInternalError "unknownChar"

-- | Creates a Lexing error message
mkLexerErrorP :: String -> Action 
mkLexerErrorP msg loc buf len = 
    let tok = BSU.toString $ BSU.take (fromIntegral len) buf in
    throwError $ mkLexerError msg loc ("At token: " ++ tok)

-- | lexToken is called every time a new token must be read from the input 
lexToken :: P (Located Token)
lexToken = do
    inp@(AI loc1 buf) <- getInput
    sc <- getLexState
    case alexScan inp sc of
        AlexEOF -> do
            setLastToken loc1 ""
            if sc > 0
               then mkLexerErrorP "Unterminated comments" loc1 buf 0
               else return (L loc1 TEof)
        AlexError (AI loc2 buf2) ->
            mkLexerErrorP "Unknown" loc2 buf2 0
        AlexSkip inp2 _ -> do
            setInput inp2
            lexToken
        AlexToken inp2@(AI end _) len t -> do
            setInput inp2
            setLastToken loc1 (BSU.toString $ BSU.take (fromIntegral len) buf)
            t loc1 buf len

-- | Full lexer with continuation
lexer :: (Located Token -> P a) -> P a
lexer cont = do
  tok@(L _span _tok__) <- lexToken
  cont tok

-- | Dummy lexer for debugging
lexDummy :: P [(Located Token)]
lexDummy = do
    tok@(L _span t) <- lexToken
    if t == TEof
    then return [tok]
    else lexDummy >>= return . (tok:)

}
