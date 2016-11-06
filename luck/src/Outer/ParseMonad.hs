{-# LANGUAGE RecordWildCards #-} 
module Outer.ParseMonad where

import Common.Error
import Common.SrcLoc

import Data.Char
import Data.Word (Word8)
import qualified Data.ByteString as BS

import Control.Monad.State

-- | Parser State 
data PState = PState {
    _buffer          :: BS.ByteString,
    _last_loc        :: SrcLoc, -- pos of previous token
    _last_tok        :: !String, -- string of the previous token
    _cur_loc         :: SrcLoc,  -- current loc (end of token + 1)
    _lex_state       :: !Int,
    _comment_state   :: !Int
  }

-- | Create an initial Parser State 
mkPState :: BS.ByteString -> SrcLoc -> PState
mkPState buf loc =
  PState {
    _buffer          = buf,
    _last_loc        = loc,
    _last_tok        = "",
    _cur_loc         = loc,
    _lex_state       = 0,
    _comment_state   = 0
  }

-- | Parsing Monad 
type P a = StateT PState (Either Message) a

runP :: P a -> PState -> Either Message a
runP = evalStateT

-- | Input for Alex interop
data AlexInput = AI SrcLoc BS.ByteString   
                   -- ^ current position & current input string

-- | Get the current (located) input of the parser
getInput :: P AlexInput
getInput = do 
  PState{..} <- get 
  return $ AI _cur_loc _buffer 

-- | Set the input of the parser
setInput :: AlexInput -> P ()
setInput (AI loc buf) = modify $ \s -> s{_cur_loc = loc
                                        ,_buffer  = buf}

-- | Get the current lexing state
getLexState :: P Int
getLexState = get >>= return . _lex_state 

-- | Set the current lexing state
setLexState :: Int -> P ()
setLexState new_state = modify $ \s -> s{_lex_state = new_state}

-- | Get the current source location
getSrcLoc :: P SrcLoc
getSrcLoc = get >>= return . _cur_loc 

-- | Set the current source location
setSrcLoc :: SrcLoc -> P ()
setSrcLoc new_loc = modify $ \s -> s{_cur_loc = new_loc}

-- | Set the last token of the parser state
setLastToken :: SrcLoc -> String -> P ()
setLastToken loc str = 
  modify $ \s -> s {_last_loc = loc
                   ,_last_tok = str}

-- | Increase comment state (for nesting)
incCommState :: P ()
incCommState = modify $ \ s-> s{_comment_state = _comment_state s + 1}

-- | Decrease comment state (ends nesting)
decCommState :: P ()
decCommState = modify $ \s -> s{_comment_state = _comment_state s - 1}

-- | Get current comment state
getCommState :: P Int
getCommState = get >>= return . _comment_state 

-- | TODO: implement if needed
alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar _ = error "alexInputPrevChar not implemented"

-- | Get the next byte from the input.
alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte (AI loc buf)
    | BS.null buf  = Nothing
    | otherwise =
        let w    = BS.head buf
            buf' = BS.tail buf
            loc' = advanceSrcLoc loc w
        in w `seq` loc' `seq` Just (w, AI loc' buf')

-- | Alex 2.x compatibility
alexGetChar :: AlexInput -> Maybe (Char, AlexInput)
alexGetChar i =
    case alexGetByte i of
        Nothing     -> Nothing
        Just (b,i') ->
            if b<0x80
                then
                    Just (chr (fromIntegral b), i')
                else
                    undefined

