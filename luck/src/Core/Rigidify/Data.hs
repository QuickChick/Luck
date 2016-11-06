{-# LANGUAGE LambdaCase #-}
module Core.Rigidify.Data (DataTree(..), convert, example) where

import Control.Monad.State
import Data.Data
import Data.Map (Map)
import qualified Data.Map as Map
import Common.Types
import Core.Rigidify.Generator (DataTree(..))
import Outer.Types (initOTcEnv)

-- | Convert the generic representation of terms to the represented value
-- in Haskell.
--
-- It is assumed that the input term is well-formed, and that the
-- datatype definitions in Haskell and in Luck are identical (in particular
-- data constructors should be declared in the same order).
convert :: (Data a, Ord c)
  => (c -> String) -- ^ Display the conflicting constructor in case of error.
  -- Useful for debugging, using the reverse mapping from Conversion.
  -> Map c ConIndex -- ^ Map from constructors to their indices
  -> DataTree c -> a
convert _ _ (DInt n) = res
  where res = fromConstr $ mkIntegralConstr (dataTypeOf res) n
convert showCon env (DCon c cargs) =
  if null residue
  then result
  else error' "Too many arguments."
  where
    ty = dataTypeOf result
    i = maybe (error $ "convert: Con not found " ++ showCon c) id
      $ Map.lookup c env
    c' = indexConstr ty i
    (result, residue) = flip runState cargs $ fromConstrM
      (StateT $ \case
        [] -> error' "Not enough arguments."
        arg : args -> return (convert showCon env arg, args))
      c'
    error' :: String -> x
    error' s = error $ "convert: " ++ s
                     ++ " Luck:" ++ showCon c
                     ++ " Hask:" ++ showConstr c'

example :: [Int]
example = convert id (conIndices initOTcEnv)
  $ DCon "Cons" [DInt 2015, DCon "Nil" []]

