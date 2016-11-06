{-# LANGUAGE FlexibleContexts #-}
module Common.Util where

import Common.Error

import System.Random
import System.Exit

import Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map

import Control.Monad.Except
import Control.Monad.Random
import Control.Arrow

-- import Debug.Trace

-- | Randomness, ala QC
frequencyR :: MonadRandom m => [(Int, m a)] -> m a
frequencyR [] = error "frequencyR used with empty list"
frequencyR freqs = join (frequencyR' freqs)

frequencyR' :: MonadRandom m => [(Int, a)] -> m a
frequencyR' [] = error "frequencyR' used with empty list"
frequencyR' freqs = getRandomR (1, tot) >>= (`pick` freqs)
  where
    tot = sum (map fst freqs)
    pick n ((k,x):xs)
        | n <= k    = return x
        | otherwise = pick (n-k) xs
    pick _ _ = error "internal error: frequencyR"

frequencyStd :: RandomGen g => g -> [(Int, a)] -> (a, g)
frequencyStd g freqs = runRand (frequencyR' freqs) g
{-
frequencyStd _g [] = error "frequencySTD used with empty list"
frequencyStd g freqs =
    let (num, g') = randomR (1, tot) g
    in (pick num freqs, g')
    
    where tot = sum (map fst freqs)
       
          pick n ((k,x):xs)
              | n <= k    = x
              | otherwise = pick (n-k) xs
          pick _ _  = error "internal error: frequencyR"
-}

freqRemoveStd :: RandomGen g => g -> [(Int, a)] -> ((a, [(Int,a)]), g)
freqRemoveStd _g [] = error "freqRemoveStd used with empty list"
freqRemoveStd g freqs =
    if tot == 0 -- Choose uniformly if all weights are 0
    then let (num, g') = randomR (0, length freqs - 1) g
             (a, (_, b) : c) = splitAt num freqs
      in ((b, a ++ c), g')
    else let (num, g') = randomR (1, tot) g
      in (pick num freqs, g')

 where tot = sum (map fst freqs)
       pick n ((k,x):xs)
           | n <= k    = (x,xs)
           | otherwise = second ((k,x):) $ pick (n-k) xs
       pick _ _ = error $ "internal error: freqRemoveStd " ++ show (tot, map fst freqs)

(!) :: (Show a, Ord a, Show b) => Map a b -> a -> b
m ! x = 
    case Map.lookup x m of 
      Just x' -> x'
      Nothing -> error $ "ti malakies kaneis : " ++ show (x, m)

-- | Converting maybe to an error
note :: MonadError Message m => Message -> Maybe a -> m a 
note s  Nothing  = throwError s
note _s (Just x) = return x

type Choice a = [(Int, a)]

choose :: MonadRandom m => Choice a -> m a
choose = frequencyR'

mapZip :: Ord tc => Map tc a -> Map tc b -> Map tc (a, b)
mapZip = Map.intersectionWith (,)
mapZip' :: Ord tc => Map tc (tvs, cs) -> Map tc alts -> Map tc (tvs, alts)
mapZip' = Map.intersectionWith ((,) . fst)

intSquareRoot n = last $ takeWhile (\x -> x * x <= n) [0 ..]

type Bimap a b = (Map a b, Map b a)

lookupL x m = Map.lookup x (fst m)
lookupR y m = Map.lookup y (snd m)

liftEither :: MonadError e m => Either e a -> m a
liftEither = either throwError return

failEither :: (Monad m, Show e) => Either e a -> m a
failEither = either (fail . show) return

randomize :: (MonadRandom m) => [(Int, a)] -> m [a]
randomize l = aux tot $ filter ((> 0) . fst) l 
  where tot = sum $ map fst l

        pick n ((k,x):xs)
            | n <= k    = ((k,x),xs)
            | otherwise = second ((k,x):) $ pick (n-k) xs
        pick n x = error $ "internal error: freqRemoveStd " ++ show (tot, n)

        aux _ [] = return []
        aux w l = do 
          n <- getRandomR (1, w) 
          let ((wx, x), xs) = pick n l
          (x:) <$> aux (w - wx) xs
