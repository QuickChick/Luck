{-# LANGUAGE TupleSections #-}
module Core.IntRep where

import Data.List(intersperse)

import Control.Monad
import Control.Monad.Random

import Common.Util
import System.Random (Random, StdGen)

-- | Smarter representation for primitives, allowing for faster (in-/dis-)equalities

data Rep tt = Point tt 
            -- ^ A single point 
            | Range tt tt    
            -- ^ Range A B. A < B (strict)
            | Union [Rep tt] 
            -- ^ Union of non-overlapping, ordered, flattened, (>1) intervals
              deriving (Eq, Show)

printRep :: Show tt => Rep tt -> String
printRep (Point a) = show a
printRep (Range a b) = "[" ++ show a ++ ".." ++ show b ++ "]"
printRep (Union rs) = concat $ intersperse "-" $ map printRep rs

-- | Inject a single value into a representation
singleton :: tt -> Rep tt 
singleton = Point

-- | Inject a range of values into a representation. Assumes arg1 < arg2
range :: tt -> tt -> Rep tt 
range = Range

-- | Attempts to extract the value of a representation.
toSingleton :: Rep a -> Maybe a 
toSingleton (Point x) = Just x 
toSingleton _ = Nothing

-- | Intersection of two representations
intersect :: Ord a => Rep a -> Rep a -> Maybe (Rep a)
intersect (Point x) (Point y) | x == y    = Just $ Point x
                              | otherwise = Nothing
intersect (Point x) (Range low high) 
    | x < low || x > high = Nothing
    | otherwise           = Just $ Point x 
intersect (Range low high) (Point x)  
    | x < low || x > high = Nothing
    | otherwise           = Just $ Point x 
intersect r1@(Range l1 h1) r2@(Range l2 h2) 
    | r1 == r2  = Just r1
    | l' == h'  = Just $ Point l'
    | l' <  h'  = Just $ Range l' h'
    | otherwise = Nothing
    where l' = max l1 l2 
          h' = min h1 h2 
intersect p1@(Union cs) p2 
    | p1 == p2 = Just p1
    | otherwise = fromMaybeList $ map (intersect p2) cs
intersect p1 p2@(Union cs) 
    | p1 == p2 = Just p1
    | otherwise = fromMaybeList $ map (intersect p1) cs

-- | Refiner format of intersection
refineEQ :: (Ord a) => Rep a -> Rep a -> Maybe (Rep a, Rep a)
refineEQ = (fmap (join (,)) .) . intersect

-- | Gets a list of option representations and converts it to a representation
fromMaybeList :: [Maybe (Rep a)] -> Maybe (Rep a)
fromMaybeList [] = Nothing
fromMaybeList [x] = x 
fromMaybeList (Nothing:t) = fromMaybeList t
fromMaybeList ((Just h):t) = 
    case fromMaybeList t of 
      Just (Union lst) -> Just (Union (h:lst))
      Just x           -> Just (Union [h,x])
      Nothing          -> Just h

-- | Removes a single point from a representation
removePoint :: (Enum a, Ord a) => a -> Rep a -> Maybe (Rep a)
removePoint x o@(Point y) | x /= y    = Just o
                          | otherwise = Nothing
removePoint x o@(Range low high) 
    | x < low || x > high             = Just o
    | x == low  && high == succ low   = Just $ Point high
    | x == high && high == succ low   = Just $ Point low
    | x == low                        = Just $ Range (succ low) high
    | x == high                       = Just $ Range low (pred high)
    | x == succ low && x == pred high = Just $ Union [Point low, Point high]
    | x == succ low  = Just $ Union [Point low, Range (succ x) high]
    | x == pred high = Just $ Union [Range low (pred x), Point high]
    | otherwise      = Just $ Union [Range low (pred x), Range (succ x) high]
removePoint x (Union cs) = fromMaybeList $ map (removePoint x) cs

-- | Refine into an inequality
refineNE :: (Ord a, Enum a) => Rep a -> Rep a -> Maybe (Rep a, Rep a)
refineNE (Point x) o = fmap (Point x,) $ removePoint x o
refineNE o (Point x) = fmap (,Point x) $ removePoint x o
refineNE o1 o2 = Just (o1,o2)

-- | Remove everything less than a point
removeLT :: (Enum a, Ord a) => a -> Rep a -> Maybe (Rep a)
removeLT x o@(Point y) | x < y    = Just o
                            | otherwise = Nothing
removeLT x o@(Range low high) 
    | x < low        = Just o
    | succ x < high  = Just $ Range (succ x) high
    | x == pred high = Just $ Point high
    | x >= high      = Nothing
removeLT x (Union lst) = 
    fromMaybeList $ map (removeLT x) lst
removeLT _ _ = error "Can't refine Point LTE for non-point argument"

removeLE :: (Enum a, Ord a) => a -> Rep a -> Maybe (Rep a)
removeLE x o@(Point y) | x <= y    = Just o
                            | otherwise = Nothing
removeLE x o@(Range low high) 
    | x <= low  = Just o
    | x < high  = Just $ Range x high
    | x == high = Just $ Point high
    | x > high  = Nothing
removeLE x (Union lst) = 
    fromMaybeList $ map (removeLE x) lst
removeLE _ _ = error "Can't refine Point LE for non-point argument"

removeGT :: (Enum a, Ord a) => a -> Rep a -> Maybe (Rep a)
removeGT x o@(Point y) | x > y     = Just o
                            | otherwise = Nothing
removeGT x o@(Range low high) 
    | x > high      = Just o
    | pred x > low  = Just $ Range low (pred x)
    | pred x == low = Just $ Point low
    | x <= low      = Nothing
removeGT x (Union lst) = 
    fromMaybeList $ map (removeGT x) lst
removeGT _ _ = error "Can't refine GTE for non-point argument"

removeGE :: (Enum a, Ord a) => a -> Rep a -> Maybe (Rep a)
removeGE x o@(Point y) | x >= y    = Just o
                            | otherwise = Nothing
removeGE x o@(Range low high) 
    | x >= high = Just o
    | x > low   = Just $ Range low x
    | x == low  = Just $ Point low
    | x < low   = Nothing
removeGE x (Union lst) = 
    fromMaybeList $ map (removeGE x) lst
removeGE _ _ = error "Can't refine GE for non-point argument"

-- | Refiner versions of inequalities
refineGT :: (Enum a, Ord a) => Rep a -> Rep a -> Maybe (Rep a, Rep a)
refineGT p1 p2 = do 
  p1' <- removeLT l2 p1
  p2' <- removeGT h1 p2
  return $ (p1',p2')
      where h1 = getHighPartialPrim p1
            l2 = getLowPartialPrim p2

refineGE :: (Enum a, Ord a) => Rep a -> Rep a -> Maybe (Rep a, Rep a)
refineGE p1 p2 = do 
  p1' <- removeLE l2 p1
  p2' <- removeGE h1 p2
  return $ (p1',p2')
      where h1 = getHighPartialPrim p1
            l2 = getLowPartialPrim p2

refineLT :: (Enum a, Ord a) => Rep a -> Rep a -> Maybe (Rep a, Rep a)
refineLT p1 p2 = do 
  p1' <- removeGT h2 p1
  p2' <- removeLT l1 p2
  return $ (p1',p2')
      where l1 = getLowPartialPrim p1
            h2 = getHighPartialPrim p2

refineLE :: (Enum a, Ord a) => Rep a -> Rep a -> Maybe (Rep a, Rep a)
refineLE p1 p2 = do 
  p1' <- removeGE h2 p1
  p2' <- removeLE l1 p2
  return $ (p1',p2')
      where l1 = getLowPartialPrim p1
            h2 = getHighPartialPrim p2

-- | Lowest point of a representation
getLowPartialPrim :: Rep a -> a 
getLowPartialPrim (Point a) = a
getLowPartialPrim (Range low _) = low
getLowPartialPrim (Union (h:_)) = getLowPartialPrim h
getLowPartialPrim (Union _) = error "Empty union"

-- | Highest point of a representation
getHighPartialPrim :: Rep a -> a 
getHighPartialPrim (Point a) = a
getHighPartialPrim (Range _ high) = high
getHighPartialPrim (Union [h]) = getHighPartialPrim h
getHighPartialPrim (Union (_:t)) = getHighPartialPrim $ Union t
getHighPartialPrim (Union _) = error "Empty union"

-- | Pick a value in the representation domain
chooseStd :: Random a => StdGen -> Rep a -> (a, StdGen)
chooseStd g r = runRand (choose' r) g

choose' :: (MonadRandom m, Random a) => Rep a -> m a
choose' (Point i) = return i
choose' (Range low high) = getRandomR (low,high)
choose' (Union cs) = frequencyR' (map (1,) cs) >>= choose'

