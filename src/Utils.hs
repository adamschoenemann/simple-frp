{-|
Module      : Utils
Description : Utility functions

-}
module Utils where

import Data.Map (Map)
import qualified Data.Map.Strict as M

-- |Unsafely lookup a value in a map by key
unsafeLookup :: (Show k, Show v, Ord k) => k -> Map k v -> v
unsafeLookup k m =
  case M.lookup k m of
    Nothing -> error $ "unsafeLookup on key " ++ show k ++ " in map " ++ show m
    Just x  -> x

-- |Safely get the last value of a list
safeLast :: [a] -> Maybe a
safeLast [] = Nothing
safeLast [x] = Just x
safeLast (x : xs) = safeLast xs