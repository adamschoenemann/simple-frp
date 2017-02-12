
module Utils where

import Data.Char (toUpper, toLower, isSpace)
import Data.Functor ((<$>))
import Data.Map (Map)
import qualified Data.Map.Strict as M

unsafeLookup :: (Show k, Show v, Ord k) => k -> Map k v -> v
unsafeLookup k m =
  case M.lookup k m of
    Nothing -> error $ "unsafeLookup on key " ++ show k ++ " in map " ++ show m
    Just x  -> x

uncons :: [a] -> Maybe (a, [a])
uncons [] = Nothing
uncons (x:xs) = Just (x,xs)

capitalize :: String -> String
capitalize s = maybe "" id $ (\(x,xs) -> toUpper x : xs) <$> uncons s

uncapitalize :: String -> String
uncapitalize s = maybe "" id $ (\(x,xs) -> toLower x : xs) <$> uncons s

trimHead :: String -> String
trimHead = dropWhile isSpace