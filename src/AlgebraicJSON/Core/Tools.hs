-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

module AlgebraicJSON.Core.Tools where

import Data.Char
import qualified Data.Set as S

-- general tools

compareSortedListWith :: Ord b => (a -> b) -> [a] -> [a] -> ([(a, a)], [a], [a])
compareSortedListWith key xs ys = iter xs ys [] [] [] where
    iter xs ys both onlyXs onlyYs = case (xs, ys) of
        ((x:xs'), (y:ys')) ->
            if key x == key y then iter xs' ys' (both++[(x, y)]) onlyXs onlyYs
            else if key x < key y then iter xs' (y:ys') both (onlyXs++[x]) onlyYs
            else {- key x > key y -} iter (x:xs') ys' both onlyXs (onlyYs++[y])
        ([], ys) -> (both, onlyXs, onlyYs ++ ys)
        (xs, []) -> (both, onlyXs ++ xs, onlyYs)

setEq :: Ord a => [a] -> [a] -> Bool
setEq xs ys = S.fromList xs == S.fromList ys

isIdentifier :: String -> Bool
isIdentifier s = not (null s) && all isAlphaNum s

showIdentifier :: String -> String
showIdentifier s = if isIdentifier s then s else show s

mergeSorted :: Ord a => [a] -> [a] -> [a]
mergeSorted [] ys = ys
mergeSorted xs [] = xs
mergeSorted (x:xs) (y:ys) = if y < x then y : mergeSorted (x:xs) ys else x : mergeSorted xs (y:ys)

