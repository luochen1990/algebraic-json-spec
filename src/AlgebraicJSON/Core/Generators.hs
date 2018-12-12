-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

{-# language MonadComprehensions #-}
{-# language TupleSections #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}

module AlgebraicJSON.Core.Generators where

import qualified Data.Map as M
import Data.List
import Data.Fix
import Data.Maybe (mapMaybe)
import Test.QuickCheck
import AlgebraicJSON.Core.Definitions
import AlgebraicJSON.Core.Functions (checkSpec)

arbKey, arbKey' :: Gen String
arbKey = elements ["a", "b", "c", "d", "e"]
arbKey' = arbKey >>= \s -> pure ('_':s)

arbNat :: Gen Int
arbNat = elements [0, 1, 2]

arbNatSized :: Int -> Gen Int
arbNatSized n = resize n arbitrarySizedNatural

arbSet :: Eq a => Int -> Gen a -> Gen [a]
arbSet n k = vectorOf n k >>= pure . nub

arbMap :: Eq a => Int -> Gen a -> Gen b -> Gen [(a, b)]
arbMap n k v = [zip ks vs | ks <- arbSet n k, vs <- vectorOf (length ks) v]

instance Arbitrary JsonData where
  arbitrary = sized tree' where
    tree' 0 = oneof [
      JsonNumber <$> arbitrary,
      JsonText <$> arbKey,
      JsonBoolean <$> arbitrary,
      pure JsonNull]
    tree' n | n > 0 = oneof [
      tree' 0,
      JsonArray <$> (arbNat >>= \m -> vectorOf m (tree' ((n-1) `div` m))),
      JsonObject <$> (arbNat >>= \m -> arbMap m arbKey (tree' ((n-1) `div` m)))]
  shrink d = case d of
    JsonArray xs -> xs ++ [JsonArray xs' | xs' <- shrink xs]
    JsonObject ps -> map snd ps ++ [JsonObject ps' | ps' <- shrink ps]
    JsonNumber x -> JsonNull : [JsonNumber 1 | x /= 1]
    JsonText s -> JsonNull : [JsonText "a" | s /= "a"]
    JsonNull -> []
    _ -> [JsonNull]

instance CoArbitrary JsonData where
  coarbitrary d = case d of
    JsonNumber x -> variant 0 . coarbitrary x
    JsonText s -> variant 1 . coarbitrary s
    JsonBoolean b -> variant 2 . coarbitrary b
    JsonNull -> variant 3
    JsonArray xs -> variant 4 . coarbitrary xs
    JsonObject ps -> variant 5 . coarbitrary ps

instance Arbitrary Strictness where
  arbitrary = elements [Strict, Tolerant]

instance Arbitrary DecProp where
  arbitrary = DecProp <$> arbitrary

instance Arbitrary Spec where
  arbitrary = sized tree' where
    tree' 0 = oneof [
      elements (map Fix [Anything, Number, Text, Boolean, Null]),
      Fix <$> (ConstNumber <$> arbitrary), Fix <$> (ConstText <$> arbKey), Fix <$> (ConstBoolean <$> arbitrary)]
    tree' n | n > 0 = oneof [
      tree' 0,
      Fix <$> (Tuple <$> arbitrary <*> (arbNat >>= \m -> vectorOf m (tree' ((n-1) `div` m)))),
      Fix <$> (Array <$> (tree' (n-1))),
      Fix <$> (NamedTuple <$> arbitrary <*> (arbNat >>= \m -> arbMap m arbKey (tree' ((n-1) `div` m)))),
      Fix <$> (TextMap <$> (tree' (n-1))),
      Fix <$> (arbNatSized (n-1) >>= \k -> (Refined <$> (tree' (n-1-k)) <*> resize k arbitrary)),
      Fix <$> (Alternative <$> tree' ((n-1) `div` 2) <*> tree' ((n-1) `div` 2) <*> pure ())]
  shrink (Fix tr) = case tr of
    Tuple s ts -> Fix Null : ts ++ [Fix $ Tuple s ts' | ts' <- shrinkList shrink ts] ++ [Fix $ Tuple Strict ts | s == Tolerant]
    Array t -> Fix Null : t : [Fix $ Array t' | t' <- shrink t]
    NamedTuple s ps -> Fix Null : map snd ps ++ [Fix $ NamedTuple s ps' | ps' <- shrinkList shrink ps] ++ [Fix $ NamedTuple Strict ps | s == Tolerant]
    TextMap t -> Fix Null : t : [Fix $ TextMap t' | t' <- shrink t]
    Refined t p -> Fix Null : t : [Fix $ Refined t' p | t' <- shrink t]
    Alternative t1 t2 _ -> Fix Null : [t1, t2] ++ [Fix $ Alternative t1' t2' () | (t1', t2') <- shrink (t1, t2)]
    ConstNumber x -> Fix Null : [Fix $ ConstNumber 1 | x /= 1]
    ConstText s -> Fix Null : [Fix $ ConstText "a" | s /= "a"]
    Null -> []
    _ -> [Fix Null]

instance Arbitrary CSpec where
  arbitrary = arbitrary `suchThatMap` (\sp -> either (const Nothing) Just $ checkSpec M.empty sp)
  shrink csp = let sp' = toSpec csp in mapMaybe (\t -> either (const Nothing) Just (checkSpec M.empty t)) (shrink sp')

-- | similar things to arbitrary in Haskell
arbitraryJ :: CSpec -> Gen JsonData
--arbitraryJ t = arbitrary `suchThat` (matchSpec' M.empty t)
arbitraryJ spec@(Fix tr) = sized (tree' tr) where
  tree' :: TyRep Name DecProp ChoiceMaker CSpec -> Int -> Gen JsonData
  tree' tr = \n -> case tr of
    Anything -> resize n arbitrary
    Number -> JsonNumber <$> arbitrary
    Text -> JsonText <$> arbitrary
    Boolean -> JsonBoolean <$> arbitrary
    Null -> pure $ JsonNull
    ConstNumber m -> pure $ JsonNumber m
    ConstText s -> pure $ JsonText s
    ConstBoolean b -> pure $ JsonBoolean b
    Tuple Strict ts -> JsonArray <$> sequence (map (\(Fix t) -> tree' t ((n-1) `div` (length ts))) ts)
    Tuple Tolerant ts ->
      let ts' = (reverse . dropWhile (acceptNull . toShape M.empty) . reverse) ts; (l, l') = (length ts, length ts')
      in arbNatSized (l - l' + 1) >>= \n ->
        let ts'' = take (l' + n) (ts ++ repeat (Fix Anything)) in arbitraryJ (Fix $ Tuple Strict ts'')
    Array (Fix t) -> arbNat >>= \m -> JsonArray <$> vectorOf m (tree' t ((n-1) `div` m))
    NamedTuple Strict ps -> JsonObject <$> sequence [(k,) <$> tree' t ((n-1) `div` length ps) | (k, (Fix t)) <- ps]
    NamedTuple Tolerant ps -> sequence [arbNatSized 1, arbNatSized 1, arbNatSized 3] >>= \[n1, n2, sz1] ->
      arbMap n1 arbKey' (resize sz1 arbitrary) >>= \ps1_ ->
        let (ps2, ps1) = partition (acceptNull . toShape M.empty . snd) ps
            ps1' = ps1 ++ ps1_
            ps2' = drop n2 ps2
        in arbitraryJ (Fix $ NamedTuple Strict (ps1' ++ ps2'))
    TextMap (Fix t) -> arbNat >>= \m -> JsonObject <$> arbMap m arbKey (tree' t ((n-1) `div` m))
    Refined (Fix t) p -> tree' t (n-1) `suchThat` testProp p
    Ref name -> error "arbitraryJ should not be used on Ref"
    Alternative (Fix a) (Fix b) _ -> oneof [tree' a n, tree' b n]

