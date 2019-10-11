-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

{-# language MonadComprehensions #-}
{-# language TupleSections #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}

module JsonSpec.Core.Generators where

import qualified Data.Map as M
import Data.List
import Data.Fix
import Data.Maybe (mapMaybe)
import Test.QuickCheck
import JsonSpec.Core.Definitions
import JsonSpec.Core.Functions

arbKey, arbKey' :: Gen String
arbKey = elements ["a", "b", "c", "d", "e"]
arbKey' = arbKey >>= \s -> pure ('_':s)

arbNat :: Gen Int
arbNat = elements [0, 1, 2]

arbNatSized :: Int -> Gen Int
arbNatSized n = resize n arbitrarySizedNatural

arbSet :: Ord a => Int -> Gen a -> Gen [a]
arbSet n k = vectorOf n k >>= pure . nub . sort

arbMap :: Ord a => Int -> Gen a -> Gen b -> Gen [(a, b)]
arbMap n k v = [zip ks vs | ks <- arbSet n k, vs <- vectorOf (length ks) v]

shrinkSnd :: Arbitrary b => (a, b) -> [(a, b)]
shrinkSnd (x, y) = [(x, y') | y' <- shrink y]

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
    JsonObject ps -> map snd ps ++ [JsonObject ps' | ps' <- shrinkList shrinkSnd ps]
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

-- | generate DecProp along a Spec,
--   the generated DecProp p satisfy `exists (d : JsonData), testProp p d == True`,
--   so that arbitraryJ can generate a value for Refined node successfully.
arbPropAbout :: Spec -> Gen DecProp
arbPropAbout spec = sized (arb' spec) where
  arb' (Fix tr) n | n >= 0 = case tr of
    Anything -> elements [(Lit (JsonBoolean True)), (Ifx It NeOp (Lit JsonNull))]
    Number -> pure (Ifx It LtOp (Lit (JsonNumber 42)))
    Text -> pure (Ifx (Pfx LenOp It) LtOp (Lit (JsonNumber 42)))
    Boolean -> elements [(Lit (JsonBoolean True)), (Ifx It NeOp (Lit (JsonBoolean True))), (Ifx It NeOp (Lit (JsonBoolean False)))]
    Null -> pure (Lit (JsonBoolean True))
    ConstNumber m -> pure (Lit (JsonBoolean True))
    ConstText s -> pure (Lit (JsonBoolean True))
    ConstBoolean b -> pure (Lit (JsonBoolean True))
    Tuple _ ts -> if null ts then pure (Lit (JsonBoolean True)) else do
      (i, t) <- elements (zip [0..] ts)
      p <- arb' t (max 0 (n-1))
      pure (injectExpr (Idx It i) p)
    Array t -> pure (Ifx (Pfx LenOp It) LtOp (Lit (JsonNumber 42)))
    Object _ ps -> if null ps then pure (Lit (JsonBoolean True)) else do
      (k, t) <- elements ps
      p <- arb' t (max 0 (n-1))
      pure (injectExpr (Dot It k) p)
    Dict t -> pure (Ifx (Pfx LenOp It) LtOp (Lit (JsonNumber 42)))
    Refined t _ -> pure (Lit (JsonBoolean True))
    Ref name -> pure (Lit (JsonBoolean True))
    Or t1 t2 _ -> pure (Lit (JsonBoolean True))

instance Arbitrary Spec where
  arbitrary = sized tree' where
    tree' 0 = oneof [
      elements (map Fix [Anything, Number, Text, Boolean, Null]),
      Fix <$> (ConstNumber <$> arbitrary), Fix <$> (ConstText <$> arbKey), Fix <$> (ConstBoolean <$> arbitrary)]
    tree' n | n > 0 = oneof [
      tree' 0,
      Fix <$> (Tuple <$> arbitrary <*> (arbNat >>= \m -> vectorOf m (tree' ((n-1) `div` m)))),
      Fix <$> (Array <$> (tree' (n-1))),
      Fix <$> (Object <$> arbitrary <*> (arbNat >>= \m -> arbMap m arbKey (tree' ((n-1) `div` m)))),
      Fix <$> (Dict <$> (tree' (n-1))),
      Fix <$> (do
        k <- arbNatSized (n-1)
        sp <- tree' (n-1-k)
        p <- resize k (arbPropAbout sp)
        pure (Refined sp p)),
      Fix <$> (Or <$> tree' ((n-1) `div` 2) <*> tree' ((n-1) `div` 2) <*> pure ())]
  shrink (Fix tr) = case tr of
    Tuple s ts -> Fix Null : ts ++ [Fix $ Tuple s ts' | ts' <- shrinkList shrink ts] ++ [Fix $ Tuple Strict ts | s == Tolerant]
    Array t -> Fix Null : t : [Fix $ Array t' | t' <- shrink t]
    Object s ps -> Fix Null : map snd ps ++ [Fix $ Object s ps' | ps' <- shrinkList shrinkSnd ps] ++ [Fix $ Object Strict ps | s == Tolerant]
    Dict t -> Fix Null : t : [Fix $ Dict t' | t' <- shrink t]
    Refined t p -> Fix Null : t : [Fix $ Refined t' (Lit (JsonBoolean True)) | t' <- [t | p /= (Lit (JsonBoolean True))] ++ shrink t]
    Or t1 t2 _ -> Fix Null : [t1, t2] ++ [Fix $ Or t1' t2' () | (t1', t2') <- shrink (t1, t2)]
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
  tree' tr = \n -> if n < 0 then error ("arbitraryJ: negative size " ++ show n) else case tr of
    Anything -> resize n arbitrary
    Number -> JsonNumber <$> arbitrary
    Text -> JsonText <$> resize n arbitrary
    Boolean -> JsonBoolean <$> arbitrary
    Null -> pure $ JsonNull
    ConstNumber m -> pure $ JsonNumber m
    ConstText s -> pure $ JsonText s
    ConstBoolean b -> pure $ JsonBoolean b
    Tuple Strict ts -> let m = length ts in JsonArray <$> sequence (map (\(Fix t) -> tree' t (max 0 (n-m-1) `div` m)) ts)
    Tuple Tolerant ts ->
      let ts' = (reverse . dropWhile (\t -> matchSpec M.empty t JsonNull == Matched) . reverse) ts; (l, l') = (length ts, length ts')
      in elements (nub [l, l', l'+1, l+1]) >>= \m ->
        let ts'' = take m (ts ++ repeat (Fix Anything)) in tree' (Tuple Strict ts'') (max 0 (n-1))
    Array (Fix t) -> arbNatSized (min 3 n) >>= \m -> JsonArray <$> vectorOf m (tree' t (max 0 (n-m-1) `div` m))
    Object Strict ps -> let m = length ps in JsonObject <$> sequence [(k,) <$> tree' t (max 0 (n-m-1) `div` m) | (k, (Fix t)) <- ps]
    Object Tolerant ps -> sequence [arbNatSized (min 1 n), arbNatSized 1] >>= \[n1, n2] ->
      arbMap n1 arbKey' (pure $ Fix Anything) >>= \ps1_ ->
        let (ps2, ps1) = partition (\(_, t) -> matchSpec M.empty t JsonNull == Matched) ps
            ps1' = ps1 ++ ps1_
            ps2' = drop n2 ps2
        in tree' (Object Strict (ps1' ++ ps2')) (max 0 (n-1-n1))
    Dict (Fix t) -> arbNatSized (min 3 n) >>= \m -> JsonObject <$> arbMap m arbKey (tree' t (max 0 (n-m-1) `div` m))
    Refined (Fix t) p -> tree' t (max 0 (n-1)) `suchThat` testProp p
    Ref name -> error "arbitraryJ should not be used on Ref"
    Or (Fix a) (Fix b) _ -> oneof [tree' a n, tree' b n]

sampleJ :: Spec -> IO ()
sampleJ sp = sample (arbitraryJ (either undefined id (checkSpec M.empty sp)))

