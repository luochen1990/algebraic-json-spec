-- Copyright 2018 LuoChen (luochen1990@gmail.com). Licensed under the Apache License 2.0.

{-# language ScopedTypeVariables #-}
{-# language MonadComprehensions #-}
{-# language TupleSections #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List
import Data.Fix
import Data.Maybe (mapMaybe)
import Control.Exception
import Test.Hspec hiding (Spec, example)
import Test.Hspec.QuickCheck
import Test.QuickCheck
import AlgebraicJSON
import AlgebraicJSON.EDSL

isRight :: Either a b -> Bool
isRight e = either (const False) (const True) e

isMatched :: MatchResult -> Bool
isMatched r = case r of Matched -> True; _ -> False

matchSpec'' = matchSpec M.empty

arbId, arbId' :: Gen String
arbId = elements ["a", "b", "c", "d", "e"]
arbId' = arbId >>= \s -> pure ('_':s)

arbNat :: Gen Int
arbNat = elements [0, 1, 2]

arbNatSized :: Int -> Gen Int
arbNatSized n = resize n arbitrarySizedNatural

arbSet :: Eq a => Int -> Gen a -> Gen [a]
arbSet n k = vectorOf n k >>= pure . nub

arbMap :: Eq a => Int -> Gen a -> Gen b -> Gen [(a, b)]
arbMap n k v = [zip ks vs | ks <- arbSet n k, vs <- vectorOf (length ks) v]

instance Arbitrary Strictness where
  arbitrary = elements [Strict, Tolerant]

instance Arbitrary Spec where
  arbitrary = sized tree' where
    tree' 0 = oneof [
      elements (map Fix [Anything, Number, Text, Boolean, Null]),
      Fix <$> (ConstNumber <$> arbitrary), Fix <$> (ConstText <$> arbId), Fix <$> (ConstBoolean <$> arbitrary)]
    tree' n | n > 0 = oneof [
      tree' 0,
      Fix <$> (Tuple <$> arbitrary <*> (arbNat >>= \m -> vectorOf m (tree' ((n-1) `div` m)))),
      Fix <$> (Array <$> (tree' (n-1))),
      Fix <$> (NamedTuple <$> arbitrary <*> (arbNat >>= \m -> arbMap m arbId (tree' ((n-1) `div` m)))),
      Fix <$> (TextMap <$> (tree' (n-1))),
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

toSpec :: CSpec -> Spec
toSpec (Fix tr) = Fix $ quadmap id id (const ()) toSpec tr

instance Arbitrary CSpec where
  arbitrary = arbitrary `suchThatMap` (\sp -> either (const Nothing) Just $ checkSpec M.empty sp)
  shrink csp = let sp' = toSpec csp in mapMaybe (\t -> either (const Nothing) Just (checkSpec M.empty t)) (shrink sp')

instance Arbitrary JsonData where
  arbitrary = sized tree' where
    tree' 0 = oneof [
      JsonNumber <$> arbitrary,
      JsonText <$> arbId,
      JsonBoolean <$> arbitrary,
      pure JsonNull]
    tree' n | n > 0 = oneof [
      tree' 0,
      JsonArray <$> (arbNat >>= \m -> vectorOf m (tree' ((n-1) `div` m))),
      JsonObject <$> (arbNat >>= \m -> arbMap m arbId (tree' ((n-1) `div` m)))]
  shrink d = case d of
    JsonArray xs -> xs ++ [JsonArray xs' | xs' <- shrink xs]
    JsonObject ps -> map snd ps ++ [JsonObject ps' | ps' <- shrink ps]
    JsonNumber x -> JsonNull : [JsonNumber 1 | x /= 1]
    JsonText s -> JsonNull : [JsonText "a" | s /= "a"]
    JsonNull -> []
    _ -> [JsonNull]

mergeSorted :: Ord a => [a] -> [a] -> [a]
mergeSorted [] ys = ys
mergeSorted xs [] = xs
mergeSorted (x:xs) (y:ys) = if y < x then y : mergeSorted (x:xs) ys else x : mergeSorted xs (y:ys)

(<?>) :: (Testable p) => p -> String -> Property
(<?>) = flip (Test.QuickCheck.counterexample . ("Extra Info: " ++))
infixl 2 <?>

matchedData :: CSpec -> Gen JsonData
--matchedData t = arbitrary `suchThat` (matchSpec' M.empty t)
matchedData spec@(Fix tr) = sized (tree' tr) where
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
      let ts' = (reverse . dropWhile (matchNull . toShape M.empty) . reverse) ts; (l, l') = (length ts, length ts')
      in arbNatSized (l - l' + 1) >>= \n ->
        let ts'' = take (l' + n) (ts ++ repeat (Fix Anything)) in matchedData (Fix $ Tuple Strict ts'')
    Array (Fix t) -> arbNat >>= \m -> JsonArray <$> vectorOf m (tree' t ((n-1) `div` m))
    NamedTuple Strict ps -> JsonObject <$> sequence [(k,) <$> tree' t ((n-1) `div` length ps) | (k, (Fix t)) <- ps]
    NamedTuple Tolerant ps -> sequence [arbNatSized 1, arbNatSized 1, arbNatSized 3] >>= \[n1, n2, sz1] ->
      arbMap n1 arbId' (resize sz1 arbitrary) >>= \ps1_ ->
        let (ps2, ps1) = partition (matchNull . toShape M.empty . snd) ps
            ps1' = ps1 ++ ps1_
            ps2' = drop n2 ps2
        in matchedData (Fix $ NamedTuple Strict (ps1' ++ ps2'))
    TextMap (Fix t) -> arbNat >>= \m -> JsonObject <$> arbMap m arbId (tree' t ((n-1) `div` m))
    Refined (Fix t) p -> tree' t (n-1) `suchThat` testProp p
    Ref name -> error "matchedData should not be used on Ref"
    Alternative (Fix a) (Fix b) _ -> oneof [tree' a n, tree' b n]

main :: IO ()
main = hspec $ do
  describe "compareSortedListWith" $ do
    prop "correct" $
      \(ori_xs :: [Int]) (ori_ys :: [Int]) ->
        let (xs, ys) = (sort ori_xs, sort ori_ys)
            (both, onlyL, onlyR) = compareSortedListWith id xs ys
            (bothL, bothR) = unzip both
        in
          mergeSorted bothL onlyL === xs .&&. mergeSorted bothR onlyR === ys .&&.
          (case (compareSortedListWith id onlyL onlyR) of (both', _, _) -> both' === []) .&&.
          (case (compareSortedListWith id bothL bothR) of (both', _, _) -> both' === both)

  describe "AlgebraicJSON" $ do
    prop "example-matchSpec" $
      \(sp :: Spec) ->
        let rst = tryMatchSpec M.empty sp (example (toShape M.empty sp))
        in isRight rst ==> case rst of Right r -> r === Matched

    prop "matchSpec-Or-commutative" $
      \(sp1 :: Spec) (sp2 :: Spec) (d :: JsonData) ->
        let rst = (,) <$> checkSpec M.empty (sp1 <|||> sp2) <*> checkSpec M.empty (sp2 <|||> sp1)
        in isRight rst ==> case rst of Right (or1, or2) -> (let r1 = matchSpec'' or1 d; r2 = matchSpec'' or2 d in collect (r1 == Matched) $ r1 === r2)

    prop "checkSpec-Or-commutative" $
      \(sp1 :: Spec) (sp2 :: Spec) (d :: JsonData) ->
        let rst1 = checkSpec M.empty (sp1 <|||> sp2)
            rst2 = checkSpec M.empty (sp2 <|||> sp1)
        in isRight rst1 === isRight rst2

    prop "checkSpec-overlapping-evidence-correct" $
      \(sp1 :: Spec) (sp2 :: Spec) ->
        let rst = checkSpec M.empty (sp1 <|||> sp2)
        in not (isRight rst) ==> case rst of
          Left (ExistOverlappingOr sp1' sp2' evi) ->
            (matchSpec'' sp1' evi === Matched .&&. matchSpec'' sp2' evi === Matched) <?> show (sp1', sp2', evi)
          _ -> label "not ExistOverlappingOr" True

    prop "matchSpec- Or a b >= a" $
      \(sp1 :: Spec) (sp2 :: Spec) (d :: JsonData) ->
        let rst = checkSpec M.empty (sp1 <|||> sp2)
        in isRight rst ==> case rst of
          Right or1@(Fix (Alternative sp1' sp2' _)) -> matchSpec'' sp1' d == Matched ==> matchSpec'' or1 d === Matched

    prop "matchSpec-Tolerant-Tuple-accept-redurant-null" $
      \(sps :: [Spec]) (ds :: [JsonData]) ->
        let rst = checkSpec M.empty (Fix $ Tuple Tolerant sps)
        in isRight rst ==> case rst of
          Right sp ->
            let d1 = JsonArray ds
                d2 = JsonArray (ds ++ [JsonNull])
            in matchSpec'' sp d1 == Matched ==> matchSpec'' sp d2 === Matched <?> show (sp, d1, d2)

    prop "matchedData-do-matchSpec" $
      \(sp :: CSpec) ->
        forAll (matchedData sp) $ \d ->
          matchSpec'' sp d === Matched

    prop "matchSpec-Tolerant-Tuple-accept-lacking-null" $
      \(sp1 :: CSpec) ->
        (matchNull . toShape M.empty) sp1 ==>
          forAll arbNat $ \n ->
            forAll (vectorOf n arbitrary) $ \sps ->
              forAll (matchedData (Fix $ Tuple Strict sps)) $ \d ->
                let sp = (Fix $ Tuple Tolerant (sps ++ [sp1])) in matchSpec'' sp d === Matched <?> show sp

    it "works with some simple cases" $ do
      show (checkSpec env (number <|||> text)) `shouldBe` "Right (Number | Text)"
      show (checkSpec env ((number <|||> text) <|||> (ctext "abc"))) `shouldBe` "Left (ExistOverlappingOr (Number | Text) \"abc\" \"abc\")"
      show (checkSpec env ((number <|||> text) <|||> case1)) `shouldBe` "Right ((Number | Text) | (\"Lit\", Number))"
      show (checkSpec env ((number <|||> text) <|||> case2)) `shouldBe` "Right ((Number | Text) | (\"Add\", AST, AST))"
      show (checkSpec env ((number <|||> text) <|||> ast)) `shouldBe` "Right ((Number | Text) | ((\"Lit\", Number) | (\"Add\", AST, AST)))"
      show (checkSpec env ((number <|||> text) <|||> case1')) `shouldBe` "Right ((Number | Text) | (\"Lit\", 1.0))"
      show (checkSpec env ((number <|||> text) <|||> (case1 <|||> case1'))) `shouldBe` "Left (ExistOverlappingOr (\"Lit\", Number) (\"Lit\", 1.0) [\"Lit\", 1.0])"
      show (toShape env ast) `shouldBe` "((\"Lit\", Number) |? (\"Add\", ((\"Lit\", Number) |? (\"Add\", Anything, Anything)), ((\"Lit\", Number) |? (\"Add\", Anything, Anything))))"
      show (checkSpec env (spec1 <|||> spec2)) `shouldBe` "Right ({x: Number, y: Number, *} | {z: Number, x: Text, *})"
      show (checkSpec env (spec1 <|||> spec2')) `shouldBe` "Left (ExistOverlappingOr {x: Number, y: Number, *} {z: Number, x: Number, *} {x: 0.0, y: 0.0, z: 0.0})"
      show (checkSpec env (spec1 <|||> spec2')) `shouldBe` "Left (ExistOverlappingOr {x: Number, y: Number, *} {z: Number, x: Number, *} {x: 0.0, y: 0.0, z: 0.0})"
      show (tryMatchSpec env ast dat1) `shouldBe` "Right Matched"
      show (tryMatchSpec env ast dat2) `shouldBe` "Right (UnMatched (StepCause OrNotMatchLeft (StepCause (TupleFieldNotMatch 1) (DirectCause OutlineNotMatch Number \"1\"))))"
      show (tryMatchSpec env spec3 data3) `shouldBe` "Right (UnMatched (StepCause (NamedTupleFieldNotMatch \"y\") (StepCause (NamedTupleFieldNotMatch \"w\") (DirectCause OutlineNotMatch Number \"3\"))))"
      show (tryMatchSpec env spec4 data4) `shouldBe` "Right (UnMatched (StepCause OrNotMatchLeft (StepCause (NamedTupleFieldNotMatch \"y\") (StepCause (NamedTupleFieldNotMatch \"w\") (DirectCause OutlineNotMatch Number \"3\")))))"

-- test data

ast = case1 <|||> case2
case1 = tuple [ctext "Lit", number]
case1' = (tuple [ctext "Lit", cnumber 1])
case2 = (tuple [ctext "Add", ref "AST", ref "AST"])

env = M.fromList [("AST", ast)]
dat1 = JsonArray [JsonText "Lit", JsonNumber 1]
dat2 = JsonArray [JsonText "Lit", JsonText "1"]

spec1 = object' [("x", number), ("y", number)]
spec2 = object' [("z", number), ("x", text)]
spec2' = object' [("z", number), ("x", number)]

spec3 = object' [("x", number), ("y", object' [("z", number), ("w", number)])]
data3 = JsonObject [("x", JsonNumber 1), ("y", JsonObject [("z", JsonNumber 2), ("w", JsonText "3")])]

spec4 = spec3 <|||> (object' [("x", text), ("y", number)])
data4 = JsonObject [("x", JsonNumber 1), ("y", JsonObject [("z", JsonNumber 2), ("w", JsonText "3")])]

