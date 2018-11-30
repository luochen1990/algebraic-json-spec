-- Copyright 2018 LuoChen (luochen1990@gmail.com). Licensed under the Apache License 2.0.

{-# language ScopedTypeVariables #-}
{-# language MonadComprehensions #-}
{-# language TupleSections #-}

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List
import Control.Exception
import Test.Hspec hiding (Spec, example)
import Test.Hspec.QuickCheck
import Test.QuickCheck
import AlgebraicJSON

isRight :: Either a b -> Bool
isRight e = either (const False) (const True) e

isMatched :: MatchResult -> Bool
isMatched r = case r of Matched -> True; _ -> False

matchSpec'' = matchSpec M.empty

arbId :: Gen String
arbId = elements ["a", "b", "c", "d", "e"]

arbNat :: Gen Int
arbNat = elements [0, 1, 2]

arbSet :: Eq a => Int -> Gen a -> Gen [a]
arbSet n k = vectorOf n k >>= pure . nub

arbMap :: Eq a => Int -> Gen a -> Gen b -> Gen [(a, b)]
arbMap n k v = [zip ks vs | ks <- arbSet n k, vs <- vectorOf (length ks) v]

instance Arbitrary Strictness where
  arbitrary = elements [Strict, Tolerant]

instance Arbitrary TypeRep where
  arbitrary = sized tree' where
    tree' 0 = oneof [
      elements [Anything, Number, Text, Boolean, Null],
      ConstNumber <$> arbitrary, ConstText <$> arbId, ConstBoolean <$> arbitrary]
    tree' n | n > 0 = oneof [
      tree' 0,
      Tuple <$> arbitrary <*> (arbNat >>= \m -> vectorOf m (tree' ((n-1) `div` m))),
      Array <$> (tree' (n-1)),
      NamedTuple <$> arbitrary <*> (arbNat >>= \m -> arbMap m arbId (tree' ((n-1) `div` m))),
      TextMap <$> (tree' (n-1)),
      Or <$> tree' ((n-1) `div` 2) <*> tree' ((n-1) `div` 2)]
  shrink tr = case tr of
    Tuple s ts -> Null : ts ++ [Tuple s ts' | ts' <- shrinkList shrink ts] ++ [Tuple Strict ts | s == Tolerant]
    Array t -> Null : t : [Array t' | t' <- shrink t]
    NamedTuple s ps -> Null : map snd ps ++ [NamedTuple s ps' | ps' <- shrinkList shrink ps] ++ [NamedTuple Strict ps | s == Tolerant]
    TextMap t -> Null : t : [TextMap t' | t' <- shrink t]
    Refined t p -> Null : t : [Refined t' p | t' <- shrink t]
    Or t1 t2 -> Null : [t1, t2] ++ [Or t1' t2' | (t1', t2') <- shrink (t1, t2)]
    Alternative t1 t2 _ -> Null : [t1, t2]
    ConstNumber x -> Null : [ConstNumber 1 | x /= 1]
    ConstText s -> Null : [ConstText "a" | s /= "a"]
    Null -> []
    _ -> [Null]

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

checkedSpec :: Gen Spec
checkedSpec = arbitrary `suchThatMap` (\sp -> either (const Nothing) Just $ checkSpec M.empty sp)

matchedData :: TypeRep -> Gen JsonData
--matchedData t = arbitrary `suchThat` (matchSpec' M.empty t)
matchedData tr = sized (tree' tr) where
  tree' tr = \n -> case tr of
    Anything -> resize n arbitrary
    Number -> JsonNumber <$> arbitrary
    Text -> JsonText <$> arbitrary
    Boolean -> JsonBoolean <$> arbitrary
    Null -> pure $ JsonNull
    ConstNumber m -> pure $ JsonNumber m
    ConstText s -> pure $ JsonText s
    ConstBoolean b -> pure $ JsonBoolean b
    Tuple _ [] -> pure $ JsonArray [] --TODO: consider tolerant case
    Tuple _ ts -> JsonArray <$> sequence (map (\t -> tree' t ((n-1) `div` (length ts))) ts) --TODO: consider tolerant case
    Array t -> arbNat >>= \m -> JsonArray <$> vectorOf m (tree' t ((n-1) `div` m))
    NamedTuple _ [] -> pure $ JsonObject [] --TODO: consider tolerant case
    NamedTuple _ ps -> JsonObject <$> sequence [(k,) <$> tree' t ((n-1) `div` length ps) | (k, t) <- ps] --TODO: consider tolerant case
    TextMap t -> arbNat >>= \m -> JsonObject <$> arbMap m arbId (tree' t ((n-1) `div` m))
    Refined t p -> tree' t (n-1) `suchThat` testProp p
    Ref name -> error "matchedData should not be used on Ref"
    Or a b -> oneof [tree' a n, tree' b n]
    Alternative a b _ ->  oneof [tree' a n, tree' b n]

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
        let rst = tryMatchSpec M.empty sp (example sp)
        in isRight rst ==> case rst of Right r -> r === Matched

    prop "matchSpec-Or-commutative" $
      \(sp1 :: Spec) (sp2 :: Spec) (d :: JsonData) ->
        let rst = (,) <$> checkSpec M.empty (Or sp1 sp2) <*> checkSpec M.empty (Or sp2 sp1)
        in isRight rst ==> case rst of Right (or1, or2) -> (let r1 = matchSpec'' or1 d; r2 = matchSpec'' or2 d in collect (r1 == Matched) $ r1 === r2)

    prop "checkSpec-Or-commutative" $
      \(sp1 :: Spec) (sp2 :: Spec) (d :: JsonData) ->
        let rst1 = checkSpec M.empty (Or sp1 sp2)
            rst2 = checkSpec M.empty (Or sp2 sp1)
        in isRight rst1 === isRight rst2

    prop "checkSpec-overlapping-evidence-correct" $
      \(sp1 :: Spec) (sp2 :: Spec) ->
        let rst = checkSpec M.empty (Or sp1 sp2)
        in not (isRight rst) ==> case rst of
          Left (ExistOverlappingOr sp1' sp2' evi) ->
            (matchSpec'' sp1' evi === Matched .&&. matchSpec'' sp2' evi === Matched) <?> show (sp1', sp2', evi)
          _ -> label "not ExistOverlappingOr" True

    prop "matchSpec- Or a b >= a" $
      \(sp1 :: Spec) (sp2 :: Spec) (d :: JsonData) ->
        let rst = checkSpec M.empty (Or sp1 sp2)
        in isRight rst ==> case rst of
          Right or1@(Alternative sp1' sp2' _) -> matchSpec'' sp1' d == Matched ==> matchSpec'' or1 d === Matched

    prop "matchSpec-Tolerant-Tuple-accept-redurant-null" $
      \(sps :: [Spec]) (ds :: [JsonData]) ->
        let rst = checkSpec M.empty (Tuple Tolerant sps)
        in isRight rst ==> case rst of
          Right sp ->
            let d1 = JsonArray ds
                d2 = JsonArray (ds ++ [JsonNull])
            in matchSpec'' sp d1 == Matched ==> matchSpec'' sp d2 === Matched <?> show (sp, d1, d2)

    prop "matchedData-do-matchSpec" $
      forAll checkedSpec $ \sp ->
        forAll (matchedData sp) $ \d ->
          matchSpec'' sp d === Matched

    prop "matchSpec-Tolerant-Tuple-accept-lacking-null" $
      forAll checkedSpec $ \sp1 ->
        matchNull sp1 ==>
          forAll arbNat $ \n ->
            forAll (vectorOf n checkedSpec) $ \sps ->
              forAll (matchedData (Tuple Tolerant sps)) $ \d ->
                matchSpec'' (Tuple Tolerant (sps ++ [sp1])) d === Matched

    it "works with some simple cases" $ do
      show (checkSpec env (Or Number Text)) `shouldBe` "Right (Number | Text)"
      show (checkSpec env (Or (Or Number Text) (ConstText "abc"))) `shouldBe` "Left (ExistOverlappingOr (Number | Text) \"abc\" \"abc\")"
      show (checkSpec env (Or (Or Number Text) case1)) `shouldBe` "Right ((Number | Text) | (\"Lit\", Number))"
      show (checkSpec env (Or (Or Number Text) case2)) `shouldBe` "Right ((Number | Text) | (\"Add\", AST, AST))"
      show (checkSpec env (Or (Or Number Text) ast)) `shouldBe` "Right ((Number | Text) | ((\"Lit\", Number) | (\"Add\", AST, AST)))"
      show (checkSpec env (Or (Or Number Text) case1')) `shouldBe` "Right ((Number | Text) | (\"Lit\", 1.0))"
      show (checkSpec env (Or (Or Number Text) (Or case1 case1'))) `shouldBe` "Left (ExistOverlappingOr (\"Lit\", Number) (\"Lit\", 1.0) [\"Lit\", 1.0])"
      show (toShape env ast) `shouldBe` "((\"Lit\", Number) |? (\"Add\", ((\"Lit\", Number) |? (\"Add\", Anything, Anything)), ((\"Lit\", Number) |? (\"Add\", Anything, Anything))))"
      show (checkSpec env (Or spec1 spec2)) `shouldBe` "Right ({x: Number, y: Number, *} | {z: Number, x: Text, *})"
      show (checkSpec env (Or spec1 spec2')) `shouldBe` "Left (ExistOverlappingOr {x: Number, y: Number, *} {z: Number, x: Number, *} {x: 0.0, y: 0.0, z: 0.0})"
      show (checkSpec env (Or spec1 spec2')) `shouldBe` "Left (ExistOverlappingOr {x: Number, y: Number, *} {z: Number, x: Number, *} {x: 0.0, y: 0.0, z: 0.0})"
      show (tryMatchSpec env ast dat1) `shouldBe` "Right Matched"
      show (tryMatchSpec env ast dat2) `shouldBe` "Right (UnMatched (StepCause OrNotMatchLeft (StepCause (TupleFieldNotMatch 1) (DirectCause ShapeNotMatch Number \"1\"))))"
      show (tryMatchSpec env spec3 data3) `shouldBe` "Right (UnMatched (StepCause (NamedTupleFieldNotMatch \"y\") (StepCause (NamedTupleFieldNotMatch \"w\") (DirectCause ShapeNotMatch Number \"3\"))))"
      show (tryMatchSpec env spec4 data4) `shouldBe` "Right (UnMatched (StepCause OrNotMatchLeft (StepCause (NamedTupleFieldNotMatch \"y\") (StepCause (NamedTupleFieldNotMatch \"w\") (DirectCause ShapeNotMatch Number \"3\")))))"

-- test data

ast = Or case1 case2
case1 = (Tuple Strict [ConstText "Lit", Number])
case1' = (Tuple Strict [ConstText "Lit", ConstNumber 1])
case2 = (Tuple Strict [ConstText "Add", Ref "AST", Ref "AST"])

env = M.fromList [("AST", ast)]
dat1 = JsonArray [JsonText "Lit", JsonNumber 1]
dat2 = JsonArray [JsonText "Lit", JsonText "1"]

spec1 = NamedTuple Tolerant [("x", Number), ("y", Number)]
spec2 = NamedTuple Tolerant [("z", Number), ("x", Text)]
spec2' = NamedTuple Tolerant [("z", Number), ("x", Number)]

spec3 = NamedTuple Tolerant [("x", Number), ("y", NamedTuple Tolerant [("z", Number), ("w", Number)])]
data3 = JsonObject [("x", JsonNumber 1), ("y", JsonObject [("z", JsonNumber 2), ("w", JsonText "3")])]

spec4 = Or spec3 (NamedTuple Tolerant [("x", Text), ("y", Number)])
data4 = JsonObject [("x", JsonNumber 1), ("y", JsonObject [("z", JsonNumber 2), ("w", JsonText "3")])]

