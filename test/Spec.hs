-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

{-# language ScopedTypeVariables #-}
{-# language MonadComprehensions #-}
{-# language TupleSections #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}

--import Debug.Trace
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List
import Data.Fix
import Data.Maybe (mapMaybe)
import Control.Exception
import Data.Bytes.Serial
import Data.Bytes.Get
import Data.Bytes.Put
import Test.Hspec hiding (Spec, example)
import Test.Hspec.QuickCheck
import Test.QuickCheck
import AlgebraicJSON.Core.Tools
import AlgebraicJSON.Core.Definitions
import AlgebraicJSON.Core.Functions
import AlgebraicJSON.Core.Generators
import AlgebraicJSON.Core.Serialize
import AlgebraicJSON.EDSL

isRight :: Either a b -> Bool
isRight e = either (const False) (const True) e

matchSpec' = matchSpec M.empty

(<?>) :: (Testable p) => p -> String -> Property
(<?>) = flip (Test.QuickCheck.counterexample . ("Extra Info: " ++))
infixl 2 <?>

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
      \(sp :: CSpec) ->
        let sh = toShape' sp
        in isDeterminateShape sh ==> matchSpec M.empty sp (example sh) === Matched

    prop "matchSpec-Or-commutative" $
      \(sp1 :: CSpec) (sp2 :: CSpec) (d :: JsonData) ->
        let rst = (,) <$> checkAlternative M.empty sp1 sp2 <*> checkAlternative M.empty sp2 sp1
        in isRight rst ==> case rst of Right (or1, or2) -> (let r1 = matchSpec' or1 d; r2 = matchSpec' or2 d in collect (r1 == Matched) $ r1 === r2)

    prop "checkSpec-Or-commutative" $
      \(sp1 :: Spec) (sp2 :: Spec) (d :: JsonData) ->
        let rst1 = checkSpec M.empty (sp1 <|||> sp2)
            rst2 = checkSpec M.empty (sp2 <|||> sp1)
        in isRight rst1 === isRight rst2

    prop "checkSpec-overlapping-evidence-correct" $
      \(sp1 :: Spec) (sp2 :: Spec) ->
        let rst = checkSpec M.empty (sp1 <|||> sp2)
        in not (isRight rst) ==> case rst of
          Left (ExistOverlappingOr Sure sp1' sp2' evi) ->
            (matchSpec' sp1' evi === Matched .&&. matchSpec' sp2' evi === Matched) <?> show (sp1', sp2', evi)
          _ -> label "not Overlapping Sure" True

    prop "matchSpec- Or a b >= a" $
      \(sp1 :: Spec) (sp2 :: Spec) (d :: JsonData) ->
        let rst = checkSpec M.empty (sp1 <|||> sp2)
        in isRight rst ==> case rst of
          Right or1@(Fix (Alternative sp1' sp2' _)) -> matchSpec' sp1' d == Matched ==> matchSpec' or1 d === Matched

    prop "matchSpec-Tolerant-Tuple-accept-redurant-null" $
      \(sps :: [Spec]) (ds :: [JsonData]) ->
        let rst = checkSpec M.empty (Fix $ Tuple Tolerant sps)
        in isRight rst ==> case rst of
          Right sp ->
            let d1 = JsonArray ds
                d2 = JsonArray (ds ++ [JsonNull])
            in matchSpec' sp d1 == Matched ==> matchSpec' sp d2 === Matched <?> show (sp, d1, d2)

    prop "arbitraryJ-generated-data-do-matchSpec" $
      \(sp :: CSpec) ->
        isDeterminateShape (toShape' sp) ==>
          forAll (arbitraryJ sp) $ \d ->
            matchSpec' sp d === Matched

    prop "matchSpec-Tolerant-Tuple-accept-lacking-null" $
      \(sp1 :: CSpec) ->
        let sh1 = toShape' sp1 in acceptNull sh1 && isDeterminateShape sh1 ==>
          forAll arbNat $ \n ->
            forAll (vectorOf n arbitrary) $ \sps ->
              let sp = (Fix $ Tuple Strict sps)
              in isDeterminateShape (toShape' sp) ==>
                forAll (arbitraryJ sp) $ \d ->
                  let sp' = (Fix $ Tuple Tolerant (sps ++ [sp1])) in matchSpec' sp' d === Matched <?> show sp'

    prop "fromJsonSpec . toJsonSpec == identity" $
      \(sp :: Spec) ->
        toShape' (fromJsonSpec (toJsonSpec sp)) === toShape' sp

    prop "deserialize . serialize == identity (for JsonData)" $
      \(d :: JsonData) ->
        either error id (runGetS deserialize (runPutS (serialize d))) === d

    prop "deserializeJ . serializeJ == identity" $
      \(sp :: CSpec) ->
        isDeterminateShape (toShape' sp) ==>
          forAll (arbitraryJ sp) $ \d ->
            deserializeJ M.empty sp (serializeJ M.empty sp d) === d

    it "works with some simple cases" $ do
      show (checkSpec env (number <|||> text)) `shouldBe` "Right (Number | Text)"
      show (checkSpec env ((number <|||> text) <|||> (ctext "abc"))) `shouldBe` "Left (ExistOverlappingOr Sure (Number | Text) \"abc\" \"abc\")"
      show (checkSpec env ((number <|||> text) <|||> case1)) `shouldBe` "Right ((Number | Text) | (\"Lit\", Number))"
      show (checkSpec env ((number <|||> text) <|||> case2)) `shouldBe` "Right ((Number | Text) | (\"Add\", AST, AST))"
      show (checkSpec env ((number <|||> text) <|||> ast)) `shouldBe` "Right ((Number | Text) | ((\"Lit\", Number) | (\"Add\", AST, AST)))"
      show (checkSpec env ((number <|||> text) <|||> case1')) `shouldBe` "Right ((Number | Text) | (\"Lit\", 1.0))"
      show (checkSpec env ((number <|||> text) <|||> (case1 <|||> case1'))) `shouldBe` "Left (ExistOverlappingOr Sure (\"Lit\", Number) (\"Lit\", 1.0) [\"Lit\", 1.0])"
      show (toShape 1 env ast) `shouldBe` "((\"Lit\", Number) |? (\"Add\", ((\"Lit\", Number) |? (\"Add\", $, $)), ((\"Lit\", Number) |? (\"Add\", $, $))))"
      show (checkSpec env (spec1 <|||> spec2)) `shouldBe` "Right ({x: Number, y: Number, *} | {z: Number, x: Text, *})"
      show (checkSpec env (spec1 <|||> spec2')) `shouldBe` "Left (ExistOverlappingOr Sure {x: Number, y: Number, *} {z: Number, x: Number, *} {x: 0.0, y: 0.0, z: 0.0})"
      show (checkSpec env (spec1 <|||> spec2')) `shouldBe` "Left (ExistOverlappingOr Sure {x: Number, y: Number, *} {z: Number, x: Number, *} {x: 0.0, y: 0.0, z: 0.0})"
      show (tryMatchSpec env ast dat1) `shouldBe` "Right Matched"
      show (tryMatchSpec env ast dat2) `shouldBe` "Right (UnMatched (StepCause OrNotMatchLeft (StepCause (TupleFieldNotMatch 1) (DirectCause OutlineNotMatch Number \"1\"))))"
      show (tryMatchSpec env spec3 data3) `shouldBe` "Right (UnMatched (StepCause (NamedTupleFieldNotMatch \"y\") (StepCause (NamedTupleFieldNotMatch \"w\") (DirectCause OutlineNotMatch Number \"3\"))))"
      show (tryMatchSpec env spec4 data4) `shouldBe` "Right (UnMatched (StepCause OrNotMatchLeft (StepCause (NamedTupleFieldNotMatch \"y\") (StepCause (NamedTupleFieldNotMatch \"w\") (DirectCause OutlineNotMatch Number \"3\")))))"
      show (tryMatchSpec M.empty (tuple' [number, cnull]) (JsonArray [JsonNumber 2])) `shouldBe` "Right Matched"
      show (tryMatchSpec M.empty (tuple' [number, cnull] <|||> tuple [cnumber 1, cnumber 1]) (JsonArray [JsonNumber 2])) `shouldBe` "Right Matched"
      show (checkSpec M.empty (tuple' [refined cnull (const False)] <|||> tuple [])) `shouldBe` "Left (ExistOverlappingOr Unsure (Refined<Null>, *) () [])"

-- test data

env = M.fromList [("AST", ast)]
ast = case1 <|||> case2
case1 = tuple [ctext "Lit", number]
case1' = (tuple [ctext "Lit", cnumber 1])
case2 = (tuple [ctext "Add", ref "AST", ref "AST"])

env' = either undefined id (checkEnv env)
ast' = either undefined id (checkSpec env ast)

dat1 = JsonArray [JsonText "Lit", JsonNumber 1]
dat2 = JsonArray [JsonText "Lit", JsonText "1"]

spec1 = object' [("x", number), ("y", number)]
spec2 = object' [("z", number), ("x", text)]
spec2' = object' [("z", number), ("x", number)]

spec3 = object' [("x", number), ("y", object' [("z", number), ("w", number)])]
data3 = JsonObject [("x", JsonNumber 1), ("y", JsonObject [("z", JsonNumber 2), ("w", JsonText "3")])]

spec4 = spec3 <|||> (object' [("x", text), ("y", number)])
data4 = JsonObject [("x", JsonNumber 1), ("y", JsonObject [("z", JsonNumber 2), ("w", JsonText "3")])]

