-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

{-# language ScopedTypeVariables #-}
{-# language MonadComprehensions #-}
{-# language TupleSections #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}

import Debug.Trace
import qualified Data.Map as M
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
import JsonSpec.Core.Tools
import JsonSpec.Core.Definitions
import JsonSpec.Core.Functions
import JsonSpec.Core.Generators
import JsonSpec.Core.Serialize
import JsonSpec.EDSL
import JsonSpec.DSL
import JsonSpec.AlgebraicAJS

isRight :: Either a b -> Bool
isRight e = either (const False) (const True) e

matchSpec' = matchSpec M.empty

(<?>) :: (Testable p) => p -> String -> Property
(<?>) = flip (Test.QuickCheck.counterexample . ("Extra Info: " ++))
infixl 2 <?>

main :: IO ()
main = hspec $ do
  describe "Arith" $ do
    prop "plus-comm" $
      \(x :: Int) (y :: Int) ->
        collect (x == y) $ x + y === y + x

  describe "Tools" $ do
    prop "compareSortedListWith correct" $
      \(ori_xs :: [Int]) (ori_ys :: [Int]) ->
        let (xs, ys) = (sort ori_xs, sort ori_ys)
            (both, onlyL, onlyR) = compareSortedListWith id xs ys
            (bothL, bothR) = unzip both
        in
          mergeSorted bothL onlyL === xs .&&. mergeSorted bothR onlyR === ys .&&.
          (case (compareSortedListWith id onlyL onlyR) of (both', _, _) -> both' === []) .&&.
          (case (compareSortedListWith id bothL bothR) of (both', _, _) -> both' === both)

  describe "JsonSpec" $ do
    describe "examples" test_simple_examples

    describe "Core.Generators" $ do
      prop "arbitraryJ-generated-data-do-matchSpec" $
        \(sp :: CSpec) ->
          -- trace (show sp) $
          forAll (arbitraryJ sp) $ \d ->
            matchSpec' sp d === Matched

    describe "Core" $ do
      prop "example-matchSpec" $
        \(sp :: CSpec) ->
          let sh = toShape' sp
          in isDeterminateShape sh ==> matchSpec M.empty sp (example sh) === Matched

      prop "matchSpec-Or-commutative" $
        \(sp1 :: CSpec) (sp2 :: CSpec) ->
          let rst = (,) <$> checkOr M.empty sp1 sp2 <*> checkOr M.empty sp2 sp1
          in isRight rst ==> case rst of
            Right (or1, or2) ->
              \(d :: JsonData) ->
                (let r1 = matchSpec' or1 d; r2 = matchSpec' or2 d in collect (r1 == Matched) $ r1 === r2)

      prop "matchSpec-Or-associative" $
        \(sp1 :: Spec) (sp2 :: Spec) (sp3 :: Spec) ->
          let rst = (,) <$> checkSpec M.empty ((sp1 <|||> sp2) <|||> sp3) <*> checkSpec M.empty (sp1 <|||> (sp2 <|||> sp3))
          in isRight rst ==> case rst of
            Right (or1, or2) ->
              \(d :: JsonData) ->
                (let r1 = matchSpec' or1 d; r2 = matchSpec' or2 d in collect (r1 == Matched) $ r1 === r2)

      prop "checkSpec-Or-commutative" $
        \(sp1 :: Spec) (sp2 :: Spec) (d :: JsonData) ->
          let rst1 = checkSpec M.empty (sp1 <|||> sp2)
              rst2 = checkSpec M.empty (sp2 <|||> sp1)
          in collect (isRight rst1) $ isRight rst1 === isRight rst2

      prop "checkSpec-Or-associative" $
        \(sp1 :: Spec) (sp2 :: Spec) (sp3 :: Spec) (d :: JsonData) ->
          let rst1 = checkSpec M.empty ((sp1 <|||> sp2) <|||> sp3)
              rst2 = checkSpec M.empty (sp1 <|||> (sp2 <|||> sp3))
          in collect (isRight rst1) $ isRight rst1 === isRight rst2

      prop "checkSpec-overlapping-evidence-correct" $
        \(sp1 :: CSpec) (sp2 :: CSpec) ->
          let rst = checkOr M.empty sp1 sp2
          in not (isRight rst) ==> case rst of
            Left (ExistOverlappingOr Sure sp1' sp2' evi) ->
              (matchSpec' sp1' evi === Matched .&&. matchSpec' sp2' evi === Matched) <?> show (sp1', sp2', evi)
            _ -> label "not Overlapping Sure" True

      prop "matchSpec-Or-accept-more (a | b >= a)" $
        \(sp1 :: CSpec) (sp2 :: CSpec) ->
          let rst = checkOr M.empty sp1 sp2
          in isRight rst ==> case rst of
            Right or1@(Fix (Or sp1' sp2' _)) ->
              \(d :: JsonData) ->
                matchSpec' sp1' d == Matched || matchSpec' sp2' d == Matched ==>
                  matchSpec' or1 d === Matched <?> show (matchSpec' sp1' d, matchSpec' sp2' d)

      prop "matchSpec-Tolerant-Tuple-accept-redurant-null" $
        \(sps :: [CSpec]) ->
          let sp = (Fix $ Tuple Tolerant sps)
          in forAll (arbitraryJ sp) $ \d1 ->
            let d2 = (case d1 of (JsonArray ds) -> JsonArray (ds ++ [JsonNull]))
            in matchSpec' sp d2 === Matched <?> show (sp, d1, d2)

      prop "matchSpec-Tolerant-Tuple-accept-lacking-null" $
        \(sps :: [CSpec]) ->
            let sp = (Fix $ Tuple Strict sps)
                sp' = (Fix $ Tuple Tolerant (sps ++ [Fix Null]))
            in
              forAll (arbitraryJ sp) $ \d ->
                matchSpec' sp' d === Matched <?> show sp'

    describe "Serialize" $ do
      prop "deserialize <> serialize == identity (for JsonData)" $
        \(d :: JsonData) ->
          either error id (runGetS deserialize (runPutS (serialize d))) === d

      prop "deserializeJ <> serializeJ == identity" $
        \(sp :: CSpec) ->
          isDeterminateShape (toShape' sp) ==>
            forAll (arbitraryJ sp) $ \d ->
              deserializeJ M.empty sp (serializeJ M.empty sp d) === d

    describe "DSL" $ do
      prop "parseExpr <> show == identity" $
        \(sp :: Spec) ->
          forAll (arbPropAbout sp) $ \e ->
            (parseExpr (show e)) === (Right e :: Either String Expr)

      prop "parseJsonData <> show == identity" $
        \(d :: JsonData) ->
          (parseJsonData (show d)) === (Right d :: Either String JsonData)

      prop "parseSpec <> show == identity" $
        \(sp :: Spec) ->
          (parseSpec (show sp)) === (Right sp :: Either String Spec)

    describe "AlgebraicAJS" $ do
      prop "fromJson <> toJson == identity" $
        \(sp :: Spec) ->
          toShape' (fromJson (toJson sp) :: Spec) === toShape' sp

      prop "matchSpec aajs & toJson" $
        \(sp :: Spec) ->
          matchSpec aajs (aajs M.! "JsonSpec") (toJson sp) === Matched <?> show (toJson sp)

    describe "** statistics **" $ do
      prop "check ratio" $
        \(sp :: Spec) ->
          collect (isRight $ checkSpec M.empty sp) True

      prop "match ratio" $
        \(sp :: CSpec) (d :: JsonData) ->
          collect (matchSpec' sp d == Matched) True

      prop "isDeterminateShape" $
        \(sp :: CSpec) ->
          collect (isDeterminateShape (toShape' sp)) True

      prop "acceptNull" $
        \(sp :: CSpec) ->
          collect (acceptNull (toShape' sp)) True

      prop "isDeterminateShape && acceptNull" $
        \(sp :: CSpec) ->
          collect (let sh = toShape' sp in acceptNull sh && isDeterminateShape sh) True

-- simple examples

test_simple_examples = do
  it "works with some simple cases" $ do
    show (checkSpec env (number <|||> text)) `shouldBe` "Right (Number | Text)"
    show (checkSpec env ((number <|||> text) <|||> (ctext "abc"))) `shouldBe` "Left (ExistOverlappingOr Sure (Number | Text) \"abc\" \"abc\")"
    show (checkSpec env ((number <|||> text) <|||> case1)) `shouldBe` "Right ((Number | Text) | [\"Lit\", Number])"
    show (checkSpec env ((number <|||> text) <|||> case2)) `shouldBe` "Right ((Number | Text) | [\"Add\", AST, AST])"
    show (checkSpec env ((number <|||> text) <|||> ast)) `shouldBe` "Right ((Number | Text) | ([\"Lit\", Number] | [\"Add\", AST, AST]))"
    show (checkSpec env ((number <|||> text) <|||> case1')) `shouldBe` "Right ((Number | Text) | [\"Lit\", 1.0])"
    show (checkSpec env ((number <|||> text) <|||> (case1 <|||> case1'))) `shouldBe` "Left (ExistOverlappingOr Sure [\"Lit\", Number] [\"Lit\", 1.0] [\"Lit\", 1.0])"
    show (toShape 1 env ast) `shouldBe` "([\"Lit\", Number] |? [\"Add\", ([\"Lit\", Number] |? [\"Add\", $, $]), ([\"Lit\", Number] |? [\"Add\", $, $])])"
    show (checkSpec env (spec1 <|||> spec2)) `shouldBe` "Right ({x: Number, y: Number, *} | {z: Number, x: Text, *})"
    show (checkSpec env (spec1 <|||> spec2')) `shouldBe` "Left (ExistOverlappingOr Sure {x: Number, y: Number, *} {z: Number, x: Number, *} {x: 0.0, y: 0.0, z: 0.0})"
    show (checkSpec env (spec1 <|||> spec2')) `shouldBe` "Left (ExistOverlappingOr Sure {x: Number, y: Number, *} {z: Number, x: Number, *} {x: 0.0, y: 0.0, z: 0.0})"
    show (tryMatchSpec env ast dat1) `shouldBe` "Right Matched"
    show (tryMatchSpec env ast dat2) `shouldBe` "Right (UnMatched (StepCause OrNotMatchLeft (StepCause (TupleFieldNotMatch 1) (DirectCause OutlineNotMatch Number \"1\"))))"
    show (tryMatchSpec env spec3 data3) `shouldBe` "Right (UnMatched (StepCause (ObjectFieldNotMatch \"y\") (StepCause (ObjectFieldNotMatch \"w\") (DirectCause OutlineNotMatch Number \"3\"))))"
    show (tryMatchSpec env spec4 data4) `shouldBe` "Right (UnMatched (StepCause OrNotMatchLeft (StepCause (ObjectFieldNotMatch \"y\") (StepCause (ObjectFieldNotMatch \"w\") (DirectCause OutlineNotMatch Number \"3\")))))"
    show (tryMatchSpec M.empty (tuple' [number, cnull]) (JsonArray [JsonNumber 2])) `shouldBe` "Right Matched"
    show (tryMatchSpec M.empty (tuple' [number, cnull] <|||> tuple [cnumber 1, cnumber 1]) (JsonArray [JsonNumber 2])) `shouldBe` "Right Matched"
    show (checkSpec M.empty (tuple' [refined cnull (Lit (JsonBoolean False))] <|||> tuple [])) `shouldBe` "Left (ExistOverlappingOr Unsure [(Null <{ False }>), *] [] [])"

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

