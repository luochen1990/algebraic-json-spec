-- Copyright 2018 and onwards LuoChen (luochen1990@gmail.com).

import Prelude hiding (otherwise)
import qualified Data.Map as M
import Data.Semigroup
import Data.Foldable (fold, foldMap)
import Data.Maybe
import GHC.Exts (sortWith)

compareSortedListWith :: Ord b => (a -> b) -> [a] -> [a] -> ([(a, a)], [a], [a])
compareSortedListWith = undefined

-- TypeRep & JsonData

data TypeRep =
      Number
    | Text
    | Boolean
    | Null
    | ConstNumber Double
    | ConstText String
    | ConstBoolean Bool
    | Tuple [TypeRep]
    | Array TypeRep
    | NamedTuple [(String, TypeRep)]
    | TextMap TypeRep
    | Refined TypeRep DecProp
    | Or TypeRep TypeRep (JsonData -> MatchChoice) -- dependently typed: Or (t1 : TypeRep) (t2 : TypeRep) (prf : typeOverlap t1 t2 = NonOverlapping)

data DecProp = DecProp {testProp :: JsonData -> Bool}
data MatchChoice = MatchLeft | MatchRight | MatchNothing deriving (Show, Eq, Ord)

data JsonData =
      JsonNumber Double
    | JsonText String
    | JsonBoolean Bool
    | JsonNull
    | JsonArray [JsonData]
    | JsonObject [(String, JsonData)]
    deriving (Show, Eq, Ord)

-- useful tools

example :: TypeRep -> JsonData
example = undefined

extendObject :: JsonData -> JsonData -> JsonData
extendObject (JsonObject ps1) (JsonObject ps2) = JsonObject (ps1 ++ ps2)
extendObject _ _ = error "extendObject must be used on two JsonObject"

-- typeOverlap & decideMatchChoice

data TypeRelation =
      Overlapping JsonData
    | MayOverlapping JsonData
    | NonOverlapping (JsonData -> MatchChoice)

joinTupleComponents :: [TypeRelation] -> TypeRelation
joinTupleComponents [] = Overlapping (JsonArray [])
joinTupleComponents (r:rs) = case (r, joinTupleComponents rs) of
    (Overlapping d1, Overlapping (JsonArray ds)) -> Overlapping (JsonArray (d1:ds))
    (Overlapping d1, MayOverlapping (JsonArray ds)) -> MayOverlapping (JsonArray (d1:ds))
    (MayOverlapping d1, Overlapping (JsonArray ds)) -> MayOverlapping (JsonArray (d1:ds))
    (MayOverlapping d1, MayOverlapping (JsonArray ds)) -> MayOverlapping (JsonArray (d1:ds))
    (_, NonOverlapping c2) -> NonOverlapping (\d -> case d of (JsonArray (x:xs)) -> c2 (JsonArray xs); _ -> MatchNothing)
    (NonOverlapping c1, _) -> NonOverlapping (\d -> case d of (JsonArray (x:xs)) -> c1 x; _ -> MatchNothing)

joinObjectComponents :: [(String, TypeRelation)] -> TypeRelation
joinObjectComponents [] = Overlapping (JsonObject [])
joinObjectComponents ((k, r):ps) = case (r, joinObjectComponents ps) of
    (Overlapping v1, Overlapping (JsonObject kvs)) -> Overlapping (JsonObject ((k,v1):kvs))
    (Overlapping v1, MayOverlapping (JsonObject kvs)) -> MayOverlapping (JsonObject ((k,v1):kvs))
    (MayOverlapping v1, Overlapping (JsonObject kvs)) -> MayOverlapping (JsonObject ((k,v1):kvs))
    (MayOverlapping v1, MayOverlapping (JsonObject kvs)) -> MayOverlapping (JsonObject ((k,v1):kvs))
    (_, NonOverlapping c2) -> NonOverlapping (\d -> case d of (JsonObject kvs) -> c2 (JsonObject kvs); _ -> MatchNothing) -- note that not remove k is correct
    (NonOverlapping c1, _) -> NonOverlapping (\d -> case d of (JsonObject kvs) -> c1 (fromMaybe JsonNull (M.lookup k (M.fromList kvs))); _ -> MatchNothing)

joinLeftOrPath :: TypeRelation -> TypeRelation -> TypeRelation
joinLeftOrPath r1 r2 = case (r1, r2) of
    (Overlapping d1, _) -> Overlapping d1
    (_, Overlapping d2) -> Overlapping d2
    (MayOverlapping d1, _) -> MayOverlapping d1
    (_, MayOverlapping d2) -> MayOverlapping d2
    (NonOverlapping c13, NonOverlapping c23) -> NonOverlapping $ \d ->
        case (c13 d, c23 d) of
            (MatchLeft, _) -> MatchLeft -- t1/t2 of course
            (_, MatchLeft) -> MatchLeft -- t2 of course
            (MatchRight, MatchRight) -> MatchRight -- t3 of course
            (MatchNothing, MatchNothing) -> MatchNothing
            _ -> MatchNothing -- seems impossible

joinRightOrPath :: TypeRelation -> TypeRelation -> TypeRelation
joinRightOrPath r1 r2 = case (r1, r2) of
    (Overlapping d1, _) -> Overlapping d1
    (_, Overlapping d2) -> Overlapping d2
    (MayOverlapping d1, _) -> MayOverlapping d1
    (_, MayOverlapping d2) -> MayOverlapping d2
    (NonOverlapping c12, NonOverlapping c13) -> NonOverlapping $ \d ->
        case (c12 d, c13 d) of
            (MatchRight, _) -> MatchRight -- t2/t3 of course
            (_, MatchRight) -> MatchRight -- t3 of course
            (MatchLeft, MatchLeft) -> MatchLeft -- t1 of course
            (MatchNothing, MatchNothing) -> MatchNothing
            _ -> MatchNothing -- seems impossible

typeOverlap :: TypeRep -> TypeRep -> TypeRelation
typeOverlap tr1 tr2 = case (tr1, tr2) of
    (Tuple ts1, Tuple ts2) ->
        let (l1, l2) = (length ts1, length ts2)
        in
            if l1 /= l2
            then NonOverlapping $ \d -> case d of
                (JsonArray xs) ->
                    let l = length xs
                    in
                        if l == l1 then MatchLeft
                        else if l == l2 then MatchRight
                        else MatchNothing
                _ -> MatchNothing
            else -- have same length
                joinTupleComponents (zipWith typeOverlap ts1 ts2)
    (Tuple ts1, Array t2) ->
        joinTupleComponents (zipWith typeOverlap ts1 (repeat t2))
    (Array t1, Tuple ts2) ->
        joinTupleComponents (zipWith typeOverlap (repeat t1) ts2)
    (Array t1, Array t2) ->
        Overlapping (JsonArray [])
    (NamedTuple ps1, NamedTuple ps2) ->
        -- 若 把 NamedTuple 看做严格模式, 即不允许冗余字段, 则:
        --      直接参考 Tuple 的实现即可.
        -- 若 把 NamedTuple 看作不严格模式, 即允许冗余字段:
        --      首先对两个 key 集的交集部分取 joinObjectComponents
        --      若 该部分不相交, 则必不相交,
        --      若 该部分相交, 则必相交, 因为其中一方未定义的字段可以当做Any.
        let (common, fstOnly, sndOnly) = compareSortedListWith fst (sortWith fst ps1) (sortWith fst ps2)
        in case joinObjectComponents [(k, typeOverlap t1 t2) | ((k, t1), (_, t2)) <- common] of
            Overlapping d -> Overlapping (extendObject d (example (NamedTuple (fstOnly ++ sndOnly))))
            MayOverlapping d -> MayOverlapping (extendObject d (example (NamedTuple (fstOnly ++ sndOnly))))
            NonOverlapping c -> NonOverlapping c
    (NamedTuple ps1, TextMap t2) ->
        joinObjectComponents [(k, typeOverlap t1 t2) | (k, t1) <- ps1]
    (TextMap t1, NamedTuple ps2) ->
        joinObjectComponents [(k, typeOverlap t1 t2) | (k, t2) <- ps2]
    (TextMap t1, TextMap t2) ->
        Overlapping (JsonObject [])
    (Or t1 t2 _, t3) ->
        joinLeftOrPath (typeOverlap t1 t3) (typeOverlap t2 t3)
    (t1, Or t2 t3 _) ->
        joinLeftOrPath (typeOverlap t1 t2) (typeOverlap t1 t3)
    (Refined t1 _, t2) ->
        typeOverlap t1 t2
    (t1, t2) -> -- trivial cases, simply with different shapes.
        NonOverlapping $ \d -> if (matchSpec' t1 d) then MatchLeft else if (matchSpec' t2 d) then MatchRight else MatchNothing


-- matchSpec

data MatchResult = Matched | UnMatched UnMatchedReason
data UnMatchedReason =
      ShapeNotMatch TypeRep JsonData
    | ConstValueNotEqual TypeRep JsonData
    | TupleLengthNotMatch TypeRep JsonData
    | TupleFieldNotMatch Int UnMatchedReason
    | ArrayElementNotMatch Int UnMatchedReason
    | NamedTupleFieldNotMatch String UnMatchedReason
    | TextMapElementNotMatch String UnMatchedReason
    | RefinedShapeNotMatch UnMatchedReason
    | RefinedPropNotMatch TypeRep JsonData
    | OrMatchNothing TypeRep JsonData
    | OrNotMatchLeft UnMatchedReason
    | OrNotMatchRight UnMatchedReason

--unless :: UnMatchedReason -> Bool -> MatchResult
--reason `unless` b = if b then Matched else UnMatched reason

otherwise :: Bool -> UnMatchedReason -> MatchResult
b `otherwise` reason = if b then Matched else UnMatched reason

wrap :: (UnMatchedReason -> UnMatchedReason) -> MatchResult -> MatchResult
wrap step rst = case rst of Matched -> Matched; UnMatched reason -> UnMatched (step reason)

instance Semigroup MatchResult where
    (<>) Matched Matched = Matched
    (<>) Matched r2 = r2
    (<>) r1 _ = r1

instance Monoid MatchResult where
    mempty = Matched
    mappend = (<>)

matchSpec :: TypeRep -> JsonData -> MatchResult
matchSpec t d = case (t, d) of
    (Number, (JsonNumber _)) -> Matched
    (Text, (JsonText _)) -> Matched
    (Boolean, (JsonBoolean _)) -> Matched
    (Null, JsonNull) -> Matched
    (ConstNumber n, d@(JsonNumber n')) -> (n == n') `otherwise` (ConstValueNotEqual (ConstNumber n) d)
    (ConstText s, d@(JsonText s')) -> (s == s') `otherwise` (ConstValueNotEqual (ConstText s) d)
    (ConstBoolean b, d@(JsonBoolean b')) -> (b == b') `otherwise` (ConstValueNotEqual (ConstBoolean b) d)
    (Tuple ts, d@(JsonArray xs)) ->
        (let l1 = length ts; l2 = length xs in (l1 == l2) `otherwise` (TupleLengthNotMatch t d)) <>
        fold [wrap (TupleFieldNotMatch i) (matchSpec t x) | (i, t, x) <- zip3 [0..] ts xs]
    (Array t, (JsonArray xs)) -> fold [wrap (ArrayElementNotMatch i) (matchSpec t x) | (i, x) <- zip [0..] xs]
    (NamedTuple ps, (JsonObject kvs)) -> let mp = M.fromList kvs in fold [matchSpec t (fromMaybe JsonNull (M.lookup k mp)) | (k, t) <- ps]
    (TextMap t, (JsonObject kvs)) -> fold [wrap (TextMapElementNotMatch k) (matchSpec t v) | (k, v) <- kvs]
    (t@(Refined t1 p), d) -> wrap RefinedShapeNotMatch (matchSpec t1 d) <> (testProp p d `otherwise` (RefinedPropNotMatch t d))
    (t@(Or t1 t2 makeChoice), d) -> case makeChoice d of
        MatchLeft -> wrap OrNotMatchLeft (matchSpec t1 d)
        MatchRight -> wrap OrNotMatchRight (matchSpec t2 d)
        MatchNothing -> UnMatched (OrMatchNothing t d)
    (t, d) -> UnMatched (ShapeNotMatch t d)

matchSpec' :: TypeRep -> JsonData -> Bool
matchSpec' t d = case (t, d) of
    (Number, (JsonNumber _)) -> True
    (Text, (JsonText _)) -> True
    (Boolean, (JsonBoolean _)) -> True
    (Null, JsonNull) -> True
    (ConstNumber x, (JsonNumber x')) -> x == x'
    (ConstText s, (JsonText s')) -> s == s'
    (ConstBoolean b, (JsonBoolean b')) -> b == b'
    (Tuple ts, (JsonArray xs)) -> length ts == length xs && all (uncurry matchSpec') (zip ts xs)
    (Array t, (JsonArray xs)) -> all (matchSpec' t) xs
    (NamedTuple ps, (JsonObject kvs)) ->
        let mp = M.fromList kvs
        in and [matchSpec' t (fromMaybe JsonNull (M.lookup k mp)) | (k, t) <- ps]
    (TextMap t, (JsonObject kvs)) -> all (matchSpec' t) (map snd kvs)
    (Refined t p, d) -> matchSpec' t d && testProp p d
    --(Or t1 t2 _, d) -> matchSpec' t1 d || matchSpec' t2 d
    (Or t1 t2 makeChoice, d) -> case makeChoice d of
        MatchLeft -> matchSpec' t1 d
        MatchRight -> matchSpec' t2 d
        MatchNothing -> False
    _ -> False

main :: IO ()
main = print "hello"

