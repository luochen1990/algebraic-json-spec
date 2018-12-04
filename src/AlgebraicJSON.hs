-- Copyright 2018 LuoChen (luochen1990@gmail.com). Licensed under the Apache License 2.0.

{-# language TupleSections #-}
{-# language FlexibleInstances #-}

module AlgebraicJSON (
    TyRep(..), Spec, CSpec, Shape, Strictness(..),
    JsonData(..), DecProp(..), Name, ChoiceMaker,
    checkSpec, matchSpec, matchSpec', tryMatchSpec, everywhereJ, example, MatchResult(..), CheckFailedReason(..),
    matchNull, notNullPrefix,
    toShape, compareSortedListWith, testAJ
) where

import Debug.Trace
import Prelude hiding (otherwise)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Semigroup
import Data.Foldable (fold, foldMap)
import Data.List (intercalate)
import Data.Maybe
import Data.Fix
import Data.Char (isAlphaNum)
import Text.MultilingualShow
import Control.Monad.State
import GHC.Exts (sortWith)

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

-- TyRep & JsonData

-- | TyRep r p c tr' means a Type Representation,
-- | with Ref indexed by r, Refined with p, Alternative attached with c,
-- | and recursively defined on tr'.
data TyRep r p c tr' =
      Anything
    | Number
    | Text
    | Boolean
    | Null
    | ConstNumber Double
    | ConstText String
    | ConstBoolean Bool
    | Tuple Strictness [tr']
    | Array tr'
    | NamedTuple Strictness [(String, tr')]
    | TextMap tr'
    | Ref r
    | Refined tr' p
    | Alternative tr' tr' c

-- | the Spec parsed from user input
type Spec = Fix (TyRep Name DecProp ())

-- | the checked Spec, attached with choice maker
type CSpec = Fix (TyRep Name DecProp ChoiceMaker)

-- | the Shape of a Spec, ignore Ref, Refined information of Spec
type Shape = Fix (TyRep () () ())

type Name = String
data DecProp = DecProp {testProp :: JsonData -> Bool}
data MatchChoice = MatchLeft | MatchRight | MatchNothing deriving (Show, Eq, Ord)
type ChoiceMaker = JsonData -> MatchChoice
data Strictness = Strict | Tolerant deriving (Show, Eq, Ord)

data JsonData =
      JsonNumber Double
    | JsonText String
    | JsonBoolean Bool
    | JsonNull
    | JsonArray [JsonData]
    | JsonObject [(String, JsonData)]
    deriving (Eq, Ord)

type Env a = M.Map Name a

-- useful tools

example :: Shape -> JsonData
example (Fix tr) = case tr of
    Anything -> JsonNull
    Number -> JsonNumber 0
    Text -> JsonText ""
    Boolean -> JsonBoolean True
    Null -> JsonNull
    ConstNumber n -> JsonNumber n
    ConstText s -> JsonText s
    ConstBoolean b -> JsonBoolean b
    Tuple _ ts -> JsonArray (map example ts)
    Array t -> JsonArray [(example t)]
    NamedTuple _ ps -> JsonObject [(k, example t) | (k, t) <- ps]
    TextMap t -> JsonObject [("k", example t)]
    Ref _ -> error "example cannot be used on Ref"
    Refined t _ -> error "examplecannot be used on Refined"
    Alternative a b _ -> example a

extendObj :: JsonData -> JsonData -> JsonData
extendObj (JsonObject ps1) (JsonObject ps2) = JsonObject (ps1 ++ ps2)
extendObj _ _ = error "extendObj must be used on two JsonObject"

lookupObj :: String -> JsonData -> Maybe JsonData
lookupObj k (JsonObject kvs) = (M.lookup k (M.fromList kvs))
lookupObj _ _ = error "lookupObj must be used on JsonObject"

lookupObj' :: String -> JsonData -> JsonData
lookupObj' k (JsonObject kvs) = (fromMaybe JsonNull (M.lookup k (M.fromList kvs)))
lookupObj' _ _ = error "lookupObj' must be used on JsonObject"

class ShowRef a where
    showRef :: a -> String

instance ShowRef [Char] where
    showRef s = s

instance ShowRef () where
    showRef () = "$"

class ShowAlternative a where
    showAlternative :: a -> String

instance ShowAlternative ChoiceMaker where
    showAlternative _ = "|"

instance ShowAlternative () where
    showAlternative _ = "|?"

instance (ShowRef r, ShowAlternative c, Show tr') => Show (TyRep r p c tr') where
    show tr = case tr of
        Anything -> "Anything"
        Number -> "Number"
        Text -> "Text"
        Boolean -> "Boolean"
        Null -> "Null"
        ConstNumber n -> show n
        ConstText s -> show s
        ConstBoolean b -> show b
        Tuple Strict ts -> "(" ++ intercalate ", " (map show ts) ++ ")"
        Tuple Tolerant ts -> "(" ++ intercalate ", " (map show ts ++ ["*"]) ++ ")"
        Array t -> "Array<" ++ show t ++ ">"
        NamedTuple Strict ps -> "{" ++ intercalate ", " [showIdentifier k ++ ": " ++ show t | (k, t) <- ps] ++ "}"
        NamedTuple Tolerant ps -> "{" ++ intercalate ", " ([showIdentifier k ++ ": " ++ show t | (k, t) <- ps] ++ ["*"]) ++ "}"
        TextMap t -> "Map<" ++ show t ++ ">"
        Ref name -> showRef name
        Refined t _ -> "Refined<" ++ show t ++ ">"
        Alternative a b c -> "(" ++ show a ++ bar ++ show b ++ ")" where
            bar = " " ++ showAlternative c ++ " "

instance {-# Overlapping #-} (ShowRef r, ShowAlternative c) => Show (Fix (TyRep r p c)) where
    show (Fix tr) = show tr

instance Show JsonData where
    show dat = case dat of
        JsonNumber x -> show x
        JsonText s -> show s
        JsonBoolean b -> show b
        JsonNull -> "null"
        JsonArray xs -> "[" ++ intercalate ", " (map show xs) ++ "]"
        JsonObject ps -> "{" ++ intercalate ", " [showIdentifier k ++ ": " ++ show v | (k, v) <- ps] ++ "}"

class QuadFunctor f where
    quadmap :: (a -> a') -> (b -> b') -> (c -> c') -> (d -> d') -> f a b c d -> f a' b' c' d'
    quadmap1 :: (a -> a') -> f a b c d -> f a' b c d
    quadmap2 :: (b -> b') -> f a b c d -> f a b' c d
    quadmap3 :: (c -> c') -> f a b c d -> f a b c' d
    quadmap4 :: (d -> d') -> f a b c d -> f a b c d'

    quadmap1 f = quadmap f id id id
    quadmap2 f = quadmap id f id id
    quadmap3 f = quadmap id id f id
    quadmap4 f = quadmap id id id f

instance QuadFunctor TyRep where
    quadmap f1 f2 f3 f4 tr = case tr of
        Anything -> Anything
        Number -> Number
        Text -> Text
        Boolean -> Boolean
        Null -> Null
        ConstNumber n -> ConstNumber n
        ConstText s -> ConstText s
        ConstBoolean b -> ConstBoolean b
        Tuple s ts -> Tuple s (map f4 ts)
        Array t -> Array (f4 t)
        NamedTuple s ps -> NamedTuple s [(k, f4 v) | (k, v) <- ps]
        TextMap t -> TextMap (f4 t)
        Ref name -> Ref (f1 name)
        Refined t p -> Refined (f4 t) (f2 p)
        Alternative t1 t2 c -> Alternative (f4 t1) (f4 t2) (f3 c)

instance Functor (TyRep r p c) where
    fmap = quadmap4

instance Foldable (TyRep r p c) where
    foldMap f tr = case tr of
        Tuple s ts -> foldMap f ts
        Array t -> f t
        NamedTuple s ps -> foldMap (f . snd) ps
        TextMap t -> f t
        Refined t _ -> f t
        Alternative t1 t2 _ -> f t1 `mappend` f t2
        _ -> mempty

instance Traversable (TyRep r p c) where
    traverse f tr = case tr of
        Anything -> pure Anything
        Number -> pure Number
        Text -> pure Text
        Boolean -> pure Boolean
        Null -> pure Null
        ConstNumber n -> pure $ ConstNumber n
        ConstText s -> pure $ ConstText s
        ConstBoolean b -> pure $ ConstBoolean b
        Ref name -> pure $ Ref name
        Tuple s ts -> Tuple s <$> (traverse f ts)
        Array t -> Array <$> f t
        NamedTuple s ps -> NamedTuple s <$> sequenceA [(k,) <$> f v | (k, v) <- ps]
        TextMap t -> TextMap <$> f t
        Refined t p -> Refined <$> f t <*> pure p
        Alternative t1 t2 c -> Alternative <$> (f t1) <*> (f t2) <*> pure c

-- toShape

toShape :: Env (Fix (TyRep Name p c)) -> (Fix (TyRep Name p' c')) -> Shape
toShape env sp = evalState (cataM g sp) S.empty where
    g :: TyRep Name p'' c'' Shape -> State (S.Set Name) Shape
    g tr = case tr of
        Ref name -> do
            --traceM ("name: " ++ name)
            visd <- get
            if name `S.member` visd
            then pure (Fix Anything)
            else do
                modify (S.insert name)
                r <- cataM g (env M.! name)
                modify (S.delete name)
                return r
        Refined t _ -> pure t
        Alternative t1 t2 _ -> pure (Fix $ Alternative t1 t2 ())
        t -> pure (Fix $ quadmap (const ()) (const ()) (const ()) id t)

-- checkSpec

data CheckFailedReason =
      ExistOverlappingOr CSpec CSpec JsonData
    | ExistMayOverlappingOr CSpec CSpec JsonData
    | InvalidItemInEnv Name CheckFailedReason
    deriving (Show)

instance MultilingualShow CheckFailedReason where
    showEnWith _ = show

wrapL :: (a -> a) -> Either a b -> Either a b
wrapL f e = case e of Left x -> Left (f x); Right y -> Right y

checkSpec :: Env Spec -> Spec -> Either CheckFailedReason CSpec
checkSpec env = cataM f where
    f :: TyRep Name DecProp () CSpec -> Either CheckFailedReason CSpec
    f (Alternative a b ()) = do
        case shapeOverlap (toShape env a) (toShape env b) of
            (NonOverlapping c) -> Right (Fix $ Alternative a b c)
            (Overlapping d) -> Left (ExistOverlappingOr a b d)
            (MayOverlapping d) -> Left (ExistMayOverlappingOr a b d)
    f tr = Right (Fix (quadmap3 undefined tr))

checkEnv :: Env Spec -> Either CheckFailedReason (Env CSpec)
checkEnv env = M.fromList <$> sequence [(k,) <$> wrapL (InvalidItemInEnv k) (checkSpec env sp) | (k, sp) <- M.toList env]

matchNull :: Shape -> Bool
matchNull (Fix tr) = case tr of
    Null -> True
    Anything -> True
    Alternative t1 t2 _ -> matchNull t1 || matchNull t2
    _ -> False

data ShapeRelation =
      Overlapping JsonData
    | MayOverlapping JsonData
    | NonOverlapping ChoiceMaker

joinTupleComponents :: [(ShapeRelation, MatchChoice)] -> ShapeRelation
joinTupleComponents [] = Overlapping (JsonArray [])
joinTupleComponents ((r, onIndexOutOfRange):rs) = case (r, joinTupleComponents rs) of
    (Overlapping d1, Overlapping (JsonArray ds)) -> Overlapping (JsonArray (d1:ds))
    (Overlapping d1, MayOverlapping (JsonArray ds)) -> MayOverlapping (JsonArray (d1:ds))
    (MayOverlapping d1, Overlapping (JsonArray ds)) -> MayOverlapping (JsonArray (d1:ds))
    (MayOverlapping d1, MayOverlapping (JsonArray ds)) -> MayOverlapping (JsonArray (d1:ds))
    (_, NonOverlapping c2) -> NonOverlapping (\d -> case d of
        (JsonArray (x:xs)) -> c2 (JsonArray xs)
        (JsonArray []) -> onIndexOutOfRange
        _ -> MatchNothing)
    (NonOverlapping c1, _) -> NonOverlapping (\d -> case d of
        (JsonArray (x:xs)) -> c1 x
        (JsonArray []) -> onIndexOutOfRange
        _ -> MatchNothing)

joinObjectComponents :: [(String, ShapeRelation, MatchChoice)] -> ShapeRelation
joinObjectComponents [] = Overlapping (JsonObject [])
joinObjectComponents ((k, r, onKeyNotExist):ps) = case (r, joinObjectComponents ps) of
    (Overlapping v1, Overlapping (JsonObject kvs)) -> Overlapping (JsonObject ((k,v1):kvs))
    (Overlapping v1, MayOverlapping (JsonObject kvs)) -> MayOverlapping (JsonObject ((k,v1):kvs))
    (MayOverlapping v1, Overlapping (JsonObject kvs)) -> MayOverlapping (JsonObject ((k,v1):kvs))
    (MayOverlapping v1, MayOverlapping (JsonObject kvs)) -> MayOverlapping (JsonObject ((k,v1):kvs))
    (_, NonOverlapping c2) -> NonOverlapping (\d -> case d of (JsonObject _) -> c2 d; _ -> MatchNothing) -- note that not remove k is correct
    (NonOverlapping c1, _) -> NonOverlapping (\d -> case d of (JsonObject _) -> maybe onKeyNotExist c1 (lookupObj k d); _ -> MatchNothing)

joinLeftOrPath :: ShapeRelation -> ShapeRelation -> ShapeRelation
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

joinRightOrPath :: ShapeRelation -> ShapeRelation -> ShapeRelation
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


notNullPrefix :: Strictness -> [Shape] -> [Shape]
{-# INLINE notNullPrefix #-}
notNullPrefix s = if s == Strict then id else reverse . dropWhile matchNull . reverse

pad :: Strictness -> [Shape] -> [Shape]
{-# INLINE pad #-}
pad s ts = if s == Strict then ts else ts ++ repeat (Fix Anything)

shapeOverlap :: Shape -> Shape -> ShapeRelation
shapeOverlap shape1@(Fix tr1) shape2@(Fix tr2) = case (tr1, tr2) of
    (Tuple s1 ts1, Tuple s2 ts2) ->
        let (l1, l2, l1', l2') = (length ts1, length ts2, length (notNullPrefix s1 ts1), length (notNullPrefix s2 ts2))
            joinCommonParts = joinTupleComponents $ do
                (i, (t1, t2)) <- zip [0..(max l1 l2)] $ zip (pad s1 ts1) (pad s2 ts2)
                let onIndexOutOfRange = (if s1 == Tolerant && matchNull t1 && i >= l1' then MatchLeft else if s2 == Tolerant && matchNull t2 && i >= l2' then MatchRight else MatchNothing)
                pure (shapeOverlap t1 t2, onIndexOutOfRange)
        in case (s1, s2) of
            (Strict, Strict) ->
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
                    joinCommonParts
            (Strict, Tolerant) ->
                if l1 < l2' then
                    NonOverlapping (\d -> case d of (JsonArray xs) -> if length xs > l1 then MatchRight else MatchLeft; _ -> MatchNothing)
                else
                    joinCommonParts
            (Tolerant, Strict) ->
                if l1' > l2 then
                    NonOverlapping (\d -> case d of (JsonArray xs) -> if length xs > l2 then MatchLeft else MatchRight; _ -> MatchNothing)
                else
                    joinCommonParts
            (Tolerant, Tolerant) ->
                joinCommonParts
    (Tuple s1 ts1, Array t2) ->
        joinTupleComponents (zip (zipWith shapeOverlap (notNullPrefix s1 ts1) (repeat t2)) (repeat MatchRight))
    (Array t1, Tuple s2 ts2) ->
        joinTupleComponents (zip (zipWith shapeOverlap (repeat t1) (notNullPrefix s2 ts2)) (repeat MatchLeft))
    (Array t1, Array t2) ->
        Overlapping (JsonArray []) -- trivial case
    (NamedTuple s1 ps1, NamedTuple s2 ps2) ->
        let (common, fstOnly, sndOnly) = compareSortedListWith fst (sortWith fst ps1) (sortWith fst ps2)
            joinCommonParts = joinObjectComponents $ do
                ((k, t1), (_, t2)) <- common
                let onKeyNotExist = (if s1 == Tolerant && matchNull t1 then MatchLeft else if s2 == Tolerant && matchNull t2 then MatchRight else MatchNothing)
                pure (k, shapeOverlap t1 t2, onKeyNotExist)
        in case (s1, s2) of
            (Strict, Strict) ->
                if not (null fstOnly) then
                    let k = fst (head fstOnly)
                    in NonOverlapping (\d -> case d of (JsonObject _) -> if isJust (lookupObj k d) then MatchLeft else MatchRight; _ -> MatchNothing)
                else if not (null sndOnly) then
                    let k = fst (head sndOnly)
                    in NonOverlapping (\d -> case d of (JsonObject _) -> if isJust (lookupObj k d) then MatchRight else MatchLeft; _ -> MatchNothing)
                else joinCommonParts
            (Strict, Tolerant) ->
                if not (null (filter (not . matchNull . snd) sndOnly)) then
                    let k = fst (head (filter (not . matchNull . snd) sndOnly))
                    in NonOverlapping (\d -> case d of (JsonObject _) -> if isJust (lookupObj k d) then MatchRight else MatchLeft; _ -> MatchNothing)
                else
                    case joinCommonParts of
                        Overlapping d -> Overlapping (extendObj d (example (Fix $ NamedTuple Strict fstOnly)))
                        MayOverlapping d -> MayOverlapping (extendObj d (example (Fix $ NamedTuple Strict fstOnly)))
                        NonOverlapping c -> NonOverlapping c
            (Tolerant, Strict) ->
                if not (null (filter (not . matchNull . snd) fstOnly)) then
                    let k = fst (head (filter (not . matchNull . snd) fstOnly))
                    in NonOverlapping (\d -> case d of (JsonObject _) -> if isJust (lookupObj k d) then MatchLeft else MatchRight; _ -> MatchNothing)
                else
                    case joinCommonParts of
                        Overlapping d -> Overlapping (extendObj d (example (Fix $ NamedTuple Strict sndOnly)))
                        MayOverlapping d -> MayOverlapping (extendObj d (example (Fix $ NamedTuple Strict sndOnly)))
                        NonOverlapping c -> NonOverlapping c
            (Tolerant, Tolerant) ->
                case joinCommonParts of
                    Overlapping d -> Overlapping (extendObj d (example (Fix $ NamedTuple Strict (fstOnly ++ sndOnly))))
                    MayOverlapping d -> MayOverlapping (extendObj d (example (Fix $ NamedTuple Strict (fstOnly ++ sndOnly))))
                    NonOverlapping c -> NonOverlapping c
    (NamedTuple s1 ps1, TextMap t2) ->
        joinObjectComponents [(k, shapeOverlap t1 t2, MatchRight) | (k, t1) <- ps1, s1 == Strict || not (matchNull t1)]
    (TextMap t1, NamedTuple s2 ps2) ->
        joinObjectComponents [(k, shapeOverlap t1 t2, MatchLeft) | (k, t2) <- ps2, s2 == Strict || not (matchNull t2)]
    (TextMap t1, TextMap t2) ->
        Overlapping (JsonObject []) -- trivial case
    (Alternative t1 t2 _, t3) ->
        joinLeftOrPath (shapeOverlap t1 (Fix t3)) (shapeOverlap t2 (Fix t3))
    (t1, Alternative t2 t3 _) ->
        joinRightOrPath (shapeOverlap (Fix t1) t2) (shapeOverlap (Fix t1) t3)
    (Anything, t) -> Overlapping (example (Fix t)) -- trivial case
    (t, Anything) -> Overlapping (example (Fix t)) -- trivial case
    (Refined _ _, _) ->
        error "shapeOverlap cannot process Refined"
    (_, Refined _ _) ->
        error "shapeOverlap cannot process Refined"
    (Ref _, _) ->
        error "shapeOverlap cannot process Ref"
    (_, Ref _) ->
        error "shapeOverlap cannot process Ref"
    _ -> --NOTE: these trivial cases, depending on matchOutline, it's correctness is subtle.
        if matchOutline' tr2 (example shape1) then Overlapping (example shape1)
        else if matchOutline' tr1 (example shape2) then Overlapping (example shape2)
        else NonOverlapping $ \d -> if (matchOutline' tr1 d) then MatchLeft else if (matchOutline' tr2 d) then MatchRight else MatchNothing

-- matchSpec

data MatchResult = Matched | UnMatched UnMatchedReason deriving (Show)
data UnMatchedReason = DirectCause DirectUMR CSpec JsonData | StepCause StepUMR UnMatchedReason deriving (Show)

instance Eq MatchResult where
    a == b = case (a, b) of (Matched, Matched) -> True; (UnMatched _, UnMatched _) -> True; _ -> False

data DirectUMR =
      OutlineNotMatch
    | ConstValueNotEqual
    | TupleLengthNotEqual
    | NamedTupleKeySetNotEqual
    | RefinedPropNotMatch --TODO: add prop description sentence
    | OrMatchNothing
    deriving (Show, Eq, Ord)

data StepUMR =
      TupleFieldNotMatch Int
    | ArrayElementNotMatch Int
    | NamedTupleFieldNotMatch String
    | TextMapElementNotMatch String
    | RefinedShapeNotMatch
    | OrNotMatchLeft
    | OrNotMatchRight
    | RefNotMatch Name
    deriving (Show, Eq, Ord)

isIdentifier :: String -> Bool
isIdentifier s = not (null s) && all isAlphaNum s

showIdentifier :: String -> String
showIdentifier s = if isIdentifier s then s else show s

explain :: UnMatchedReason -> (DirectUMR, CSpec, JsonData, String, String)
explain reason = iter reason undefined [] where
    iter reason dc path = case reason of
        DirectCause dr sp d -> (dr, sp, d, concatMap specAccessor path, concatMap dataAccessor path)
        StepCause sr r -> iter r dc (path ++ [sr])

    specAccessor r = case r of
        TupleFieldNotMatch i -> "(" ++ show i ++ ")"
        ArrayElementNotMatch i -> "[" ++ show i ++ "]"
        NamedTupleFieldNotMatch k -> "(" ++ show k ++ ")"
        TextMapElementNotMatch k -> "[" ++ show k ++ "]"
        RefinedShapeNotMatch -> "<refined>"
        OrNotMatchLeft -> "<left>"
        OrNotMatchRight -> "<right>"
        RefNotMatch name -> "{" ++ name ++ "}"

    dataAccessor r = case r of
        TupleFieldNotMatch i -> "[" ++ show i ++ "]"
        ArrayElementNotMatch i -> "[" ++ show i ++ "]"
        NamedTupleFieldNotMatch k -> (if isIdentifier k then "." ++ k else "[" ++ show k ++ "]")
        TextMapElementNotMatch k -> "[" ++ show k ++ "]"
        _ -> ""

instance MultilingualShow UnMatchedReason where
    showEnWith _ r =
        let (direct, sp, d, specPath, dataPath) = explain r
        in "  Abstract: it" ++ dataPath ++ " should be a " ++ show sp ++ ", but got " ++ show d ++
            "\n  Direct Cause: " ++ show direct ++
            "\n    Spec: " ++ show sp ++
            "\n    Data: " ++ show d ++
            "\n  Spec Path: " ++ specPath ++
            "\n  Data Path: " ++ dataPath
    showZhWith _ r =
        let (direct, sp, d, specPath, dataPath) = explain r
        in "  摘要: it" ++ dataPath ++ " 应该是一个 " ++ show sp ++ ", 但这里是 " ++ show d ++
            "\n  直接原因: " ++ show direct ++
            "\n    规格: " ++ show sp ++
            "\n    数据: " ++ show d ++
            "\n  规格路径: " ++ specPath ++
            "\n  数据路径: " ++ dataPath

instance MultilingualShow MatchResult where
    showEnWith f mr = case mr of Matched -> "Matched"; (UnMatched r) -> "UnMatched !\n" ++ f r

otherwise :: Bool -> UnMatchedReason -> MatchResult
b `otherwise` reason = if b then Matched else UnMatched reason

wrap :: StepUMR -> MatchResult -> MatchResult
wrap step rst = case rst of Matched -> Matched; UnMatched reason -> UnMatched (StepCause step reason)

instance Semigroup MatchResult where
    (<>) Matched Matched = Matched
    (<>) Matched r2 = r2
    (<>) r1 _ = r1

instance Monoid MatchResult where
    mempty = Matched
    mappend = (<>)

isPrimTyRep :: TyRep r p c tr' -> Bool
isPrimTyRep tr = case tr of
    Anything -> True
    Number -> True
    Text -> True
    Boolean -> True
    Null -> True
    ConstNumber n -> True
    ConstText s -> True
    ConstBoolean b -> True
    _ -> False

-- | shadow matching, only process trivial cases
matchOutline :: TyRep r p c tr' -> JsonData -> Maybe DirectUMR
matchOutline tr d = case (tr, d) of
    (Anything, _) -> Nothing
    (Number, (JsonNumber _)) -> Nothing
    (Text, (JsonText _)) -> Nothing
    (Boolean, (JsonBoolean _)) -> Nothing
    (Null, JsonNull) -> Nothing
    (ConstNumber n, d@(JsonNumber n')) -> if (n == n') then Nothing else Just ConstValueNotEqual
    (ConstText s, d@(JsonText s')) -> if (s == s') then Nothing else Just ConstValueNotEqual
    (ConstBoolean b, d@(JsonBoolean b')) -> if (b == b') then Nothing else Just ConstValueNotEqual
    (Tuple _ _, (JsonArray _)) -> Nothing
    (Array _, (JsonArray _)) -> Nothing
    (NamedTuple _ _, (JsonObject _)) -> Nothing
    (TextMap _, (JsonObject _)) -> Nothing
    (Refined t _, d) -> error "matchOutline can not process with Refined"
    (Ref _, _) -> error "matchOutline can not process with Ref"
    (Alternative _ _ _, _) -> error "matchOutline can not process with Alternative"
    _ -> Just OutlineNotMatch

matchOutline' :: TyRep r p c tr' -> JsonData -> Bool
matchOutline' tr d = maybe True (const False) (matchOutline tr d)

matchSpec :: Env CSpec -> CSpec -> JsonData -> MatchResult
matchSpec env spec@(Fix t) d = let rec = matchSpec env in case (t, d) of
    (Tuple Strict ts, d@(JsonArray xs)) ->
        (let l1 = length ts; l2 = length xs in (l1 == l2) `otherwise` (DirectCause TupleLengthNotEqual spec d)) <>
        fold [wrap (TupleFieldNotMatch i) (rec t x) | (i, t, x) <- zip3 [0..] ts xs]
    (Tuple Tolerant ts, d@(JsonArray xs)) ->
        fold [wrap (TupleFieldNotMatch i) (rec t x) | (i, t, x) <- zip3 [0..] ts (xs ++ repeat JsonNull)]
    (Array t, (JsonArray xs)) -> fold [wrap (ArrayElementNotMatch i) (rec t x) | (i, x) <- zip [0..] xs]
    (NamedTuple Strict ps, d@(JsonObject kvs)) ->
        (setEq (map fst ps) (map fst kvs) `otherwise` (DirectCause NamedTupleKeySetNotEqual spec d)) <>
        fold [wrap (NamedTupleFieldNotMatch k) (rec t (lookupObj' k d)) | (k, t) <- ps]
    (NamedTuple Tolerant ps, d@(JsonObject kvs)) ->
        fold [wrap (NamedTupleFieldNotMatch k) (rec t (lookupObj' k d)) | (k, t) <- ps]
    (TextMap t, (JsonObject kvs)) -> fold [wrap (TextMapElementNotMatch k) (rec t v) | (k, v) <- kvs]
    (t@(Refined t1 p), d) -> wrap RefinedShapeNotMatch (rec t1 d) <> (testProp p d `otherwise` (DirectCause RefinedPropNotMatch spec d))
    (t@(Alternative t1 t2 makeChoice), d) -> case makeChoice d of
        MatchLeft -> wrap OrNotMatchLeft (rec t1 d)
        MatchRight -> wrap OrNotMatchRight (rec t2 d)
        MatchNothing -> UnMatched (DirectCause OrMatchNothing spec d)
    (Ref name, d) -> wrap (RefNotMatch name) (rec (env M.! name) d) -- NOTICE: can fail if name not in env
    (t, d) -> maybe Matched (\c -> UnMatched (DirectCause c spec d)) (matchOutline t d)

matchSpec' :: Env CSpec -> CSpec -> JsonData -> Bool
matchSpec' env t d = case (matchSpec env t d) of Matched -> True; _ -> False

tryMatchSpec :: Env Spec -> Spec -> JsonData -> Either CheckFailedReason MatchResult
tryMatchSpec env sp d = ((,) <$> checkEnv env <*> checkSpec env sp) >>= (\(env', sp') -> pure (matchSpec env' sp' d))

tryMatchSpec' = tryMatchSpec M.empty

-- everywhereJ

everywhereJ :: Monad m => Env CSpec -> CSpec -> Name -> (JsonData -> m JsonData) -> (JsonData -> m JsonData)
everywhereJ env spec name g dat = rec spec dat where
    rec (Fix tr) dat = case (tr, dat) of
        (Tuple _ ts, (JsonArray xs)) -> (JsonArray <$> sequence [rec t x | (t, x) <- zip ts xs]) >>= g
        (Array t, (JsonArray xs)) -> (JsonArray <$> sequence [rec t x | x <- xs]) >>= g
        (NamedTuple _ ps, d@(JsonObject _)) -> (JsonObject <$> sequence [(k,) <$> rec t (lookupObj' k d) | (k, t) <- ps]) >>= g --NOTE: use everywhereJ will remove redundant keys
        (TextMap t, (JsonObject kvs)) -> (JsonObject <$> sequence [(k,) <$> rec t v | (k, v) <- kvs]) >>= g
        (Refined t _, d) -> rec t d
        (Alternative t1 t2 makeChoice, d) -> case makeChoice d of
            MatchLeft -> rec t1 d
            MatchRight -> rec t2 d
            MatchNothing -> error "everywhereJ not used correctly (1)"
        (Ref name', d) -> let t = env M.! name in if name' == name then rec t d >>= g else rec t d
        (t, d) -> if matchOutline' t d then pure d else error "everywhereJ not used correctly (2)"

-- test

testAJ = print "type checked"

