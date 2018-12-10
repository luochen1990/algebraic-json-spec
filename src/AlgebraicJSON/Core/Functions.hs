-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

{-# language TupleSections #-}
{-# language RankNTypes #-}

module AlgebraicJSON.Core.Functions (
    checkSpec, checkEnv, checkAlternative, CheckFailedReason(..),
    matchSpec, tryMatchSpec,
    everywhereJ,
    shapeOverlap, ShapeRelation(..), Sureness(..), -- export for test
) where

--import Debug.Trace
import Prelude hiding (otherwise)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Semigroup
import Data.Foldable (fold, foldMap)
import Data.List (partition)
import Data.Maybe
import Data.Fix
import Text.MultilingualShow
import Control.Monad.State
import GHC.Exts (sortWith)
import AlgebraicJSON.Core.Tools
import AlgebraicJSON.Core.Definitions

------------------- ShapeRelation & shapeOverlap --------------------

-- | the overlapping relation of two Shape
data ShapeRelation =
      Overlapping Sureness JsonData -- sometimes we cannot be sure, since there are Refined node.
    | NonOverlapping ChoiceMaker
    deriving (Show)

data Sureness = Sure | Unsure deriving (Show, Eq)

shapeOverlap :: Shape -> Shape -> ShapeRelation
shapeOverlap shape1@(Fix tr1) shape2@(Fix tr2) = case (tr1, tr2) of
    (Tuple s1 ts1, Tuple s2 ts2) ->
        let (l1, l2, l1', l2') = (length ts1, length ts2, length (notNullPrefix s1 ts1), length (notNullPrefix s2 ts2))
            joinCommonParts = joinTupleComponents $ do
                (i, (t1, t2)) <- zip [0..(max l1 l2)] $ zip (pad s1 ts1) (pad s2 ts2)
                let onIndexOutOfRange = (if s1 == Tolerant && acceptNull t1 && i >= l1' then MatchLeft else if s2 == Tolerant && acceptNull t2 && i >= l2' then MatchRight else MatchNothing)
                pure (shapeOverlap t1 t2, onIndexOutOfRange)
        in case (s1, s2) of
            (Strict, Strict) ->
                if l1 /= l2 then NonOverlapping (ViaArrayLength l1 l2)
                else joinCommonParts
            (Strict, Tolerant) ->
                if l1 < l2' then NonOverlapping (ViaArrayLengthGT l1 MatchRight)
                else joinCommonParts
            (Tolerant, Strict) ->
                if l1' > l2 then NonOverlapping (ViaArrayLengthGT l2 MatchLeft)
                else joinCommonParts
            (Tolerant, Tolerant) ->
                joinCommonParts
    (Tuple s1 ts1, Array t2) ->
        let s = sureness shape1 <> sureness shape2
        in blurWith s $ joinTupleComponents (zip (zipWith shapeOverlap (notNullPrefix s1 ts1) (repeat t2)) (repeat MatchRight))
    (Array t1, Tuple s2 ts2) ->
        let s = sureness shape1 <> sureness shape2
        in blurWith s $ joinTupleComponents (zip (zipWith shapeOverlap (repeat t1) (notNullPrefix s2 ts2)) (repeat MatchLeft))
    (Array t1, Array t2) ->
        Overlapping Sure (JsonArray []) -- trivial case
    (NamedTuple s1 ps1, NamedTuple s2 ps2) ->
        let (common, fstOnly, sndOnly) = compareSortedListWith fst (sortWith fst ps1) (sortWith fst ps2)
            joinCommonParts = joinObjectComponents $ do
                ((k, t1), (_, t2)) <- common
                let onKeyNotExist = (if s1 == Tolerant && acceptNull t1 then MatchLeft else if s2 == Tolerant && acceptNull t2 then MatchRight else MatchNothing)
                pure (k, shapeOverlap t1 t2, onKeyNotExist)
        in case (s1, s2) of
            (Strict, Strict) ->
                if not (null fstOnly) then
                    let k = fst (head fstOnly)
                    in NonOverlapping (ViaObjectHasKey k MatchLeft)
                else if not (null sndOnly) then
                    let k = fst (head sndOnly)
                    in NonOverlapping (ViaObjectHasKey k MatchRight)
                else joinCommonParts
            (Strict, Tolerant) ->
                let (psMayNull, psNotNull) = partition (acceptNull . snd) sndOnly in
                if not (null psNotNull) then
                    let k = fst (head psNotNull) in NonOverlapping (ViaObjectHasKey k MatchRight)
                else
                    blurWith (foldMap (sureness . snd) psMayNull) (extendOverlappingEvidenceObj fstOnly joinCommonParts)
            (Tolerant, Strict) ->
                let (psMayNull, psNotNull) = partition (acceptNull . snd) fstOnly in
                if not (null psNotNull) then
                    let k = fst (head psNotNull) in NonOverlapping (ViaObjectHasKey k MatchLeft)
                else
                    blurWith (foldMap (sureness . snd) psMayNull) (extendOverlappingEvidenceObj sndOnly joinCommonParts)
            (Tolerant, Tolerant) ->
                extendOverlappingEvidenceObj (fstOnly ++ sndOnly) joinCommonParts
    (NamedTuple s1 ps1, TextMap t2) ->
        let s = sureness shape1 <> sureness shape2
        in blurWith s $ joinObjectComponents [(k, shapeOverlap t1 t2, MatchRight) | (k, t1) <- ps1, s1 == Strict || not (acceptNull t1)]
    (TextMap t1, NamedTuple s2 ps2) ->
        let s = sureness shape1 <> sureness shape2
        in blurWith s $ joinObjectComponents [(k, shapeOverlap t1 t2, MatchLeft) | (k, t2) <- ps2, s2 == Strict || not (acceptNull t2)]
    (TextMap t1, TextMap t2) ->
        Overlapping Sure (JsonObject []) -- trivial case
    (Alternative t1 t2 _, t3) ->
        joinLeftOrPath (shapeOverlap t1 (Fix t3)) (shapeOverlap t2 (Fix t3))
    (t1, Alternative t2 t3 _) ->
        joinRightOrPath (shapeOverlap (Fix t1) t2) (shapeOverlap (Fix t1) t3)
    (Refined t1 _, t2) -> blur (shapeOverlap t1 (Fix t2)) -- Refined condition is treated as blackbox
    (t1, Refined t2 _) -> blur (shapeOverlap (Fix t1) t2) -- Refined condition is treated as blackbox
    (Ref _, t) -> Overlapping Unsure (example (Fix t)) -- Ref () is treated as blackbox
    (t, Ref _) -> Overlapping Unsure (example (Fix t)) -- Ref () is treated as blackbox
    (Anything, t) -> Overlapping (sureness (Fix t)) (example (Fix t))
    (t, Anything) -> Overlapping (sureness (Fix t)) (example (Fix t))
    _ -> --NOTE: these trivial cases, depending on matchOutline, it's correctness is subtle.
        if matchOutline tr2 (example shape1) then Overlapping Sure (example shape1)
        else if matchOutline tr1 (example shape2) then Overlapping Sure (example shape2)
        else NonOverlapping (ViaOutline tr1 tr2)

--------------- trivial things used in shapeOverlap -----------------

instance Semigroup Sureness where
    (<>) = mappend

instance Monoid Sureness where
    mempty = Sure
    mappend Sure Sure = Sure
    mappend _ _ = Unsure

sureness :: Shape -> Sureness
sureness sh = if isDeterminateShape sh then Sure else Unsure

-- | change Sure to s when Overlapping
blurWith :: Sureness -> ShapeRelation -> ShapeRelation
blurWith s sr = case sr of Overlapping Sure d -> Overlapping s d; _ -> sr

-- | change Sure to Unsure when Overlapping
blur :: ShapeRelation -> ShapeRelation
blur = blurWith Unsure

extendOverlappingEvidenceObj :: [(String, Shape)] -> ShapeRelation -> ShapeRelation
extendOverlappingEvidenceObj ps sr = case sr of
    Overlapping s d -> let sh' = (Fix $ NamedTuple Strict ps) in Overlapping (s <> sureness sh') (extendObj d (example sh'))
    NonOverlapping c -> NonOverlapping c

notNullPrefix :: Strictness -> [Shape] -> [Shape]
{-# INLINE notNullPrefix #-}
notNullPrefix s = if s == Strict then id else reverse . dropWhile acceptNull . reverse

pad :: Strictness -> [Shape] -> [Shape]
{-# INLINE pad #-}
pad s ts = if s == Strict then ts else ts ++ repeat (Fix Anything)

joinTupleComponents :: [(ShapeRelation, MatchChoice)] -> ShapeRelation
joinTupleComponents [] = Overlapping Sure (JsonArray [])
joinTupleComponents ((r, onIndexOutOfRange):rs) = case (r, joinTupleComponents rs) of
    (Overlapping s1 d1, Overlapping s2 (JsonArray ds)) -> Overlapping (s1 <> s2) (JsonArray (d1:ds))
    (NonOverlapping c, _) -> NonOverlapping (ViaArrayElement 0 onIndexOutOfRange c)
    (_, NonOverlapping (ViaArrayElement i mc c')) -> NonOverlapping (ViaArrayElement (i+1) onIndexOutOfRange c')

joinObjectComponents :: [(String, ShapeRelation, MatchChoice)] -> ShapeRelation
joinObjectComponents [] = Overlapping Sure (JsonObject [])
joinObjectComponents ((k, r, onKeyNotExist):ps) = case (r, joinObjectComponents ps) of
    (Overlapping s1 v1, Overlapping s2 (JsonObject kvs)) -> Overlapping (s1 <> s2) (JsonObject ((k,v1):kvs))
    (NonOverlapping c, _) -> NonOverlapping (ViaObjectField k onKeyNotExist c)
    (_, NonOverlapping c) -> NonOverlapping c

-- | for the case (t1 | t2) | t3, name (shapeOverlap t1 t3) as r1, (shapeOverlap t2 t3) as r2
joinLeftOrPath :: ShapeRelation -> ShapeRelation -> ShapeRelation
joinLeftOrPath r1 r2 = case (r1, r2) of
    (Overlapping Sure d1, _) -> Overlapping Sure d1
    (_, Overlapping Sure d2) -> Overlapping Sure d2
    (Overlapping Unsure d1, _) -> Overlapping Unsure d1
    (_, Overlapping Unsure d2) -> Overlapping Unsure d2
    (NonOverlapping c13, NonOverlapping c23) -> NonOverlapping (ViaOrL c13 c23)

-- | for the case t1 | (t2 | t3), name (shapeOverlap t1 t2) as r1, (shapeOverlap t1 t3) as r2
joinRightOrPath :: ShapeRelation -> ShapeRelation -> ShapeRelation
joinRightOrPath r1 r2 = case (r1, r2) of
    (Overlapping Sure d1, _) -> Overlapping Sure d1
    (_, Overlapping Sure d2) -> Overlapping Sure d2
    (Overlapping Unsure d1, _) -> Overlapping Unsure d1
    (_, Overlapping Unsure d2) -> Overlapping Unsure d2
    (NonOverlapping c12, NonOverlapping c13) -> NonOverlapping (ViaOrR c12 c13)

----------------------- checkSpec & checkEnv ------------------------

-- | representation of the reason why we failed to check a Spec
data CheckFailedReason =
      ExistOverlappingOr Sureness CSpec CSpec JsonData
    | InvalidItemInEnv Name CheckFailedReason
    deriving (Show)

-- | check Spec to get CSpec
checkSpec :: Env Spec -> Spec -> Either CheckFailedReason CSpec
checkSpec env = cataM f where
    f :: TyRep Name DecProp () CSpec -> Either CheckFailedReason CSpec
    f (Alternative a b ()) = checkAlternative env a b
    f tr = Right (Fix (quadmap3 undefined tr))

checkAlternative :: forall p c. Env (Fix (TyRep Name p c)) -> CSpec -> CSpec -> Either CheckFailedReason CSpec
checkAlternative env a b = case shapeOverlap (toShape env a) (toShape env b) of
    (NonOverlapping c) -> Right (Fix $ Alternative a b c)
    (Overlapping s d) -> Left (ExistOverlappingOr s a b d)

-- | check (Env Spec) to get (Env CSpec)
checkEnv :: Env Spec -> Either CheckFailedReason (Env CSpec)
checkEnv env = M.fromList <$> sequence [(k,) <$> wrapL (InvalidItemInEnv k) (checkSpec env sp) | (k, sp) <- M.toList env]

wrapL :: (a -> a) -> Either a b -> Either a b
wrapL f e = case e of Left x -> Left (f x); Right y -> Right y

--------------------------- matchSpec -------------------------------

-- | match CSpec and JsonData
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
    (t@(Alternative t1 t2 c), d) -> case makeChoice c d of
        MatchLeft -> wrap OrNotMatchLeft (rec t1 d)
        MatchRight -> wrap OrNotMatchRight (rec t2 d)
        MatchNothing -> UnMatched (DirectCause OrMatchNothing spec d)
    (Ref name, d) -> wrap (RefNotMatch name) (rec (env M.! name) d) -- NOTICE: can fail if name not in env
    (t, d) -> if matchOutline t d then Matched else UnMatched (DirectCause OutlineNotMatch spec d)

-- | match Spec and JsonData
tryMatchSpec :: Env Spec -> Spec -> JsonData -> Either CheckFailedReason MatchResult
tryMatchSpec env sp d = ((,) <$> checkEnv env <*> checkSpec env sp) >>= (\(env', sp') -> pure (matchSpec env' sp' d))

---------------------------- everywhereJ ----------------------------

-- | a generic programming tool, similar to everywhereM in Haskell
everywhereJ :: Monad m => Env CSpec -> CSpec -> Name -> (JsonData -> m JsonData) -> (JsonData -> m JsonData)
everywhereJ env spec name g dat = rec spec dat where
    rec (Fix tr) dat = case (tr, dat) of
        (Tuple _ ts, (JsonArray xs)) -> (JsonArray <$> sequence [rec t x | (t, x) <- zip ts xs]) >>= g
        (Array t, (JsonArray xs)) -> (JsonArray <$> sequence [rec t x | x <- xs]) >>= g
        (NamedTuple _ ps, d@(JsonObject _)) -> (JsonObject <$> sequence [(k,) <$> rec t (lookupObj' k d) | (k, t) <- ps]) >>= g --NOTE: use everywhereJ will remove redundant keys
        (TextMap t, (JsonObject kvs)) -> (JsonObject <$> sequence [(k,) <$> rec t v | (k, v) <- kvs]) >>= g
        (Refined t _, d) -> rec t d
        (Alternative t1 t2 c, d) -> case makeChoice c d of
            MatchLeft -> rec t1 d
            MatchRight -> rec t2 d
            MatchNothing -> error "everywhereJ not used correctly (1)"
        (Ref name', d) -> let t = env M.! name in if name' == name then rec t d >>= g else rec t d
        (t, d) -> if matchOutline t d then pure d else error "everywhereJ not used correctly (2)"

