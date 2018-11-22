-- Copyright 2018 LuoChen (luochen1990@gmail.com). Licensed under the Apache License 2.0.

{-# language TupleSections #-}
{-# language RankNTypes #-}

import Debug.Trace
import Prelude hiding (otherwise)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Semigroup
import Data.Foldable (fold, foldMap)
import Data.List (intercalate)
import Data.Maybe
import Control.Monad.State
import GHC.Exts (sortWith)
--import Data.Generics.Schemes (everywhereM)
--import Data.Generics.Aliases (mkM)
--import Data.Typeable
--import Data.Data (Data)

-- generic tools

class MultilingualShow a where
    showEnWith, showZhWith :: (forall a'. MultilingualShow a' => a' -> String) -> (a -> String)
    showZhWith showPart = showEnWith showPart

    showEn, showZh :: a -> String
    showEn = showEnWith showEn
    showZh = showZhWith showZh

    printEn, printZh :: a -> IO ()
    printEn = putStrLn . showEn
    printZh = putStrLn . showZh

instance (MultilingualShow a, MultilingualShow b) => MultilingualShow (Either a b) where
    showEnWith f e = case e of Left x -> "Left " ++ f x; Right y -> "Right " ++ f y

compareSortedListWith :: Ord b => (a -> b) -> [a] -> [a] -> ([(a, a)], [a], [a])
compareSortedListWith key xs ys = iter xs ys [] [] [] where
    iter xs ys both onlyXs onlyYs = case (xs, ys) of
        ((x:xs'), (y:ys')) ->
            if key x == key y then iter xs' ys' ((x, y):both) onlyXs onlyYs
            else if key x < key y then iter xs' (y:ys') both (x:onlyXs) onlyYs
            else {- key x > key y -} iter (x:xs') ys' both onlyXs (y:onlyYs)
        ([], ys) -> (both, onlyXs, onlyYs ++ ys)
        (xs, []) -> (both, onlyXs ++ xs, onlyYs)

-- TypeRep & JsonData

type Spec = TypeRep -- without Alternative
type Shape = TypeRep -- without Alternative, Ref, Refined
type CheckedSpec = TypeRep -- without Or
-- subtyping relations:
--   Shape <: Spec
--   CheckedSpec <: Spec

data TypeRep =
      Anything
    | Number
    | Text
    | Boolean
    | Null
    | ConstNumber Double
    | ConstText String
    | ConstBoolean Bool
    | Tuple Strictness [TypeRep]
    | Array TypeRep
    | NamedTuple Strictness [(String, TypeRep)]
    | TextMap TypeRep
    | Refined TypeRep DecProp
    | Ref Name
    | Or TypeRep TypeRep
    | Alternative TypeRep TypeRep (JsonData -> MatchChoice)

type Name = String
data DecProp = DecProp {testProp :: JsonData -> Bool}
data MatchChoice = MatchLeft | MatchRight | MatchNothing deriving (Show, Eq, Ord)
data Strictness = Strict | Tolerant

data JsonData =
      JsonNumber Double
    | JsonText String
    | JsonBoolean Bool
    | JsonNull
    | JsonArray [JsonData]
    | JsonObject [(String, JsonData)]
    deriving (Eq, Ord)

type Env a = M.Map String a

-- useful tools

example :: Shape -> JsonData
example tr = case tr of
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
    Refined t _ -> error "Shape should not contain Refined"
    Ref name -> error "Shape should not contain Ref"
    Or a b -> error "Shape should not contain Or"
    Alternative a b _ -> example a

extendObj :: JsonData -> JsonData -> JsonData
extendObj (JsonObject ps1) (JsonObject ps2) = JsonObject (ps1 ++ ps2)
extendObj _ _ = error "extendObj must be used on two JsonObject"

lookupObj :: String -> JsonData -> JsonData
lookupObj k (JsonObject kvs) = (fromMaybe JsonNull (M.lookup k (M.fromList kvs)))
lookupObj _ _ = error "lookupObj must be used on JsonObject"

instance Show TypeRep where
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
        Tuple Tolerant ts -> "(" ++ intercalate ", " (map show ts) ++ ", *)"
        Array t -> "Array<" ++ show t ++ ">"
        NamedTuple Strict ps -> "{" ++ intercalate ", " [k ++ ": " ++ show t | (k, t) <- ps] ++ "}"
        NamedTuple Tolerant ps -> "{" ++ intercalate ", " [k ++ ": " ++ show t | (k, t) <- ps] ++ ", *}"
        TextMap t -> "Map<" ++ show t ++ ">"
        Refined t _ -> "Refined<" ++ show t ++ ">"
        Ref name -> name
        Or a b -> "(" ++ show a ++ " |? " ++ show b ++ ")"
        Alternative a b _ -> "(" ++ show a ++ " | " ++ show b ++ ")"

instance Show JsonData where
    show dat = case dat of
        JsonNumber x -> show x
        JsonText s -> show s
        JsonBoolean b -> show b
        JsonNull -> "null"
        JsonArray xs -> "[" ++ intercalate ", " (map show xs) ++ "]"
        JsonObject ps -> "{" ++ intercalate ", " [k ++ ": " ++ show v | (k, v) <- ps] ++ "}"

-- specialized version of everywhereM for TypeRep
everywhereMTR :: Monad m => (TypeRep -> m TypeRep) -> (TypeRep -> m TypeRep)
everywhereMTR g tr | isSimpleShape tr = g tr
everywhereMTR g tr = let rec = everywhereMTR g in case tr of
    Tuple s ts -> Tuple s <$> sequence (map rec ts) >>= g
    Array t -> Array <$> rec t >>= g
    NamedTuple s ps -> NamedTuple s <$> sequence [(k,) <$> (rec t) | (k, t) <- ps] >>= g
    TextMap t -> TextMap <$> rec t >>= g
    Refined t p -> Refined <$> rec t <*> pure p >>= g
    Ref name -> g (Ref name)
    Or a b -> Or <$> rec a <*> rec b >>= g
    Alternative a b c -> Alternative <$> rec a <*> rec b <*> pure c >>= g

-- toShape

toShape :: Env TypeRep -> TypeRep -> Shape
toShape env tr = evalState (everywhereMTR g tr) S.empty where
    g :: TypeRep -> State (S.Set Name) TypeRep
    g tr = case tr of
        Ref name -> do
            --traceM ("name: " ++ name)
            visd <- get
            if name `S.member` visd
            then pure Anything
            else do
                modify (S.insert name)
                r <- everywhereMTR g (env M.! name)
                modify (S.delete name)
                return r
        Refined t _ -> pure t
        Alternative t1 t2 _ -> pure (Or t1 t2)
        t -> pure t

-- checkSpec

data CheckFailedReason =
      ExistOverlappingOr Spec Spec JsonData
    | ExistMayOverlappingOr Spec Spec JsonData
    | InvalidItemInEnv Name CheckFailedReason
    deriving (Show)

instance MultilingualShow CheckFailedReason where
    showEnWith _ = show

wrapL :: (a -> a) -> Either a b -> Either a b
wrapL f e = case e of Left x -> Left (f x); Right y -> Right y

checkSpec :: Env Spec -> Spec -> Either CheckFailedReason CheckedSpec
checkSpec env = everywhereMTR f where
    f (Or a b) = do
        case shapeOverlap (toShape env a) (toShape env b) of
            (NonOverlapping c) -> Right (Alternative a b c)
            (Overlapping d) -> Left (ExistOverlappingOr a b d)
            (MayOverlapping d) -> Left (ExistMayOverlappingOr a b d)
    --f (Ref name) = wrapL (InvalidItemInEnv name) (checkSpec env (env M.! name))
    f spec = Right spec

checkEnv :: Env Spec -> Either CheckFailedReason (Env CheckedSpec)
checkEnv env = M.fromList <$> sequence [(k,) <$> wrapL (InvalidItemInEnv k) (checkSpec env sp) | (k, sp) <- M.toList env]

data ShapeRelation =
      Overlapping JsonData
    | MayOverlapping JsonData
    | NonOverlapping (JsonData -> MatchChoice)

joinTupleComponents :: [ShapeRelation] -> ShapeRelation
joinTupleComponents [] = Overlapping (JsonArray [])
joinTupleComponents (r:rs) = case (r, joinTupleComponents rs) of
    (Overlapping d1, Overlapping (JsonArray ds)) -> Overlapping (JsonArray (d1:ds))
    (Overlapping d1, MayOverlapping (JsonArray ds)) -> MayOverlapping (JsonArray (d1:ds))
    (MayOverlapping d1, Overlapping (JsonArray ds)) -> MayOverlapping (JsonArray (d1:ds))
    (MayOverlapping d1, MayOverlapping (JsonArray ds)) -> MayOverlapping (JsonArray (d1:ds))
    (_, NonOverlapping c2) -> NonOverlapping (\d -> case d of (JsonArray (x:xs)) -> c2 (JsonArray xs); _ -> MatchNothing)
    (NonOverlapping c1, _) -> NonOverlapping (\d -> case d of (JsonArray (x:xs)) -> c1 x; _ -> MatchNothing)

joinObjectComponents :: [(String, ShapeRelation)] -> ShapeRelation
joinObjectComponents [] = Overlapping (JsonObject [])
joinObjectComponents ((k, r):ps) = case (r, joinObjectComponents ps) of
    (Overlapping v1, Overlapping (JsonObject kvs)) -> Overlapping (JsonObject ((k,v1):kvs))
    (Overlapping v1, MayOverlapping (JsonObject kvs)) -> MayOverlapping (JsonObject ((k,v1):kvs))
    (MayOverlapping v1, Overlapping (JsonObject kvs)) -> MayOverlapping (JsonObject ((k,v1):kvs))
    (MayOverlapping v1, MayOverlapping (JsonObject kvs)) -> MayOverlapping (JsonObject ((k,v1):kvs))
    (_, NonOverlapping c2) -> NonOverlapping (\d -> case d of (JsonObject _) -> c2 d; _ -> MatchNothing) -- note that not remove k is correct
    (NonOverlapping c1, _) -> NonOverlapping (\d -> case d of (JsonObject _) -> c1 (lookupObj k d); _ -> MatchNothing)

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

shapeOverlap :: Shape -> Shape -> ShapeRelation
shapeOverlap tr1 tr2 = case (tr1, tr2) of
    (Tuple s1 ts1, Tuple s2 ts2) ->
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
                joinTupleComponents (zipWith shapeOverlap ts1 ts2)
    (Tuple _ ts1, Array t2) ->
        joinTupleComponents (zipWith shapeOverlap ts1 (repeat t2))
    (Array t1, Tuple _ ts2) ->
        joinTupleComponents (zipWith shapeOverlap (repeat t1) ts2)
    (Array t1, Array t2) ->
        Overlapping (JsonArray []) -- trivial case
    (NamedTuple s1 ps1, NamedTuple s2 ps2) ->
        -- NamedTuple is non-strict
        let (common, fstOnly, sndOnly) = compareSortedListWith fst (sortWith fst ps1) (sortWith fst ps2)
        in case joinObjectComponents [(k, shapeOverlap t1 t2) | ((k, t1), (_, t2)) <- common] of
            Overlapping d -> Overlapping (extendObj d (example (NamedTuple Strict (fstOnly ++ sndOnly))))
            MayOverlapping d -> MayOverlapping (extendObj d (example (NamedTuple Strict (fstOnly ++ sndOnly))))
            NonOverlapping c -> NonOverlapping c
    (NamedTuple _ ps1, TextMap t2) ->
        joinObjectComponents [(k, shapeOverlap t1 t2) | (k, t1) <- ps1]
    (TextMap t1, NamedTuple _ ps2) ->
        joinObjectComponents [(k, shapeOverlap t1 t2) | (k, t2) <- ps2]
    (TextMap t1, TextMap t2) ->
        Overlapping (JsonObject []) -- trivial case
    (Or t1 t2, t3) ->
        joinLeftOrPath (shapeOverlap t1 t3) (shapeOverlap t2 t3)
    (t1, Or t2 t3) ->
        joinLeftOrPath (shapeOverlap t1 t2) (shapeOverlap t1 t3)
    (Anything, t) -> Overlapping (example t) -- trivial case
    (t, Anything) -> Overlapping (example t) -- trivial case
    (Alternative _ _ _, _) ->
        error "error in shapeOverlap: Shape should not contain Alternative node !"
    (_, Alternative _ _ _) ->
        error "error in shapeOverlap: Shape should not contain Alternative node !"
    (Refined _ _, _) ->
        error "error in shapeOverlap: Shape should not contain Refined node !"
    (_, Refined _ _) ->
        error "error in shapeOverlap: Shape should not contain Refined node !"
    (Ref _, _) ->
        error "error in shapeOverlap: Shape should not contain Ref node !"
    (_, Ref _) ->
        error "error in shapeOverlap: Shape should not contain Ref node !"
    (t1, t2) -> --NOTE: these trivial cases, depending on matchOutline, it's correctness is subtle.
        if matchOutline' t2 (example t1) then Overlapping (example t1)
        else if matchOutline' t1 (example t2) then Overlapping (example t2)
        else NonOverlapping $ \d -> if (matchOutline' t1 d) then MatchLeft else if (matchOutline' t2 d) then MatchRight else MatchNothing

-- matchSpec

data MatchResult = Matched | UnMatched UnMatchedReason deriving (Show)
data UnMatchedReason = DirectCause DirectUMR CheckedSpec JsonData | StepCause StepUMR UnMatchedReason deriving (Show)

data DirectUMR =
      ShapeNotMatch
    | ConstValueNotEqual
    | TupleLengthNotMatch
    | NamedTupleKeySetNotMatch
    | RefinedPropNotMatch --TODO: add prop description sentence
    | OrMatchNothing
    deriving (Show)

data StepUMR =
      TupleFieldNotMatch Int
    | ArrayElementNotMatch Int
    | NamedTupleFieldNotMatch String
    | TextMapElementNotMatch String
    | RefinedShapeNotMatch
    | OrNotMatchLeft
    | OrNotMatchRight
    | RefNotMatch Name
    deriving (Show)

isIdentifier :: String -> Bool
isIdentifier _ = True --TODO:

explain :: UnMatchedReason -> (DirectUMR, CheckedSpec, JsonData, String, String)
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

isSimpleShape :: Shape -> Bool
isSimpleShape t = case t of
    Anything -> True
    Number -> True
    Text -> True
    Boolean -> True
    Null -> True
    ConstNumber n -> True
    ConstText s -> True
    ConstBoolean b -> True
    _ -> False

matchOutline :: TypeRep -> JsonData -> MatchResult --NOTE: this is shadow matching, only process trivial cases
matchOutline t d = case (t, d) of
    (Anything, _) -> Matched
    (Number, (JsonNumber _)) -> Matched
    (Text, (JsonText _)) -> Matched
    (Boolean, (JsonBoolean _)) -> Matched
    (Null, JsonNull) -> Matched
    (ConstNumber n, d@(JsonNumber n')) -> (n == n') `otherwise` (DirectCause ConstValueNotEqual (ConstNumber n) d)
    (ConstText s, d@(JsonText s')) -> (s == s') `otherwise` (DirectCause ConstValueNotEqual (ConstText s) d)
    (ConstBoolean b, d@(JsonBoolean b')) -> (b == b') `otherwise` (DirectCause ConstValueNotEqual (ConstBoolean b) d)
    (Tuple _ _, (JsonArray _)) -> Matched
    (Array _, (JsonArray _)) -> Matched
    (NamedTuple _ _, (JsonObject _)) -> Matched
    (TextMap _, (JsonObject _)) -> Matched
    (Refined t _, d) -> matchOutline t d
    (Ref _, d) -> error ("matchOutline can not process with Ref/Or/Alternative node: " ++ show t)
    (Or _ _, d) -> error ("matchOutline can not process with Ref/Or/Alternative node: " ++ show t)
    (Alternative _ _ _, d) -> error ("matchOutline can not process with Ref/Or/Alternative node: " ++ show t)
    (t, d) -> UnMatched (DirectCause ShapeNotMatch t d)

matchOutline' :: TypeRep -> JsonData -> Bool
matchOutline' t d = case (matchOutline t d) of Matched -> True; _ -> False

matchSpec :: Env CheckedSpec -> CheckedSpec -> JsonData -> MatchResult
matchSpec env t d = let rec = matchSpec env in case (t, d) of
    (Tuple Strict ts, d@(JsonArray xs)) ->
        (let l1 = length ts; l2 = length xs in (l1 == l2) `otherwise` (DirectCause TupleLengthNotMatch t d)) <>
        fold [wrap (TupleFieldNotMatch i) (rec t x) | (i, t, x) <- zip3 [0..] ts xs]
    (Tuple Tolerant ts, d@(JsonArray xs)) ->
        fold [wrap (TupleFieldNotMatch i) (rec t x) | (i, t, x) <- zip3 [0..] ts (take (length ts) xs)]
    (Array t, (JsonArray xs)) -> fold [wrap (ArrayElementNotMatch i) (rec t x) | (i, x) <- zip [0..] xs]
    (NamedTuple Strict ps, d@(JsonObject kvs)) ->
        ((S.fromList (map fst ps) == S.fromList (map fst kvs)) `otherwise` (DirectCause NamedTupleKeySetNotMatch t d)) <>
        fold [wrap (NamedTupleFieldNotMatch k) (rec t (lookupObj k d)) | (k, t) <- ps]
    (NamedTuple Tolerant ps, d@(JsonObject kvs)) ->
        fold [wrap (NamedTupleFieldNotMatch k) (rec t (lookupObj k d)) | (k, t) <- ps]
    (TextMap t, (JsonObject kvs)) -> fold [wrap (TextMapElementNotMatch k) (rec t v) | (k, v) <- kvs]
    (t@(Refined t1 p), d) -> wrap RefinedShapeNotMatch (rec t1 d) <> (testProp p d `otherwise` (DirectCause RefinedPropNotMatch t d))
    (t@(Alternative t1 t2 makeChoice), d) -> case makeChoice d of
        MatchLeft -> wrap OrNotMatchLeft (rec t1 d)
        MatchRight -> wrap OrNotMatchRight (rec t2 d)
        MatchNothing -> UnMatched (DirectCause OrMatchNothing t d)
    (Ref name, d) -> wrap (RefNotMatch name) (rec (env M.! name) d) -- NOTICE: can fail if name not in env
    (t, d) -> matchOutline t d

matchSpec' :: Env CheckedSpec -> CheckedSpec -> JsonData -> Bool
matchSpec' env t d = case (matchSpec env t d) of Matched -> True; _ -> False

tryMatchSpec :: Env Spec -> Spec -> JsonData -> Either CheckFailedReason MatchResult
tryMatchSpec env sp d = ((,) <$> checkEnv env <*> checkSpec env sp) >>= (\(env', sp') -> pure (matchSpec env' sp' d))

-- everywhereJ

type CheckedJson = (JsonData, CheckedSpec) -- also with a proof about (matchSpec' sp d = True)

everywhereJ :: Monad m => Env CheckedSpec -> CheckedSpec -> Name -> (JsonData -> m JsonData) -> (JsonData -> m JsonData)
everywhereJ env spec name g dat = rec spec dat where
    rec spec dat = case (spec, dat) of
        (Tuple _ ts, (JsonArray xs)) -> (JsonArray <$> sequence [rec t x | (t, x) <- zip ts xs]) >>= g
        (Array t, (JsonArray xs)) -> (JsonArray <$> sequence [rec t x | x <- xs]) >>= g
        (NamedTuple _ ps, d@(JsonObject _)) -> (JsonObject <$> sequence [(k,) <$> rec t (lookupObj k d) | (k, t) <- ps]) >>= g --NOTE: use everywhereJ will remove redundant keys
        (TextMap t, (JsonObject kvs)) -> (JsonObject <$> sequence [(k,) <$> rec t v | (k, v) <- kvs]) >>= g
        (Refined t _, d) -> rec t d
        (Alternative t1 t2 makeChoice, d) -> case makeChoice d of
            MatchLeft -> rec t1 d
            MatchRight -> rec t2 d
            MatchNothing -> error "everywhereJ not used correctly (1)"
        (Ref name', d) -> let t = env M.! name in if name' == name then rec t d >>= g else rec t d
        (t, d) -> if matchOutline' t d then pure d else error "everywhereJ not used correctly (2)"

-- test

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

main :: IO ()
main = do
    print (checkSpec env (Or Number Text))
    print (checkSpec env (Or (Or Number Text) (ConstText "abc")))
    print (checkSpec env (Or (Or Number Text) case1))
    print (checkSpec env (Or (Or Number Text) case2))
    print (checkSpec env (Or (Or Number Text) ast))
    print (checkSpec env (Or (Or Number Text) case1'))
    print (checkSpec env (Or (Or Number Text) (Or case1 case1')))
    print (toShape env ast)
    print (checkSpec env (Or spec1 spec2))
    print (checkSpec env (Or spec1 spec2'))
    print (checkSpec env (Or spec1 spec2'))
    printEn (tryMatchSpec env ast dat1)
    printZh (tryMatchSpec env ast dat2)
    printZh (tryMatchSpec env spec3 data3)
    printZh (tryMatchSpec env spec4 data4)

