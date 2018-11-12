-- Copyright 2018 and onwards LuoChen (luochen1990@gmail.com).

{-# language DeriveDataTypeable, TupleSections #-}
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

compareSortedListWith :: Ord b => (a -> b) -> [a] -> [a] -> ([(a, a)], [a], [a])
compareSortedListWith = undefined

-- TypeRep & JsonData

type Spec = TypeRep -- without Alternative
type Shape = TypeRep -- without Alternative, Ref, Refined
type SimpleShape = TypeRep -- only simple atomic shapes (8 cases)
type CheckedSpec = TypeRep -- without Or
-- subtyping relations:
--   SimpleShape <: Shape <: Spec
--   SimpleShape <: CheckedSpec <: Spec

data TypeRep =
      Anything
    | Number
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
    | Ref Name
    | Or TypeRep TypeRep
    | Alternative TypeRep TypeRep (JsonData -> MatchChoice)

type Name = String
data DecProp = DecProp {testProp :: JsonData -> Bool}
data MatchChoice = MatchLeft | MatchRight | MatchNothing deriving (Show, Eq, Ord)

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
    Tuple ts -> JsonArray (map example ts)
    Array t -> JsonArray [(example t)]
    NamedTuple ps -> JsonObject [(k, example t) | (k, t) <- ps]
    TextMap t -> JsonObject [("k", example t)]
    Refined t _ -> error "Shape should not contain Refined"
    Ref name -> error "Shapeshould not contain Ref"
    Or a b -> error "Shapeshould not contain Or"
    Alternative a b _ -> example a

extendObject :: JsonData -> JsonData -> JsonData
extendObject (JsonObject ps1) (JsonObject ps2) = JsonObject (ps1 ++ ps2)
extendObject _ _ = error "extendObject must be used on two JsonObject"

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
        Tuple ts -> "(" ++ intercalate ", " (map show ts) ++ ")"
        Array t -> "Array<" ++ show t ++ ">"
        NamedTuple ps -> "{" ++ intercalate ", " [k ++ ": " ++ show t | (k, t) <- ps] ++ "}"
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
    Tuple ts -> Tuple <$> sequence (map rec ts) >>= g
    Array t -> Array <$> rec t >>= g
    NamedTuple ps -> NamedTuple <$> sequence [(k,) <$> (rec t) | (k, t) <- ps] >>= g
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
    (_, NonOverlapping c2) -> NonOverlapping (\d -> case d of (JsonObject kvs) -> c2 (JsonObject kvs); _ -> MatchNothing) -- note that not remove k is correct
    (NonOverlapping c1, _) -> NonOverlapping (\d -> case d of (JsonObject kvs) -> c1 (fromMaybe JsonNull (M.lookup k (M.fromList kvs))); _ -> MatchNothing)

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
                joinTupleComponents (zipWith shapeOverlap ts1 ts2)
    (Tuple ts1, Array t2) ->
        joinTupleComponents (zipWith shapeOverlap ts1 (repeat t2))
    (Array t1, Tuple ts2) ->
        joinTupleComponents (zipWith shapeOverlap (repeat t1) ts2)
    (Array t1, Array t2) ->
        Overlapping (JsonArray []) -- trivial case
    (NamedTuple ps1, NamedTuple ps2) ->
        -- NamedTuple is non-strict
        let (common, fstOnly, sndOnly) = compareSortedListWith fst (sortWith fst ps1) (sortWith fst ps2)
        in case joinObjectComponents [(k, shapeOverlap t1 t2) | ((k, t1), (_, t2)) <- common] of
            Overlapping d -> Overlapping (extendObject d (example (NamedTuple (fstOnly ++ sndOnly))))
            MayOverlapping d -> MayOverlapping (extendObject d (example (NamedTuple (fstOnly ++ sndOnly))))
            NonOverlapping c -> NonOverlapping c
    (NamedTuple ps1, TextMap t2) ->
        joinObjectComponents [(k, shapeOverlap t1 t2) | (k, t1) <- ps1]
    (TextMap t1, NamedTuple ps2) ->
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
    (t1, t2) -> --NOTE: these trivial cases, depending on matchShape, it's correctness is subtle.
        if matchShape' t2 (example t1) then Overlapping (example t1)
        else if matchShape' t1 (example t2) then Overlapping (example t2)
        else NonOverlapping $ \d -> if (matchShape' t1 d) then MatchLeft else if (matchShape' t2 d) then MatchRight else MatchNothing

-- matchSpec

data MatchResult = Matched | UnMatched UnMatchedReason
data UnMatchedReason =
      ShapeNotMatch CheckedSpec JsonData
    | ConstValueNotEqual CheckedSpec JsonData
    | TupleLengthNotMatch CheckedSpec JsonData
    | TupleFieldNotMatch Int UnMatchedReason
    | ArrayElementNotMatch Int UnMatchedReason
    | NamedTupleFieldNotMatch String UnMatchedReason
    | TextMapElementNotMatch String UnMatchedReason
    | RefinedShapeNotMatch UnMatchedReason
    | RefinedPropNotMatch CheckedSpec JsonData
    | OrMatchNothing CheckedSpec JsonData
    | OrNotMatchLeft UnMatchedReason
    | OrNotMatchRight UnMatchedReason
    | NamedTypeNotMatch Name UnMatchedReason
    deriving (Show)

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

matchShape :: SimpleShape -> JsonData -> MatchResult --NOTE: this is shadow matching, only process trivial cases
matchShape t d = case (t, d) of
    (Anything, _) -> Matched
    (Number, (JsonNumber _)) -> Matched
    (Text, (JsonText _)) -> Matched
    (Boolean, (JsonBoolean _)) -> Matched
    (Null, JsonNull) -> Matched
    (ConstNumber n, d@(JsonNumber n')) -> (n == n') `otherwise` (ConstValueNotEqual (ConstNumber n) d)
    (ConstText s, d@(JsonText s')) -> (s == s') `otherwise` (ConstValueNotEqual (ConstText s) d)
    (ConstBoolean b, d@(JsonBoolean b')) -> (b == b') `otherwise` (ConstValueNotEqual (ConstBoolean b) d)
    (Tuple _, (JsonArray _)) -> Matched
    (Array _, (JsonArray _)) -> Matched
    (NamedTuple _, (JsonObject _)) -> Matched
    (TextMap _, (JsonObject _)) -> Matched
    (Refined t _, d) -> matchShape t d
    (Ref _, d) -> error ("matchShape can not process with Ref/Or/Alternative node: " ++ show t)
    (Or _ _, d) -> error ("matchShape can not process with Ref/Or/Alternative node: " ++ show t)
    (Alternative _ _ _, d) -> error ("matchShape can not process with Ref/Or/Alternative node: " ++ show t)
    (t, d) -> UnMatched (ShapeNotMatch t d)

matchShape' :: SimpleShape -> JsonData -> Bool
matchShape' t d = case (matchShape t d) of Matched -> True; _ -> False

matchSpec :: Env CheckedSpec -> CheckedSpec -> JsonData -> MatchResult
matchSpec env t d = let rec = matchSpec env in case (t, d) of
    (Tuple ts, d@(JsonArray xs)) ->
        (let l1 = length ts; l2 = length xs in (l1 == l2) `otherwise` (TupleLengthNotMatch t d)) <>
        fold [wrap (TupleFieldNotMatch i) (rec t x) | (i, t, x) <- zip3 [0..] ts xs]
    (Array t, (JsonArray xs)) -> fold [wrap (ArrayElementNotMatch i) (rec t x) | (i, x) <- zip [0..] xs]
    (NamedTuple ps, (JsonObject kvs)) -> let mp = M.fromList kvs in fold [rec t (fromMaybe JsonNull (M.lookup k mp)) | (k, t) <- ps] --NamedTuple is not strict
    (TextMap t, (JsonObject kvs)) -> fold [wrap (TextMapElementNotMatch k) (rec t v) | (k, v) <- kvs]
    (t@(Refined t1 p), d) -> wrap RefinedShapeNotMatch (rec t1 d) <> (testProp p d `otherwise` (RefinedPropNotMatch t d))
    (t@(Alternative t1 t2 makeChoice), d) -> case makeChoice d of
        MatchLeft -> wrap OrNotMatchLeft (rec t1 d)
        MatchRight -> wrap OrNotMatchRight (rec t2 d)
        MatchNothing -> UnMatched (OrMatchNothing t d)
    (Ref name, d) -> wrap (NamedTypeNotMatch name) (rec (env M.! name) d) -- NOTICE: can fail if name not in env
    (t, d) -> matchShape t d

matchSpec' :: Env CheckedSpec -> CheckedSpec -> JsonData -> Bool
matchSpec' env t d = case (matchSpec env t d) of Matched -> True; _ -> False

-- test

ast = Or case1 case2
case1 = (Tuple [ConstText "Lit", Number])
case1' = (Tuple [ConstText "Lit", ConstNumber 1])
case2 = (Tuple [ConstText "Add", Ref "AST", Ref "AST"])

env = M.fromList [("AST", ast)]
dat1 = JsonArray [JsonText "Lit", JsonNumber 1]
dat2 = JsonArray [JsonText "Lit", JsonText "1"]

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
    case checkSpec env ast of
        Right ast' -> do
            traceM $ "GOT ast': " ++ show ast'
            case checkEnv env of
                Right env' -> do
                    traceM $ "GOT env': " ++ show env'
                    print (matchSpec' env' ast' dat1)
                    print (matchSpec' env' ast' dat2)
                _ -> putStrLn "error"
        _ -> putStrLn "error"

