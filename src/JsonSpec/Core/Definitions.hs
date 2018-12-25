-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

{-# language TupleSections #-}
{-# language FlexibleInstances #-}

-- | Providing core definitions about JsonSpec
module JsonSpec.Core.Definitions where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Semigroup
import Data.Foldable (fold, foldMap)
import Data.List
import Data.Maybe
import Data.Fix
import Data.Text.Lazy (unpack)
import Data.Char (isAlphaNum)
import Text.MultilingualShow
import Control.Monad.State
import JsonSpec.Core.Tools
import Text.Pretty.Simple

---------------------------------------------------------------------
-- * JsonData
---------------------------------------------------------------------

-- | JSON Data in ADT
data JsonData =
      JsonNumber Double
    | JsonText String
    | JsonBoolean Bool
    | JsonNull
    | JsonArray [JsonData]
    | JsonObject [(String, JsonData)]
    deriving (Eq, Ord)

-- | literal JSON
instance Show JsonData where
    show dat = case dat of
        JsonNumber x -> show x
        JsonText s -> show s
        JsonBoolean b -> show b
        JsonNull -> "null"
        JsonArray xs -> "[" ++ intercalate ", " (map show xs) ++ "]"
        JsonObject ps -> "{" ++ intercalate ", " [showIdentifier k ++ ": " ++ show v | (k, v) <- ps] ++ "}"

extendObj :: JsonData -> JsonData -> JsonData
extendObj (JsonObject ps1) (JsonObject ps2) = JsonObject (ps1 ++ ps2)
extendObj _ _ = error "extendObj must be used on two JsonObject"

lookupObj :: String -> JsonData -> Maybe JsonData
lookupObj k (JsonObject kvs) = (M.lookup k (M.fromList kvs))
lookupObj _ _ = error "lookupObj must be used on JsonObject"

lookupObj' :: String -> JsonData -> JsonData
lookupObj' k (JsonObject kvs) = (fromMaybe JsonNull (M.lookup k (M.fromList kvs)))
lookupObj' _ _ = error "lookupObj' must be used on JsonObject"

---------------------------------------------------------------------
-- * TyRep
---------------------------------------------------------------------

-- | TyRep r p c tr' is a generic representation of Spec & CSpec & Shape,
--   with Ref indexed by r, Refined with p, Or attached with c,
--   and recursively defined on tr'.
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
    | Object Strictness [(String, tr')]
    | TextMap tr'
    | Ref r
    | Refined tr' p
    | Or tr' tr' c

-- | a tool function to filter out prim TyRep nodes,
--   we can use it to simplify pattern matching logic.
isPrimTyRepNode :: TyRep r p c tr' -> Bool
isPrimTyRepNode tr = case tr of
    Anything -> True
    Number -> True
    Text -> True
    Boolean -> True
    Null -> True
    ConstNumber n -> True
    ConstText s -> True
    ConstBoolean b -> True
    _ -> False

-- ** useful instances about TyRep

instance (Eq r, Eq p, Eq c, Eq tr') => Eq (TyRep r p c tr') where
    tr1 == tr2 = case (tr1, tr2) of
        (Anything, Anything) -> True
        (Number, Number) -> True
        (Text, Text) -> True
        (Boolean, Boolean) -> True
        (Null, Null) -> True
        (ConstNumber n1, ConstNumber n2) -> n1 == n2
        (ConstText s1, ConstText s2) -> s1 == s2
        (ConstBoolean b1, ConstBoolean b2) -> b1 == b2
        (Tuple s1 ts1, Tuple s2 ts2) -> s1 == s2 && ts1 == ts2
        (Array t1, Array t2) -> t1 == t2
        (Object s1 ps1, Object s2 ps2) -> s1 == s2 && ps1 == ps2
        (TextMap t1, TextMap t2) -> t1 == t2
        (Ref r1, Ref r2) -> r1 == r2
        (Refined t1 p1, Refined t2 p2) -> t1 == t2 && p1 == p2
        (Or a1 b1 c1, Or a2 b2 c2) -> a1 == a2 && b1 == b2 && c1 == c2
        _ -> False

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
        Object s ps -> Object s [(k, f4 v) | (k, v) <- ps]
        TextMap t -> TextMap (f4 t)
        Ref name -> Ref (f1 name)
        Refined t p -> Refined (f4 t) (f2 p)
        Or t1 t2 c -> Or (f4 t1) (f4 t2) (f3 c)

instance Functor (TyRep r p c) where
    fmap = quadmap4

instance Foldable (TyRep r p c) where
    foldMap f tr = case tr of
        Tuple s ts -> foldMap f ts
        Array t -> f t
        Object s ps -> foldMap (f . snd) ps
        TextMap t -> f t
        Refined t _ -> f t
        Or t1 t2 _ -> f t1 `mappend` f t2
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
        Object s ps -> Object s <$> sequenceA [(k,) <$> f v | (k, v) <- ps]
        TextMap t -> TextMap <$> f t
        Refined t p -> Refined <$> f t <*> pure p
        Or t1 t2 c -> Or <$> (f t1) <*> (f t2) <*> pure c

-- ** trivial things about TyRep

-- | strictness label for Tuple & Object
data Strictness
    = Strict -- ^ a strict Tuple or Object doesnt accept redurant part, and null cannot be ignored
    | Tolerant -- ^ a tolerant Tuple or Object accept redurant part, and treat not present part as null
    deriving (Show, Eq, Ord)

instance (ShowRef r, ShowOr c, Show tr') => Show (TyRep r p c tr') where
    show tr = case tr of
        Anything -> "Anything"
        Number -> "Number"
        Text -> "Text"
        Boolean -> "Boolean"
        Null -> "Null"
        ConstNumber n -> show n
        ConstText s -> show s
        ConstBoolean b -> show b
        Tuple Strict ts -> "[" ++ intercalate ", " (map show ts) ++ "]"
        Tuple Tolerant ts -> "[" ++ intercalate ", " (map show ts ++ ["*"]) ++ "]"
        Array t -> "(Array " ++ show t ++ ")"
        Object Strict ps -> "{" ++ intercalate ", " [showIdentifier k ++ ": " ++ show t | (k, t) <- ps] ++ "}"
        Object Tolerant ps -> "{" ++ intercalate ", " ([showIdentifier k ++ ": " ++ show t | (k, t) <- ps] ++ ["*"]) ++ "}"
        TextMap t -> "(TextMap " ++ show t ++ ")"
        Ref name -> showRef name
        Refined t _ -> "(Refined " ++ show t ++ ")"
        Or a b c -> "(" ++ show a ++ bar ++ show b ++ ")" where
            bar = " " ++ showOr c ++ " "

instance {-# Overlapping #-} (ShowRef r, ShowOr c) => Show (Fix (TyRep r p c)) where
    show (Fix tr) = show tr

class ShowRef a where
    showRef :: a -> String

instance ShowRef [Char] where
    showRef s = s

instance ShowRef () where
    showRef () = "$"

class ShowOr a where
    showOr :: a -> String

instance ShowOr () where
    showOr _ = "|?"

---------------------------------------------------------------------
-- * Spec & CSpec & Shape
---------------------------------------------------------------------

-- | the Spec parsed from user input
type Spec = Fix (TyRep Name DecProp ())

-- | the checked Spec, attached with choice maker
type CSpec = Fix (TyRep Name DecProp ChoiceMaker)

-- | the Shape of a Spec, ignore Ref, Refined information of Spec
type Shape = Fix (TyRep () () ())

-- ** Name & Env

-- | the name of a user defined Spec
type Name = String

-- | the environment which contains information a
type Env a = M.Map Name a

-- ** DecProp

-- | a decidable proposition about JsonData
data DecProp = DecProp {testProp :: JsonData -> Bool}

-- ** ChoiceMaker

-- | a matching choice maked by choice maker
data MatchChoice = MatchNothing | MatchLeft | MatchRight deriving (Show, Eq, Ord)

flipMatchChoice :: MatchChoice -> MatchChoice
flipMatchChoice mc = case mc of
    MatchRight -> MatchLeft
    MatchLeft -> MatchRight
    MatchNothing -> MatchNothing

-- | a choice maker helps to make choice on Or node,
--   also an evidence of two shape not overlapping
data ChoiceMaker
    = ViaArrayLength Int Int
    | ViaArrayLengthGT Int MatchChoice
    | ViaObjectHasKey String MatchChoice
    | ViaOutline (S.Set Outline) (S.Set Outline)
    | ViaArrayElement Int MatchChoice ChoiceMaker
    | ViaObjectField String MatchChoice ChoiceMaker
    | ViaOrL ChoiceMaker ChoiceMaker
    | ViaOrR ChoiceMaker ChoiceMaker
    deriving (Show, Eq)

-- | a ChoiceMaker can be interpreted as a function directly
makeChoice :: ChoiceMaker -> JsonData -> MatchChoice
makeChoice cm = case cm of
    ViaArrayLength l1 l2 -> \d -> case d of
        (JsonArray xs) ->
            let l = length xs
            in
                if l == l1 then MatchLeft
                else if l == l2 then MatchRight
                else MatchNothing
        _ -> MatchNothing
    ViaArrayLengthGT l r ->
        let r' = flipMatchChoice r
        in \d -> case d of
            (JsonArray xs) ->
                if length xs > l then r else r'
            _ -> MatchNothing
    ViaObjectHasKey k r ->
        let r' = flipMatchChoice r
        in \d -> case d of
            (JsonObject _) ->
                if isJust (lookupObj k d) then r else r'
            _ -> MatchNothing
    ViaOutline ols1 ols2 -> \d ->
        if or [(matchOutline ol1 d) | ol1 <- S.toList ols1] then MatchLeft
        else if or [(matchOutline ol2 d) | ol2 <- S.toList ols2] then MatchRight
        else MatchNothing
    ViaArrayElement i dft c -> \d -> case d of
        (JsonArray xs) ->
            if i < length xs then makeChoice c (xs !! i) else dft
        _ -> MatchNothing
    ViaObjectField k dft c -> \d -> case d of
        (JsonObject ps) ->
            maybe dft (makeChoice c) (lookupObj k d)
        _ -> MatchNothing
    ViaOrL c13 c23 -> \d ->
        case (makeChoice c13 d, makeChoice c23 d) of
            (MatchLeft, _) -> MatchLeft -- t1/t2 of course
            (_, MatchLeft) -> MatchLeft -- t2 of course
            (MatchRight, MatchRight) -> MatchRight -- t3 of course
            (MatchNothing, MatchNothing) -> MatchNothing
            _ -> MatchNothing -- seems impossible
    ViaOrR c12 c13 -> \d ->
        case (makeChoice c12 d, makeChoice c13 d) of
            (MatchRight, _) -> MatchRight -- t2/t3 of course
            (_, MatchRight) -> MatchRight -- t3 of course
            (MatchLeft, MatchLeft) -> MatchLeft -- t1 of course
            (MatchNothing, MatchNothing) -> MatchNothing
            _ -> MatchNothing -- seems impossible

instance ShowOr ChoiceMaker where
    showOr _ = "|"

-- ** Outline

data Outline =
      AnythingOL
    | NumberOL
    | TextOL
    | BooleanOL
    | ConstOL JsonData
    | ArrayOL
    | ObjectOL
    deriving (Eq, Ord)

instance Show Outline where
    show ol = case ol of
        AnythingOL -> "Anything"
        NumberOL -> "Number"
        TextOL -> "Text"
        BooleanOL -> "Boolean"
        ConstOL d -> show d
        ArrayOL -> "Array"
        ObjectOL -> "Object"

toOutline :: Fix (TyRep r p c) -> Outline
toOutline (Fix tr) = case tr of
    Anything -> AnythingOL
    Number -> NumberOL
    Text -> TextOL
    Boolean -> BooleanOL
    Null -> ConstOL JsonNull
    ConstNumber n -> ConstOL (JsonNumber n)
    ConstText s -> ConstOL (JsonText s)
    ConstBoolean b -> ConstOL (JsonBoolean b)
    Tuple _ _ -> ArrayOL
    Array _ -> ArrayOL
    Object _ _ -> ObjectOL
    TextMap _ -> ObjectOL
    Ref _ -> AnythingOL
    Refined t _ -> toOutline t
    Or a b c -> AnythingOL

-- | shadow matching, only returns False on very obvious cases, no recursion
matchOutline :: Outline -> JsonData -> Bool
matchOutline ol d = case (ol, d) of
    (AnythingOL, _) -> True
    (NumberOL, (JsonNumber _)) -> True
    (TextOL, (JsonText _)) -> True
    (BooleanOL, (JsonBoolean _)) -> True
    (ConstOL d', _) -> d == d'
    (ArrayOL, (JsonArray _)) -> True
    (ObjectOL, (JsonObject _)) -> True
    _ -> False

-- ** useful tools about Spec & CSpec & Shape

toSpec :: CSpec -> Spec
toSpec (Fix tr) = Fix $ quadmap id id (const ()) toSpec tr

-- | generate an non-recursive and env-independent shape from a Spec or CSpec,
--   a Nat depth is required to specify how many times a Ref should be expanded.
toShape :: Int -> Env (Fix (TyRep Name p c)) -> (Fix (TyRep Name p' c')) -> Shape
toShape dep env sp | dep >= 0 = evalState (cataM g sp) M.empty where
    g :: TyRep Name p'' c'' Shape -> State (M.Map Name Int) Shape
    g tr = case tr of
        Ref name -> do
            --traceM ("name: " ++ name)
            visd <- get
            if dep == 0 || fromMaybe 0 (visd M.!? name) >= dep
            then pure (Fix (Ref ()))
            else do
                modify (M.alter (Just . (+1) . fromMaybe 0) name)
                r <- cataM g (env M.! name) --NOTE: may fail
                modify (M.alter (Just . (+(-1)) . fromJust) name)
                return r
        Refined t _ -> pure (Fix (Refined t ()))
        Or t1 t2 _ -> pure (Fix $ Or t1 t2 ())
        t -> pure (Fix $ quadmap (const ()) (const ()) (const ()) id t)

-- | a convenient variant of toShape, with depth = 0
toShape' :: (Fix (TyRep Name p c)) -> Shape
toShape' = toShape 0 M.empty

-- | decide whether a shape contains no blackbox item
isDeterminateShape :: Shape -> Bool
isDeterminateShape = cata f where
    f tr = case tr of
        Tuple _ ts -> and ts
        Array t -> t
        Object _ ps -> and (map snd ps)
        TextMap t -> t
        Ref _ -> False -- blackbox item
        Refined t _ -> False -- blackbox item
        Or a b _ -> a && b
        _ -> True

-- | decide whether a shape accept JsonNull, treat blackbox item as True
acceptNull :: Shape -> Bool
acceptNull (Fix tr) = case tr of
    Null -> True
    Anything -> True
    Or t1 t2 _ -> acceptNull t1 || acceptNull t2
    Ref _ -> True -- blackbox item
    Refined t _ -> acceptNull t -- blackbox item
    _ -> False

-- | generate example JsonData along a specific Shape,
--   not rigorous: example matches the Spec only when it's shape isDeterminateShape
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
    Object _ ps -> JsonObject [(k, example t) | (k, t) <- ps]
    TextMap t -> JsonObject [("k", example t)]
    Ref _ -> JsonNull --NOTE: not a rigorous example
    Refined t _ -> example t --NOTE: not a rigorous example
    Or a b _ -> example a

-- | show ChoiceMaker of a CSpec
showChoiceMaker :: CSpec -> String
showChoiceMaker (Fix (Or a b c)) = unpack (pShow (show c))

ppcm :: CSpec -> IO ()
ppcm (Fix (Or a b c)) = pPrint c

pp :: Show a => a -> IO ()
pp = pPrint

---------------------------------------------------------------------
-- * MatchResult
---------------------------------------------------------------------

-- | matching result when we try to match a specific JsonData to a specific Spec
data MatchResult = Matched | UnMatched UnMatchedReason deriving (Show)

-- | a convenient infix constructor of MatchResult
elseReport :: Bool -> UnMatchedReason -> MatchResult
b `elseReport` reason = if b then Matched else UnMatched reason

-- | a convenient prefix constructor of MatchResult
wrapMR :: StepUMR -> MatchResult -> MatchResult
wrapMR step rst = case rst of Matched -> Matched; UnMatched reason -> UnMatched (StepCause step reason)

-- | Eq instance of MatchResult only compare the tag of the result
instance Eq MatchResult where
    a == b = case (a, b) of (Matched, Matched) -> True; (UnMatched _, UnMatched _) -> True; _ -> False

-- | mappend means if both components are Matched, then entireness is Matched,
--   mempty = Matched means when no component is considered, then we think it is Matched
instance Monoid MatchResult where
    mempty = Matched
    mappend = (<>)

instance Semigroup MatchResult where
    (<>) Matched Matched = Matched
    (<>) Matched r2 = r2
    (<>) r1 _ = r1

-- ** trivial things about MatchResult

-- | representation of the reason why they are not matched
data UnMatchedReason = DirectCause DirectUMR CSpec JsonData | StepCause StepUMR UnMatchedReason deriving (Show)

-- | direct unmatch reason, a part of UnMatchedReason
data DirectUMR =
      OutlineNotMatch
    | TupleLengthNotEqual
    | ObjectKeySetNotEqual
    | RefinedPropNotMatch --TODO: add prop description sentence
    | OrMatchNothing ChoiceMaker
    deriving (Show, Eq)

-- | step unmatch reason, a part of UnMatchedReason
data StepUMR =
      TupleFieldNotMatch Int
    | ArrayElementNotMatch Int
    | ObjectFieldNotMatch String
    | TextMapElementNotMatch String
    | RefinedShapeNotMatch
    | OrNotMatchLeft
    | OrNotMatchRight
    | RefNotMatch Name
    deriving (Show, Eq, Ord)

instance MultilingualShow MatchResult where
    showEnWith f mr = case mr of Matched -> "Matched"; (UnMatched r) -> "UnMatched !\n" ++ f r

instance MultilingualShow UnMatchedReason where
    showEnWith _ r =
        let (direct, sp, d, specPath, dataPath) = explainUnMatchedReason r
        in "  Abstract: it" ++ dataPath ++ " should be a " ++ show sp ++ ", but got " ++ show d ++
            "\n  Direct Cause: " ++ show direct ++
            "\n    Spec: " ++ show sp ++
            "\n    Data: " ++ show d ++
            "\n  Spec Path: " ++ specPath ++
            "\n  Data Path: " ++ dataPath
    showZhWith _ r =
        let (direct, sp, d, specPath, dataPath) = explainUnMatchedReason r
        in "  摘要: it" ++ dataPath ++ " 应该是一个 " ++ show sp ++ ", 但这里是 " ++ show d ++
            "\n  直接原因: " ++ show direct ++
            "\n    规格: " ++ show sp ++
            "\n    数据: " ++ show d ++
            "\n  规格路径: " ++ specPath ++
            "\n  数据路径: " ++ dataPath

explainUnMatchedReason :: UnMatchedReason -> (DirectUMR, CSpec, JsonData, String, String)
explainUnMatchedReason reason = iter reason undefined [] where
    iter reason dc path = case reason of
        DirectCause dr sp d -> (dr, sp, d, concatMap specAccessor path, concatMap dataAccessor path)
        StepCause sr r -> iter r dc (path ++ [sr])

    specAccessor r = case r of
        TupleFieldNotMatch i -> "." ++ show i
        ArrayElementNotMatch i -> "[" ++ show i ++ "]"
        ObjectFieldNotMatch k -> "." ++ if isIdentifier k then k else show k
        TextMapElementNotMatch k -> "[" ++ show k ++ "]"
        RefinedShapeNotMatch -> "<refined>"
        OrNotMatchLeft -> "<left>"
        OrNotMatchRight -> "<right>"
        RefNotMatch name -> "{" ++ name ++ "}"

    dataAccessor r = case r of
        TupleFieldNotMatch i -> "[" ++ show i ++ "]"
        ArrayElementNotMatch i -> "[" ++ show i ++ "]"
        ObjectFieldNotMatch k -> (if isIdentifier k then "." ++ k else "[" ++ show k ++ "]")
        TextMapElementNotMatch k -> "[" ++ show k ++ "]"
        _ -> ""

