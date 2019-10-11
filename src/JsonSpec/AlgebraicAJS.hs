-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

{-# language QuasiQuotes #-}
{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}

-- | express JsonSpec via JsonSpec
module JsonSpec.AlgebraicAJS where

import Text.RawString.QQ
import qualified Data.Map as M
import Data.Fix
import Data.List (partition)
import JsonSpec.Core.Definitions
import JsonSpec.Core.Functions
import JsonSpec.DSL
--import JsonSpec.EDSL

-- | Json serialization & deserialization
class JsonSerial a where
    toJson :: a -> JsonData
    fromJson :: JsonData -> a
    fromJson s = either error id (safeFromJson s)
    safeFromJson :: JsonData -> Either String a

instance JsonSerial Spec where
    toJson (Fix tr) = case tr of
        Anything -> tag "Anything"
        Number -> tag "Number"
        Text -> tag "Text"
        Boolean -> tag "Boolean"
        Null -> JsonNull
        ConstNumber n -> JsonNumber n
        ConstText s -> JsonArray [tag "Lit", JsonText s]
        ConstBoolean b -> JsonBoolean b
        Tuple Strict ts -> JsonArray (map toJson ts)
        Tuple Tolerant ts -> JsonArray (map toJson ts ++ [tag "Tolerant"])
        Array t -> JsonArray [tag "Array", (toJson t)]
        Object Strict ps -> JsonObject [(k, toJson t) | (k, t) <- ps]
        Object Tolerant ps -> JsonObject ([(k, toJson t) | (k, t) <- ps] ++ [("*", tag "Tolerant")])
        Dict t -> JsonArray [tag "Dict", (toJson t)]
        Ref name -> JsonText ('$':name)
        Refined t p -> JsonArray [tag "Refined", (toJson t)]
        Or a b _ -> JsonArray [tag "Or", (toJson a), (toJson b)]
        where
            tag s = JsonText ('#':s)

    safeFromJson d = case d of
        JsonNull -> pure (Fix Null)
        JsonNumber n -> pure (Fix $ ConstNumber n)
        JsonText s -> case s of
            ('#':s') -> case s' of
                "Anything" -> pure (Fix Anything)
                "Number" -> pure (Fix Number)
                "Text" -> pure (Fix Text)
                "Boolean" -> pure (Fix Boolean)
            ('$':s') -> pure (Fix $ Ref s')
            _ -> Left ("invalid Spec from JSON: " ++ show d)
        JsonBoolean b -> pure (Fix $ ConstBoolean b)
        JsonArray xs -> case xs of
            (JsonText "#Lit" : (JsonText s) : []) -> pure (Fix $ ConstText s)
            (JsonText "#Array" : x : []) -> pure (Fix $ Array (fromJson x))
            (JsonText "#Dict" : x : []) -> pure (Fix $ Dict (fromJson x))
            (JsonText "#Refined" : x : _) -> pure (Fix $ Refined (fromJson x) undefined)
            (JsonText "#Or" : x : y : []) -> pure (Fix $ Or (fromJson x) (fromJson y) ())
            _ ->
                let (tol, xs') = partition (== JsonText "#Tolerant") xs
                    s = if (null tol) then Strict else Tolerant
                in pure (Fix $ Tuple s (map fromJson xs'))
        JsonObject ps ->
            let (tol, ps') = partition ((== JsonText "#Tolerant") . snd) ps
                s = if (null tol) then Strict else Tolerant
            in pure (Fix $ Object s [(k, fromJson v) | (k, v) <- ps'])

-- | express JsonSpec via JsonSpec
aajs :: Env CSpec
aajs = env where
    textInput = [r|
        data JsonSpec =
            | (   "#Anything"
                | "#Number"
                | "#Text"
                | "#Boolean"
                | Null
                | Number
                | Boolean )
            | (   ["#Lit", Text]
                | ["#Array", JsonSpec]
                | ["#Dict", JsonSpec]
                | ["#Refined", JsonSpec]
                | ["#Or", JsonSpec, JsonSpec] )
            | Array (JsonSpec | "#Tolerant")
            | Dict (JsonSpec | "#Tolerant")
        |]

    decs = either error id (parseFile textInput)
    env = either (error . show) id (checkEnv (M.fromList decs))

