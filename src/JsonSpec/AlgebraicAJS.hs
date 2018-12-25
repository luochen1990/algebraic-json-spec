-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

{-# language QuasiQuotes #-}

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

-- | serialize Spec to JSON
toJson :: Spec -> JsonData
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
    TextMap t -> JsonArray [tag "TextMap", (toJson t)]
    Ref name -> JsonText ('$':name)
    Refined t p -> JsonArray [tag "Refined", (toJson t)]
    Or a b _ -> JsonArray [tag "Or", (toJson a), (toJson b)]
    where
        tag s = JsonText ('#':s)

-- | deserialize Spec from JSON
fromJson :: JsonData -> Spec
fromJson d = Fix $ case d of
    JsonNull -> Null
    JsonNumber n -> ConstNumber n
    JsonText s -> case s of
        ('#':s') -> case s' of
            "Anything" -> Anything
            "Number" -> Number
            "Text" -> Text
            "Boolean" -> Boolean
        ('$':s') -> Ref s'
    JsonBoolean b -> ConstBoolean b
    JsonArray xs -> case xs of
        (JsonText "#Lit" : (JsonText s) : []) -> ConstText s
        (JsonText "#Array" : x : []) -> Array (fromJson x)
        (JsonText "#TextMap" : x : []) -> TextMap (fromJson x)
        (JsonText "#Refined" : x : _) -> Refined (fromJson x) undefined
        (JsonText "#Or" : x : y : []) -> Or (fromJson x) (fromJson y) ()
        _ ->
            let (tol, xs') = partition (== JsonText "#Tolerant") xs
                s = if (null tol) then Strict else Tolerant
            in Tuple s (map fromJson xs')
    JsonObject ps ->
        let (tol, ps') = partition ((== JsonText "#Tolerant") . snd) ps
            s = if (null tol) then Strict else Tolerant
        in Object s [(k, fromJson v) | (k, v) <- ps']

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
                | ["#TextMap", JsonSpec]
                | ["#Refined", JsonSpec]
                | ["#Or", JsonSpec, JsonSpec] )
            | Array (JsonSpec | "#Tolerant")
            | TextMap (JsonSpec | "#Tolerant")
        |]

    decs = either error id (parseFile textInput)
    env = either (error . show) id (checkEnv (M.fromList decs))

