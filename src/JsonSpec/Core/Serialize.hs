-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

-- Binary serialization & deserialization
module JsonSpec.Core.Serialize (serializeJ, deserializeJ, serialList, deserialList) where

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Semigroup
import Data.Foldable (fold, foldMap)
import Data.List
import Data.Maybe
import Data.Fix
import Data.Char (isAlphaNum)
import Text.MultilingualShow
import Control.Monad.State
import JsonSpec.Core.Definitions
import GHC.Exts (sortWith)

import Data.Bytes.Serial
import Data.Bytes.Put
import Data.Bytes.Get
import Data.Bytes.VarInt
import Data.Word (Word8)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Serialize.Put (Put)
import Data.Serialize.Get (Get)

word :: Int -> Word8
word x = fromIntegral x

serialList :: (MonadPut m, Serial a) => [a] -> m ()
serialList xs = serialize (VarInt (length xs)) >> sequence_ (map serialize xs)

deserialList :: (MonadGet m, Serial a) => m [a]
deserialList = do
    (VarInt n) <- deserialize
    xs <- replicateM n deserialize
    return xs

instance Serial JsonData where
    serialize d = case d of
        JsonNull -> putWord8 0
        JsonNumber x -> putWord8 1 >> serialize x
        JsonText s -> putWord8 2 >> serialList s
        JsonBoolean b -> putWord8 (3 + (if b then 1 else 0))
        JsonArray xs -> putWord8 5 >> serialList xs
        JsonObject ps -> putWord8 6 >> serialList ps
    deserialize = do
        tag <- getWord8
        case tag of
            0 -> pure JsonNull
            1 -> JsonNumber <$> deserialize
            2 -> JsonText <$> deserialList
            3 -> pure (JsonBoolean False)
            4 -> pure (JsonBoolean True)
            5 -> JsonArray <$> deserialList
            6 -> JsonObject <$> deserialList

serializeJ :: Env CSpec -> CSpec -> JsonData -> ByteString
serializeJ env spec d = runPutS (seri spec d)
    where
        seri :: CSpec -> JsonData -> Put
        seri (Fix tr) d = case (tr, d) of
            (Anything, _) -> serialize d
            (Number, (JsonNumber x)) -> serialize x
            (Text, (JsonText s)) -> serialize s
            (Boolean, (JsonBoolean b)) -> serialize b
            (Null, JsonNull) -> pure ()
            (ConstNumber n, (JsonNumber n')) -> if n == n' then pure () else error "not match"
            (ConstText s, (JsonText s')) -> if s == s' then pure () else error "not match"
            (ConstBoolean b, (JsonBoolean b')) -> if b == b' then pure () else error "not match"
            (Tuple Strict ts, (JsonArray xs)) -> if length ts == length xs then sequence_ (zipWith seri ts xs) else error "not match"
            (Tuple Tolerant ts, (JsonArray xs)) -> serialList xs --TODO: optmize
            (Array t, (JsonArray xs)) -> serialize (VarInt (length xs)) >> sequence_ (map (seri t) xs)
            (Object Strict ps, (JsonObject kvs)) ->
                if length ps == length kvs then
                    let ps' = sortWith fst ps
                        mp = M.fromList kvs
                    in sequence_ [seri t (mp M.! k) | (k, t) <- ps']
                else error "not match"
            (Object Tolerant ps, (JsonObject kvs)) -> serialList kvs --TODO: optmize
            (TextMap t, (JsonObject kvs)) -> serialize (VarInt (length kvs)) >> sequence_ [serialize k >> seri t v | (k, v) <- kvs]
            (Refined t _, _) -> seri t d
            (Ref r, _) -> seri (env M.! r) d
            (Or a b c, _) -> case makeChoice c d of
                MatchLeft -> putWord8 0 >> seri a d
                MatchRight -> putWord8 1 >> seri b d
                MatchNothing -> error "not match"
            _ -> error "not match"

deserializeJ :: Env CSpec -> CSpec -> ByteString -> JsonData
deserializeJ env spec bs = case runGetS (deseri spec) bs of
    Left msg -> error ("deserializeJ failed: " ++ msg)
    Right r -> r
    where
        deseri (Fix tr) = case tr of
            Anything -> deserialize
            Number -> JsonNumber <$> deserialize
            Text -> JsonText <$> deserialize
            Boolean -> JsonBoolean <$> deserialize
            Null -> pure JsonNull
            ConstNumber n -> pure (JsonNumber n)
            ConstText s -> pure (JsonText s)
            ConstBoolean b -> pure (JsonBoolean b)
            Tuple Strict ts -> JsonArray <$> sequence (map deseri ts)
            Tuple Tolerant ts -> JsonArray <$> deserialList --TODO: optmize
            Array t -> do
                (VarInt n) <- deserialize
                xs <- replicateM n (deseri t)
                return $ JsonArray xs
            Object Strict ps ->
                let ps' = sortWith fst ps
                in JsonObject <$> sequence [liftM2 (,) (pure k) (deseri t) | (k, t) <- ps']
            Object Tolerant ps -> JsonObject <$> deserialList --TODO: optmize
            TextMap t -> do
                (VarInt n) <- deserialize
                kvs <- replicateM n (liftM2 (,) deserialize (deseri t))
                return $ JsonObject kvs
            Ref r -> deseri (env M.! r)
            Refined t _ -> deseri t
            Or a b _ -> do
                bit <- deserialize
                if bit then deseri b else deseri a

