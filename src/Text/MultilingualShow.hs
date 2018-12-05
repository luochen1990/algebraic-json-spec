-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

{-# language RankNTypes #-}
{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}

module Text.MultilingualShow where

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

instance {-# Overlappable #-} Show a => MultilingualShow a where
    showEnWith _ = show

