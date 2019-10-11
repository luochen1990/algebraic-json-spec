-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

-- | Spec EDSL
module JsonSpec.EDSL where

import Data.Fix
import JsonSpec.Core.Definitions (TyRep(..), Strictness(..), DecProp(..), JsonData(..), Spec, Name)

tuple, tuple' :: [Spec] -> Spec
tuple ts = Fix (Tuple Strict ts)
tuple' ts = Fix (Tuple Tolerant ts)

object, object' :: [(Name, Spec)] -> Spec
object ps = Fix (Object Strict ps)
object' ps = Fix (Object Tolerant ps)

dict, array :: Spec -> Spec
dict t = Fix (Dict t)
array t = Fix (Array t)

boolean, number, text, cnull :: Spec
boolean = Fix Boolean
number = Fix Number
text = Fix Text
cnull = Fix Null

cboolean :: Bool -> Spec
cboolean b = Fix (ConstBoolean b)

cnumber :: Double -> Spec
cnumber n = Fix (ConstNumber n)

ctext :: String -> Spec
ctext s = Fix (ConstText s)

ref :: Name -> Spec
ref s = Fix (Ref s)

refined :: Spec -> DecProp -> Spec
refined sp prop = Fix (Refined sp prop)

-- | infix constructor of an Or node
(<|||>) :: Spec -> Spec -> Spec
a <|||> b = Fix $ Or a b ()
infixr 9 <|||>

