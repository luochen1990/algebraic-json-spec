-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

-- | Spec DSL
module JsonSpec.DSL (
    parseFile, parseSpec, parseJsonData, parseExpr
) where

import Text.Megaparsec hiding (sepBy, sepBy1)
import Text.Megaparsec.Char hiding (space, space1, spaceChar)
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Combinators.Expr
import qualified Data.Map as M
import Data.Fix
import Data.Char
import Data.Void
import Data.Functor
import Control.Monad.Identity
import Control.Monad.State
import JsonSpec.Core.Definitions
import JsonSpec.Core.Functions
import JsonSpec.EDSL
-- import Text.Megaparsec.Debug
dbg = const id

type Parser = ParsecT Void String Identity

pFile :: Parser [(Name, Spec)]
pFile = many (newline <|> spaceChar) *> many (pDeclaration <* many (newline <|> spaceChar))

pDeclaration :: Parser (Name, Spec)
pDeclaration = (,) <$> (toks "data " *> pName <* tok '=' <* optional (newline <* (toks "|?" <|> tok '|'))) <*> pSpec <* newline

pName :: Parser Name
pName = some alphaNumChar

pSpec :: Parser Spec
pSpec = makeExprParser (pSpec') [
    [ Prefix ((toks "Array") $> array) , Prefix (toks "Dict" $> dict)],
    [ Postfix ((toks "<{" *> pExpr <* toks "}>") >>= \p -> pure (\sp -> Fix (Refined sp p)))],
    [ InfixR (try (optional (try (space >> newline)) *> (toks "|?" <|> tok '|')) $> (<|||>)) ]
    ]

pSpec' :: Parser Spec
pSpec' = toks "Anything" $> Fix Anything
    <|> toks "Null" $> cnull
    <|> toks "Boolean" $> boolean
    <|> toks "Number" $> number
    <|> toks "Text" $> text
    <|> cboolean <$> pLitBoolean
    <|> cnumber <$> pLitNumber
    <|> ctext <$> pLitText
    <|> (do
        ts <- tok '[' *> pSpec `sepBy` tok ','
        star <- optional ((when (not (null ts)) (tok ',')) *> (tok '*'))
        tok ']'
        pure (Fix (Tuple (maybe Strict (const Tolerant) star) ts))
        )
    <|> (do
        ps <- tok '{' *> ((,) <$> (pKey <* tok ':') <*> pSpec) `sepBy` tok ','
        star <- optional ((when (not (null ps)) (tok ',')) *> (tok '*'))
        tok '}'
        pure (Fix (Object (maybe Strict (const Tolerant) star) ps))
        )
    <|> ref <$> pName
    <|> tok '(' *> pSpec <* tok ')'

pLitNumber :: Parser Double
pLitNumber = (char '-' $> negate <|> pure id) <*> L.float

pLitText :: Parser String
pLitText = char '"' *> many (pSpecialChar <|> anySingleBut '"') <* char '"'

pSpecialChar :: Parser Char
pSpecialChar = char '\\' *> (char '"' <|> char '\\') --TODO: more special chars

pLitBoolean :: Parser Bool
pLitBoolean = toks "True" $> True <|> toks "False" $> False

pKey :: Parser String
pKey = some alphaNumChar <|> pLitText

pNat :: Parser Int
pNat = read <$> some digitChar

pExpr :: Parser Expr
pExpr = dbg "pExpr" $ makeExprParser (try pExpr') [
    [ Postfix ((foldl1 (flip (.))) <$> some pAccessor) ],
    [ Prefix (try pUnaOp) ],
    [ InfixL (try pBinOp1L) ],
    [ InfixL (try pBinOp2L) ],
    [ InfixL (try pBinOp3L) ],
    [ InfixL (try pBinOp4L) ]
    ]

pAccessor :: Parser (Expr -> Expr)
pAccessor = (try (tok '.' *> pKey) >>= \k -> pure (\e -> Dot e k))
    <|> (try (tok '[' *> pNat <* tok ']') >>= \i -> pure (\e -> Idx e i))

pExpr' :: Parser Expr
pExpr' = dbg "pExpr'" $ toks "it" $> It
    <|> Lit <$> pJsonData
    <|> tok '(' *> pExpr <* tok ')'

pUnaOp :: Parser (Expr -> Expr)
pUnaOp =
        toks "len" $> Pfx LenOp
    <|> toks "not" $> Pfx NotOp

pBinOp1L, pBinOp2L, pBinOp3L, pBinOp4L :: Parser (Expr -> Expr -> Expr)

pBinOp1L =
        toks "*"  $> (\a b -> Ifx a MulOp b)
    <|> toks "/"  $> (\a b -> Ifx a DivOp b)
    <|> toks "%"  $> (\a b -> Ifx a ModOp b)

pBinOp2L =
        toks "+"  $> (\a b -> Ifx a AddOp b)
    <|> toks "-"  $> (\a b -> Ifx a SubOp b)

pBinOp3L =
        toks "="  $> (\a b -> Ifx a EqOp b)
    <|> toks "!=" $> (\a b -> Ifx a NeOp b)
    <|> toks "<"  $> (\a b -> Ifx a LtOp b)
    <|> toks ">"  $> (\a b -> Ifx a GtOp b)
    <|> toks "<=" $> (\a b -> Ifx a LeOp b)
    <|> toks ">=" $> (\a b -> Ifx a GeOp b)

pBinOp4L =
        toks "and" $> (\a b -> Ifx a AndOp b)
    <|> toks "or"  $> (\a b -> Ifx a OrOp b)

pJsonData :: Parser JsonData
pJsonData =
        JsonNumber <$> pLitNumber
    <|> JsonText <$> pLitText
    <|> JsonBoolean <$> pLitBoolean
    <|> JsonNull <$ toks "null"
    <|> JsonArray <$> (tok '[' *> (pJsonData `sepBy` tok ',') <* tok ']')
    <|> JsonObject <$> (tok '{' *> (((,) <$> ((pKey <|> pLitText) <* tok ':') <*> pJsonData) `sepBy` tok ',') <* tok '}')

parseJsonData :: String -> Either String JsonData
parseJsonData s = either (Left . errorBundlePretty) Right (runParser (pJsonData <* space <* eof) "input" s)

parseExpr :: String -> Either String Expr
parseExpr s = either (Left . errorBundlePretty) Right (runParser (pExpr <* space <* eof) "input" s)

parseSpec :: String -> Either String Spec
parseSpec s = either (Left . errorBundlePretty) Right (runParser (pSpec <* space <* eof) "input" s)

parseFile :: String -> Either String [(Name, Spec)]
parseFile s = either (Left . errorBundlePretty) Right (runParser (pFile <* space <* eof) "input" s)

-- ** conbinators

spaceChar :: Parser Char
spaceChar = (char ' ' <|> tab)

space :: Parser ()
space = many spaceChar $> ()

tok :: Char -> Parser ()
tok c = () <$ try (space *> char c <* space)

toks :: String -> Parser ()
toks s | isAlphaNum (last s) = () <$ try (space *> string s <* notFollowedBy alphaNumChar <* space)
toks s = () <$ try (space *> string s <* space)

sepBy1 :: Parser a -> Parser b -> Parser [a]
sepBy1 p op = liftM2 (:) p (many (try (op *> p)))

sepBy :: Parser a -> Parser b -> Parser [a]
sepBy p op = liftM2 (:) p (many (try (op *> p))) <|> pure []


s1 = "([[(Dict (Null |? True)), (Array Null)], *] <{ ((len it[0][1]) < 42.0) }>)"
s2 = "([[(Dict Null), (Array Null)], *] <{ ((len it[0][1]) < 42.0) }>)"
s3 = "([[(Dict Null)], *] <{ ((len it[0][1]) < 42.0) }>)"
s4 = "([(Dict Null), *] <{ ((len it[0][1]) < 42.0) }>)"
s5 = "([Dict Null, *] <{ ((len it[0][1]) < 42.0) }>)"
s6 = "([Null, *] <{ ((len it[0][1]) < 42.0) }>)"
s7 = "(Null <{ ((len it[0][1]) < 42.0) }>)"
s8 = "(Null <{ ((len it[0][1]) < 1.0) }>)"
s9 = "(Null <{ (it[0][1] < 1.0) }>)"
s10 = "(Null <{ (it[0][0] < 1.0) }>)"
s11 = "Null <{ (it[0][0] < 1.0) }>"
b3 = "(Null <{ (it[0] < 1.0) }>)"
b2 = "(Null <{ ((len it) < 1.0) }>)"
b1 = "([Null, *] <{ ((len it) < 42.0) }>)"

ss1 = "((len it[0].b) < 42.0)"
ss2 = "it.a.b"
ss3 = "((len it.d[0]) < 42.0)"

