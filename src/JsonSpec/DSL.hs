-- Copyright 2018 LuoChen (luochen1990@gmail.com). Apache License 2.0

-- | Spec DSL
module JsonSpec.DSL (
    parseFile, parseSpec
) where

import Text.Megaparsec.Debug
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

type Parser = ParsecT Void String Identity

pFile :: Parser [(Name, Spec)]
pFile = many (newline <|> spaceChar) *> many (pDeclaration <* many (newline <|> spaceChar))

pDeclaration :: Parser (Name, Spec)
pDeclaration = (,) <$> (toks "data " *> pName <* tok '=' <* optional (newline <* (toks "|?" <|> tok '|'))) <*> pSpec <* newline

pName :: Parser Name
pName = some alphaNumChar

pSpec :: Parser Spec
pSpec = makeExprParser (try pSpec') [
    [ Prefix (try (toks "Array") $> array) , Prefix (toks "TextMap" $> textmap)],
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

parseSpec :: String -> Either String Spec
parseSpec s = either (Left . errorBundlePretty) Right (runParser (pSpec <* space) "input" s)

parseFile :: String -> Either String [(Name, Spec)]
parseFile s = either (Left . errorBundlePretty) Right (runParser (pFile <* space) "input" s)

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

