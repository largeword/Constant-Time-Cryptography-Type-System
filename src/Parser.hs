module Parser (
  parse
) where

import AST
import Type
import Text.Parsec hiding (parse)
import qualified Text.Parsec as Parsec
import Control.Monad

import Data.List (foldl')
import Data.Char (digitToInt)

parse :: String -> String -> Either ParseError Expr
parse = Parsec.parse (pExpr <* eof)

type Parser = Parsec String ()

pWhitespace :: Parser ()
pWhitespace = skipMany (void space <|> lineComment <|> blockComment)
  where
    lineComment :: Parser ()
    lineComment = () <$ try (string "--") <* manyTill anyChar newline

    blockComment :: Parser ()
    blockComment = () <$ try (string "{-") <* manyTill anyChar (try (string "-}"))

pInt :: Parser Int
pInt = foldl' (\accum chr -> 10 * accum + digitToInt chr) 0 <$> many1 digit

pAtom :: Parser Expr
pAtom
  = Nat <$> pInt <* pWhitespace
  <|> Bool True <$ pKeyword "true" <* pWhitespace
  <|> Bool False <$ pKeyword "false" <* pWhitespace
  <|> Nil <$ string "[]" <* pWhitespace
  <|> Var <$> pIdentifier <* pWhitespace
  <|> pParens

pParens :: Parser Expr
pParens = do
  base <- char '(' *> pWhitespace *> pExpr
  option base (Pair base <$ char ',' <* pWhitespace <*> pExpr) <* char ')' <* pWhitespace

pIndex :: Parser Expr
pIndex = do
  base <- pAtom
  indices <- many (char '[' *> pWhitespace *> pExpr <* char ']' <* pWhitespace)
  return $ foldl ArrayRead base indices

pApp :: Parser Expr
pApp =
  Array <$ pKeyword "array" <* pWhitespace <*> pAtom <*> pAtom
  <|> (do
    base <- pIndex
    args <- many pAtom
    return $ foldl App base args
  )

pExpr7 :: Parser Expr
pExpr7 = chainl1 pApp (Operator Multiply <$ char '*' <* pWhitespace <|> Operator Divide <$ char '/' <* pWhitespace)

pExpr6 :: Parser Expr
pExpr6 = chainl1 pExpr7 (Operator Add <$ char '+' <* pWhitespace <|> Operator Subtract <$ char '-' <* pWhitespace)

pExpr5 :: Parser Expr
pExpr5 = chainr1 pExpr6 (Cons <$ pCons <* pWhitespace)

pExpr4 :: Parser Expr
pExpr4 = do
  left <- pExpr5
  option left (Operator <$> op <*> return left <* pWhitespace <*> pExpr6)
  where
    op :: Parser (Operator)
    op = Equals <$ try (string "==")
      <|> NotEquals <$ try (string "!=")
      <|> LessThan <$ char '<'

pExpr3 :: Parser Expr
pExpr3 = chainr1 pExpr4 (Operator And <$ string "&&" <* pWhitespace)

pExpr2 :: Parser Expr
pExpr2 = chainr1 pExpr3 (Operator Or <$ string "||" <* pWhitespace)

pExpr2OrWrite :: Parser Expr
pExpr2OrWrite = do
  base <- pExpr2
  case base of
    ArrayRead arr idx ->
      option base $ ArrayWrite arr idx <$ char '=' <* pWhitespace <*> pExpr1
    _ -> return base

pExpr1Base :: Parser Expr
pExpr1Base = IfThenElse <$ pKeyword "if" <* pWhitespace <*> pExpr1 <* pKeyword "then" <* pWhitespace <*> pExpr1 <* pKeyword "else" <* pWhitespace <*> pExpr1
  <|> Let <$ pKeyword "let" <* pWhitespace <*> pIdentifier <* pWhitespace <* char '=' <* pWhitespace <*> pExpr1 <* pKeyword "in" <* pWhitespace <*> pExpr1
  <|> Fn <$ pKeyword "fn" <* pWhitespace <*> pIdentifier <* pWhitespace <* string "->" <* pWhitespace <*> pExpr1
  <|> Fun <$ pKeyword "fun" <* pWhitespace <*> pIdentifier <* pWhitespace <*> pIdentifier <* pWhitespace <* string "->" <* pWhitespace <*> pExpr1
  <|> createCase <$ pKeyword "case" <* pWhitespace <*> pExpr1 <* pKeyword "of" <* pWhitespace <*> pAlternatives
  <|> pExpr2OrWrite

pExpr1 :: Parser Expr
pExpr1 = do
  base <- pExpr1Base
  option base (TypeAnnotation base <$ string "::" <* pWhitespace <*> pLabelledType <*  pWhitespace)

pExpr :: Parser Expr
pExpr = chainl1 pExpr1 (Sequence <$ char ';' <* pWhitespace)

pKeyword :: String -> Parser ()
pKeyword name = try (string name >> notFollowedBy alphaNum)

pIdentifier :: Parser Id
pIdentifier = try $ do
  name <- (:) <$> (letter <|> char '_') <*> many (alphaNum <|> char '_')
  if name `elem` ["fn", "fun", "let", "in", "if", "then", "else", "alloc", "nil", "case", "of", "Int", "Bool", "Array", "List"] then
    fail $ "expected identifier, '" ++ name ++ "' is a keyword"
  else
    return name

-- Utilities for parsing case-expressions
data CaseAlternatives = AltPair Id Id Expr | AltList Expr Id Id Expr
createCase :: Expr -> CaseAlternatives -> Expr
createCase scrutinee (AltPair x y body) = CasePair scrutinee x y body
createCase scrutinee (AltList e1 x y e2) = CaseList scrutinee e1 x y e2

pAlternatives :: Parser CaseAlternatives
pAlternatives
  = AltPair <$ char '(' <* pWhitespace <*> pIdentifier <* pWhitespace <* char ','
    <* pWhitespace <*> pIdentifier <* pWhitespace <* char ')'
    <* arrow <*> pExpr1
  <|> altList' <$> pIdentifier <* pWhitespace <* pCons <* pWhitespace <*> pIdentifier <* arrow <*> pExpr1
    <* char ',' <* pWhitespace <* string "[]" <* arrow <*> pExpr1
  <|> AltList <$ string "[]" <* arrow <*> pExpr1
    <* char ',' <* pWhitespace <*> pIdentifier <* pWhitespace <* pCons <* pWhitespace <*> pIdentifier <* arrow <*> pExpr1
  where
    altList' :: Id -> Id -> Expr -> Expr -> CaseAlternatives
    altList' x y e2 e1 = AltList e1 x y e2
    arrow = pWhitespace <* string "->" <* pWhitespace

-- Parser that matches ':' (the list constructor), but not '::' (for type assertions)
pCons :: Parser Char
pCons = try (char ':' <* notFollowedBy (char ':'))

-- Parsers for types
pLabelledType :: Parser LabelledType
pLabelledType = LabelledType <$> pTypeAtom <*> pLabel

pLabel :: Parser Label
pLabel
  = (H <$ char 'ᴴ' <?> "ᴴ")
  <|> (L <$ char 'ᴸ' <?> "ᴸ")
  <|> char '^' *> pSuperscript
  where
    pSuperscript
      = L <$ string "L" <|> H <$ string "H" <|> LabelVar <$> pAnnotationVar

pAnnotationVar :: Parser AnnotationVar
pAnnotationVar = AnnotationVar <$ char 'b' <*> pSubscriptNumber

pTypeAtom :: Parser Type
pTypeAtom
  = TNat <$ pKeyword "Nat"
  <|> TBool <$ pKeyword "Bool"
  <|> TVar <$> pTypeVar
  <|> pTypeParens

pTypeParens :: Parser Type
pTypeParens = do
  base <- char '(' *> pWhitespace *> pType
  option base (pair base <$> pLabel <* pWhitespace <* char ',' <* pWhitespace <*> pLabelledType <* pWhitespace) <* char ')'
  where
    pair left leftLabel right = TPair (LabelledType left leftLabel) right

-- Returns the parsed type, and whether that type was atomic
pTypeApp :: Parser (Bool, Type)
pTypeApp = (\t -> (True, t)) <$> pTypeAtom
  <|> (\t -> (False, TArray t)) <$ pKeyword "Array" <* pWhitespace <*> pLabelledType
  <|> (\t -> (False, TList t)) <$ pKeyword "List" <* pWhitespace <*> pLabelledType

pType :: Parser Type
pType = do
  (atomic, base) <- pTypeApp
  if atomic then
    -- We might just have parsed the first argument of a function type
    option base (fun base <$> try (pLabel <* pWhitespace <* string "->") <* pWhitespace <*> pLabelledType)
  else
    return base
  where
    fun arg argLabel ret = TFun (LabelledType arg argLabel) ret

pTypeVar  :: Parser TypeVar
pTypeVar = TypeVar <$ char 'a' <*> pSubscriptNumber

pSubscriptNumber :: Parser Int
pSubscriptNumber = foldl' (\accum i -> 10 * accum + i) 0 <$> many1 (digit' <?> "digit")
  where
    digit' = digitToInt <$> digit
      <|> 0 <$ char '₀'
      <|> 1 <$ char '₁'
      <|> 2 <$ char '₂'
      <|> 3 <$ char '₃'
      <|> 4 <$ char '₄'
      <|> 5 <$ char '₅'
      <|> 6 <$ char '₆'
      <|> 7 <$ char '₇'
      <|> 8 <$ char '₈'
      <|> 9 <$ char '₉'
