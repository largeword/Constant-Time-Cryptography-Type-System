{-# LANGUAGE LambdaCase #-}

module AST (
  Id, Expr(..), Operator(..), showInline
) where

import Data.List (intercalate)
import Type

type Id = String

data Expr
  = Nat Int
  | Bool Bool
  | Var Id
  | Let Id Expr Expr
  | Fn Id Expr
  | Fun Id Id Expr
  | App Expr Expr
  | IfThenElse Expr Expr Expr
  | Operator Operator Expr Expr
  | TypeAnnotation Expr LabelledType
  | Sequence Expr Expr

  -- Arrays
  | Array Expr Expr -- 'array e1 e2' creates an array of length e1, filled with e2
  | ArrayRead Expr Expr
  | ArrayWrite Expr Expr Expr

  -- Pairs
  | Pair Expr Expr
  | CasePair Expr Id Id Expr

  -- Lists
  | Nil
  | Cons Expr Expr
  | CaseList Expr Expr Id Id Expr

data Operator = Add | Subtract | Multiply | Divide | And | Or | Equals | NotEquals | LessThan
  deriving Eq

instance Show Operator where
  show Add = "+"
  show Subtract = "-"
  show Multiply = "*"
  show Divide = "/"
  show And = "&&"
  show Or = "||"
  show Equals = "=="
  show NotEquals = "!="
  show LessThan = "<"

instance Show Expr where
  showsPrec context = \case
    Nat i -> shows i
    Bool True -> showString "true"
    Bool False -> showString "false"
    Var x -> showString x
    Fn arg body ->
      showParen (context > 1) $
        showString "fn"
          . showString (" " ++ arg ++ " ->\n")
          . indent (showsPrec 1 body)
    Fun f arg body ->
      showParen (context > 1) $
        showString "fun"
          . showString (" " ++ f ++ " " ++ arg ++ " ->\n")
          . indent (showsPrec 1 body)
    App e1 e2 ->
      showParen (context > 10) $ showsPrec 10 e1 . showString " " . showsPrec 12 e2
    Let x e1 e2 ->
      showParen (context > 1) $
        showString ("let " ++ x ++ " =\n")
          . indent (showsPrec 1 e1)
          . showString "\nin\n"
          . indent (showsPrec 1 e2)
    IfThenElse condition true false ->
      showParen (context > 1) $
          showString "if\n"
          . indent (showsPrec 1 condition)
          . showString "\nthen\n"
          . indent (showsPrec 1 true)
          . showString "\nelse\n"
          . indent (showsPrec 1 false)
    TypeAnnotation e tp ->
      showParen (context > 1) $
        showsPrec 2 e . showString " :: " . showsPrec 1 tp
    Operator op e1 e2 ->
      let
        -- Precedence, left and right associativity
        (prec, left, right) = case op of
          Add -> (6, True, False)
          Subtract -> (6, True, False)
          Multiply -> (7, True, False)
          Divide -> (7, True, False)
          And -> (3, False, True)
          Or -> (2, False, True)
          _ -> (4, False, False)
      in
        showParen (context > prec) $
          showsPrec (if left then prec else prec + 1) e1
            . showString " "
            . shows op
            . showString " "
            . showsPrec (if right then prec else prec + 1) e2
    Pair e1 e2
      | trivial e1 && trivial e2 ->
        showString "(" . showsPrec 0 e1 . showString ", " . showsPrec 0 e2 . showString ")"
      | otherwise ->
        showString "(\n" . indent (showsPrec 0 e1) . showString ",\n" . showsPrec 0 e2 . showString "\n)"
    Nil -> showString "[]"
    Cons e1 e2 ->
      showParen (context > 5) $
        showsPrec 6 e1 . showString " : " . showsPrec 5 e2
    CasePair e1 x y e2 ->
      showParen (context > 1) $
        showString "case " . showsPrec 1 e1 . showString " of\n  (" . showString x . showString ", " . showString y . showString ") ->\n" . indent (indent (showsPrec 1 e2))
    CaseList e1 e2 x y e3 ->
      showParen (context > 1) $
        showString "case " . showsPrec 1 e1 . showString " of\n [] ->\n"
        . indent (indent (showsPrec 1 e2))
        . showString ",\n  " . showString x . showString " : " . showString y . showString " ->\n"
        . indent (indent (showsPrec 1 e3))
    Array e1 e2 ->
      showParen (context > 10) $ showString "array " . showsPrec 11 e1 . showString " " . showsPrec 11 e2
    ArrayRead array idx
      | trivial idx ->
        showParen (context > 11) $
          showsPrec 11 array . showString "[" . showsPrec 0 idx . showString "]"
      | otherwise ->
        showParen (context > 11) $
          showsPrec 11 array . showString "[\n" . indent (showsPrec 0 idx) . showString "\n]"
    ArrayWrite array idx value
      | trivial idx ->
        showParen (context > 1) $
          showsPrec 11 array . showString "[" . showsPrec 0 idx . showString "] = " . showsPrec 0 value
      | otherwise ->
        showParen (context > 1) $
          showsPrec 11 array . showString "[\n" . indent (showsPrec 0 idx) . showString "\n] = " . showsPrec 0 value
    Sequence e1 e2
      | context == 0 ->
        showsPrec 0 e1 . showString ";\n" . showsPrec 0 e2
      | otherwise ->
        showString "(\n" . indent (showsPrec 0 e1) . showString ";\n" . indent (showsPrec 0 e2) . showString ")"

indent :: ShowS -> ShowS
indent s = showString $ intercalate "\n" $ map ("  " ++) $ lines $ s ""

trivial :: Expr -> Bool
trivial = go 8
  where
    go :: Int -> Expr -> Bool
    go 0 = const False
    go fuel = \case
      Nat _ -> True
      Var _ -> True
      App e1 e2 -> go (fuel - 1) e1 && go (fuel - 1) e2
      ArrayRead e1 e2 -> go (fuel - 1) e1 && go (fuel - 1) e2
      Operator _ e1 e2 -> go (fuel - 1) e1 && go (fuel - 1) e2
      Pair e1 e2 -> go (fuel - 1) e1 && go (fuel - 1) e2
      Nil -> True
      Cons e1 e2 -> go (fuel - 1) e1 && go (fuel - 1) e2
      _ -> False

showInline :: Expr -> String
showInline = unwords . words . show
