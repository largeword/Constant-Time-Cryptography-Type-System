{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}

module Type (
  TypeScheme(..),
  LabelledType(..),
  Label(..),
  AnnotationVar(..),
  Type(..),
  TypeVar(..),
) where

data TypeScheme = Forall TypeVar TypeScheme | Type LabelledType

data LabelledType = LabelledType Type Label

data Label = L | H | LabelVar AnnotationVar
             deriving (Eq, Ord)

newtype AnnotationVar = AnnotationVar Int
                        deriving (Eq, Ord)

deriving instance Eq LabelledType

data Type
  = TNat
  | TBool
  | TFun LabelledType LabelledType
  | TArray LabelledType
  | TPair LabelledType LabelledType
  | TList LabelledType
  | TVar TypeVar

deriving instance Eq Type

newtype TypeVar = TypeVar Int
                  deriving (Eq, Ord)

instance Show TypeScheme where
  showsPrec _ (Forall var scheme) = showString "forall " . showsPrec 0 var . showString ": " . showsPrec 0 scheme
  showsPrec p (Type lt) = showsPrec p lt

instance Show LabelledType where
  showsPrec _ (LabelledType t l) = showsPrec 0 t . showsPrec 0 l

instance Show Type where
  showsPrec _ = \case
    TNat -> showString "Nat"
    TBool -> showString "Bool"
    TFun t1 t2 -> showString "(" . showsPrec 0 t1 . showString " -> " . showsPrec 0 t2 . showString ")"
    TArray t -> showString "(Array " . showsPrec 0 t . showString ")"
    TPair t1 t2 -> showString "(" . showsPrec 0 t1 . showString ", " . showsPrec 0 t2 . showString ")"
    TList t -> showString "(List " . showsPrec 0 t . showString ")"
    TVar v -> showsPrec 0 v

instance Show Label where
  showsPrec _ = \case
    H -> showString "ᴴ"
    L -> showString "ᴸ"
    LabelVar var  -> showString "^" . showsPrec 0 var . showString ""

instance Show TypeVar where
  showsPrec _ (TypeVar var) = showString "a" . showsSubscript var

instance Show AnnotationVar where
  showsPrec _ (AnnotationVar var) = showString "b" . showsSubscript var

showsSubscript :: Int -> ShowS
showsSubscript value = showString $ conv value
  where
    conv :: Int -> String
    conv x
      | x < 0 = '\'' : reverse (go (-x))
      | otherwise = reverse (go x)
    go :: Int -> String
    go x
      | r == 0 = subscript !! m : ""
      | otherwise = subscript !! m : go r
      where
        (r, m) = x `divMod` 10
    subscript = "₀₁₂₃₄₅₆₇₈₉"
