{-# LANGUAGE LambdaCase #-}

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
data Label = H | L | LabelVar AnnotationVar
newtype AnnotationVar = AnnotationVar Int

data Type
  = TNat
  | TBool
  | TFun LabelledType LabelledType
  | TArray LabelledType
  | TPair LabelledType LabelledType
  | TList LabelledType
  | TVar TypeVar

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
showsSubscript value = showString $ reverse (go value)
  where
    go :: Int -> String
    go x
      | x < 0 = error "Negative value"
      | r == 0 = subscript !! m : ""
      | otherwise = subscript !! m : go r
      where
        (r, m) = x `divMod` 10
    subscript = "₀₁₂₃₄₅₆₇₈₉"
