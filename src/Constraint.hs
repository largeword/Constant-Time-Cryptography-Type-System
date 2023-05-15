{-# LANGUAGE InstanceSigs #-}

module Constraint(
  ConstraintT(..),
  Constraint,
  Constraints,
  emptyConstraints
) where

import Type
import Data.Set
import AST (Expr)

-- constraint datatype

type Constraint = ConstraintT Expr AnnotationVar

type Constraints = Set Constraint

-- Constraint: LowConf b: b <= L, HighConf b: H <= b, LowerThan b1 b2: b1 <= b2
-- constraint rules: L <= L, L <= H, H <= H
data ConstraintT i a = LowConf i a | HighConf i a | LowerThan i a a

instance (Eq a) => Eq (ConstraintT i a) where
  (==) :: ConstraintT i a -> ConstraintT i a -> Bool
  (LowConf _ a1) == (LowConf _ a2) = a1 == a2
  (HighConf _ a1) == (HighConf _ a2) = a1 == a2
  (LowerThan _ a1 b1) == (LowerThan _ a2 b2) = a1 == a2 && b1 == b2
  _ == _ = False

instance (Ord a) => Ord (ConstraintT i a) where
  compare :: ConstraintT i a -> ConstraintT i a -> Ordering
  compare (LowConf _ a1) (LowConf _ a2) = compare a1 a2
  compare (HighConf _ a1) (HighConf _ a2) = compare a1 a2
  compare (LowerThan _ a1 b1) (LowerThan _ a2 b2) = case compare a1 a2 of
                                                      EQ -> compare b1 b2
                                                      t -> t
  compare c1 c2 = compare (ordinal c1) (ordinal c2)

ordinal :: ConstraintT i a -> Int
ordinal (LowConf _ _) = 0
ordinal (HighConf _ _) = 1
ordinal LowerThan {} = 2

instance (Show a) => Show (ConstraintT i a) where
  show (LowConf _ a) = show a ++ " ≤ L"
  show (HighConf _ a) = "H ≤ " ++ show a
  show (LowerThan _ a1 a2) = show a1 ++ " ≤ " ++ show a2

instance Functor (ConstraintT i) where
  fmap :: (a -> b) -> ConstraintT i a -> ConstraintT i b
  fmap f (LowConf i a) = LowConf i (f a)
  fmap f (HighConf i a) = HighConf i (f a)
  fmap f (LowerThan i a1 a2) = LowerThan i (f a1) (f a2)

emptyConstraints :: Constraints
emptyConstraints = empty
