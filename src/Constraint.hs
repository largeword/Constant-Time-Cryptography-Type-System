{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}

module Constraint(
  ConstraintT(..),
  Constraint,
  Constraints,
  emptyConstraints
) where

import Type
import Data.Set

-- constraint datatype

type Constraint = ConstraintT AnnotationVar

type Constraints = Set Constraint

-- Constraint: LowConf b: b <= L, HighConf b: H <= b, LowerThan b1 b2: b1 <= b2
-- constraint rules: L <= L, L <= H, H <= H
data ConstraintT a = LowConf a | HighConf a | LowerThan a a

deriving instance (Show a) => Show (ConstraintT a)
deriving instance (Eq a) => Eq (ConstraintT a)
deriving instance (Ord a) => Ord (ConstraintT a)

instance Functor ConstraintT where
  fmap :: (a -> b) -> ConstraintT a -> ConstraintT b
  fmap f (LowConf a) = LowConf (f a)
  fmap f (HighConf a) = HighConf (f a)
  fmap f (LowerThan a1 a2) = LowerThan (f a1) (f a2)

emptyConstraints :: Constraints
emptyConstraints = empty
