module Constraint(
  Constraint(..),
  Constraints,
  emptyConstraints,
  singleConstraint
) where

import Type
import Data.Set

-- constraint datatype

-- Constraint l1 l2 means l1 <= l2, where L <= L, L <= H and H <= H
data Constraint = Constraint Label Label
                  deriving (Eq, Ord)

type Constraints = Set Constraint

emptyConstraints :: Constraints
emptyConstraints = empty

singleConstraint :: Label -> Label -> Constraints
singleConstraint l1 l2 = singleton (Constraint l1 l2)
