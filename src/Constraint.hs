{-# LANGUAGE InstanceSigs #-}

module Constraint(
  ConstraintT(..),
  Constraint,
  Constraints,
  emptyConstraints,
  solve
) where

import Type
import Data.Set as Set
import AST (Expr, showInline)
import Control.Monad.State
import Control.Monad.Except

import Data.Map as Map (Map, lookup, insert, empty, elems)
import Data.Maybe (fromMaybe)
import Data.Graph (SCC (AcyclicSCC, CyclicSCC), stronglyConnComp)
import Control.Monad.Trans.Except (throwE)
import Data.Foldable (traverse_)
import Debug.Trace (trace)

-- constraint datatype
type Constraint = ConstraintT Metadata AnnotationVar

type Metadata = Expr

showMetadata :: Metadata -> String
showMetadata = showInline

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
  compare (LowerThan _ a1 b1) (LowerThan _ a2 b2)
    | b1 == a2 = LT
    | b2 == a1 = GT
    | otherwise = case compare a1 a2 of
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
emptyConstraints = Set.empty

type ConstraintGraph = ([Constraint], Label, [Label])

type SolvingContext = ExceptT String (State (Map AnnotationVar Label))

solve :: TypeScheme -> Constraints -> Either String TypeScheme
solve ts c = do
                m <- runBruteSolver c
                return $ replaceLabels (trace (show m) m) ts

replaceLabels :: Map AnnotationVar Label -> TypeScheme -> TypeScheme
replaceLabels m (Forall a ts) = Forall a $ replaceLabels m ts
replaceLabels m (Type lt) = Type $ replaceLabelsLT m lt

replaceLabelsLT :: Map AnnotationVar Label -> LabelledType -> LabelledType
replaceLabelsLT m (LabelledType t l) = LabelledType (replaceLabelsT m t) (replaceLbl m l)

replaceLabelsT :: Map AnnotationVar Label -> Type -> Type
replaceLabelsT m (TFun t1 t2)  = TFun (replaceLabelsLT m t1) (replaceLabelsLT m t2)
replaceLabelsT m (TPair t1 t2) = TPair (replaceLabelsLT m t1) (replaceLabelsLT m t2)
replaceLabelsT m (TArray t)    = TArray (replaceLabelsLT m t)
replaceLabelsT m (TList t)     = TList (replaceLabelsLT m t)
replaceLabelsT _ t = t

replaceLbl :: Map AnnotationVar Label -> Label -> Label
replaceLbl m (LabelVar a) = fromMaybe L $ Map.lookup a m
replaceLbl _ l = l

runBruteSolver :: Constraints -> Either String (Map AnnotationVar Label)
runBruteSolver cs = evalState (runExceptT (bruteSolver cs)) Map.empty

bruteSolver :: Constraints -> SolvingContext (Map AnnotationVar Label)
bruteSolver cons = do
                     let csl = toList cons
                     splitted <- initAndSplit csl
                     fillUntilUnchanged splitted
                     get

fillUntilUnchanged :: [Constraint] -> SolvingContext ()
fillUntilUnchanged cs = do
                          (changed, cs') <- fillAndFilter cs
                          if changed then
                            fillUntilUnchanged cs'
                          else
                            return ()
                        -- where fills = foldM (\a c -> (|| a) <$> fill c) False cs

fillAndFilter :: [Constraint] -> SolvingContext (Bool, [Constraint])
fillAndFilter cs = runDiff <$> foldM go (False, id) cs
                    where
                      runDiff (res, diff) = (res, diff [])
                      go (ch, acc) c = do changed <- fill c
                                          if changed then return (True, acc)
                                          else return (ch, acc . (c:))

-- initAndSplit calling order assumption: LowConf first, then HighConf, then LowerThan
initAndSplit :: [Constraint] -> SolvingContext [Constraint]
initAndSplit [] = return []
initAndSplit ((LowConf _ a):cs) = do
                                    m <- get
                                    put $ Map.insert a L m
                                    initAndSplit cs
initAndSplit ((HighConf i a):cs) = do
                                    m <- get
                                    if Map.lookup a m == Just L
                                    then throwE $ "CTC secret value violated in " ++ showMetadata i
                                    else put $ Map.insert a H m
                                    initAndSplit cs
initAndSplit cs = return cs

fill :: Constraint -> SolvingContext Bool
fill (LowerThan i a1 a2) = do
                              m <- get
                              let l1 = LabelVar a1
                              let l2 = LabelVar a2
                              let v1 = fromMaybe l1 $ Map.lookup a1 m
                              let v2 = fromMaybe l2 $ Map.lookup a2 m
                              (fill1, fill2, changed) <- makeFill i v1 v2
                              if changed then
                                let update1 = Map.insert a1 fill1
                                    update2 = Map.insert a2 fill2 in
                                put (update1 $ update2 m) >> return True
                              else
                                return False
fill _ = return False

makeFill :: Metadata -> Label -> Label -> SolvingContext (Label, Label, Bool)
makeFill _ (LabelVar {}) L = return (L, L, True)
makeFill _ H (LabelVar {}) = return (H, H, True)
makeFill i H L = throwE $ "CTC secret value violation in " ++ showMetadata i
makeFill _ l1 l2 = return (l1, l2, False)

-------

runSolver :: Constraints -> Either String (Map AnnotationVar Label)
runSolver cs = evalState (runExceptT (sortAndFill cs)) Map.empty

-- initAndFilter calling order assumption: LowConf first, then HighConf, then LowerThan
initAndFilter :: Constraint -> SolvingContext Bool
initAndFilter (LowConf _ a) = do
                                  m <- get
                                  put $ Map.insert a L m
                                  return False
initAndFilter (HighConf i a) = do
                                  m <- get
                                  if Map.lookup a m == Just L
                                  then throwE $ "CTC secret value violated in " ++ showMetadata i
                                  else put $ Map.insert a H m
                                  return False
initAndFilter (LowerThan _ l1 l2) = do
                                    initVar l1
                                    initVar l2
                                    return True

initVar :: AnnotationVar -> SolvingContext ()
initVar k = do
              m <- get
              let l = LabelVar k
              if Map.lookup k m == Nothing then
                put $ Map.insert k l m
              else return ()

sortAndFill :: Constraints -> SolvingContext (Map AnnotationVar Label)
sortAndFill cs = do
                 let csl = toList cs -- csl is sorted by LowConf < HighConf < LowerThan
                 lowerOnly <- filterM initAndFilter csl
                 let sorted = toposortConstraints lowerOnly
                 traverse_ fillSCConstraint sorted
                 get

fillSCConstraint :: SCC [Constraint] -> SolvingContext ()
fillSCConstraint (AcyclicSCC cs) = traverse_ fillConstraint cs
fillSCConstraint (CyclicSCC cs) = traverse_ fillConstraint (concat cs)

fillConstraint :: Constraint -> SolvingContext ()
fillConstraint (LowerThan i a1 a2) = do
                                        m <- get
                                        let l1 = LabelVar a1
                                        let l2 = LabelVar a2
                                        let v1 = fromMaybe l1 $ Map.lookup a1 m
                                        let v2 = fromMaybe l2 $ Map.lookup a2 m

                                        let fill1 = if isLabelVar v1 then L else v1 -- default to L if empty
                                        let fill2 = if isLabelVar v2 then fill1 else v2 -- default to l1's value if empty

                                        validateFill i l1 l2 fill1 fill2
                                        let update1 = Map.insert a1 fill1
                                        let update2 = Map.insert a2 fill2

                                        put $ update1 $ update2 m
fillConstraint _ = return ()

isLabelVar :: Label -> Bool
isLabelVar (LabelVar _) = True
isLabelVar _ = False

validateFill :: Metadata -> Label -> Label -> Label -> Label -> SolvingContext ()
validateFill i l1 l2 H L = throwE $ "CTC secret value violation ("++ show l1 ++ " and "++ show l2 ++") in " ++ showMetadata i
validateFill _ _ _ _ _ = return ()

toposortConstraints :: [Constraint] -> [SCC [Constraint]]
toposortConstraints = reverse . stronglyConnComp . convertConstraints

convertConstraints :: [Constraint] -> [ConstraintGraph]
convertConstraints cons = Map.elems $ evalState (toCGMap cons) Map.empty
                          where
                            toCGMap [] = get
                            toCGMap (c:cs) = convert c >> toCGMap cs

convert :: Constraint -> State (Map Label ConstraintGraph) ConstraintGraph
convert c@(LowConf _ l)       = do -- l < L
                                  let lbl = LabelVar l
                                  addEdge lbl c L

convert c@(HighConf _ l)      = do -- H < l
                                  let lbl = LabelVar l
                                  addEdge H c lbl

convert c@(LowerThan _ l1 l2) = do -- l1 < l2
                                  let lbl1 = LabelVar l1
                                  let lbl2 = LabelVar l2
                                  addEdge lbl1 c lbl2

addEdge :: Label -> Constraint -> Label -> State (Map Label ConstraintGraph) ConstraintGraph
addEdge key c l = do
                    m <- get
                    let cg' = add $ fromMaybe ([], key, []) $ Map.lookup key m
                    put $ Map.insert key cg' m
                    ensureExist l
                    return cg'
                  where add (cs, k, ls) = (c:cs, k, l:ls)

ensureExist :: Label -> State (Map Label ConstraintGraph) ()
ensureExist key = do
                    m <- get
                    case Map.lookup key m of
                      Nothing -> put $ Map.insert key ([], key, []) m
                      Just _ -> return ()
