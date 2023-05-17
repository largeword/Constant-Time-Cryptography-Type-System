module Analysis (
  analyse, analyseVerbose, TypeScheme(..)
) where

import AST
import Type
import TypeInference
import Constraint (solve, Constraints)
import Data.Map as Map (Map, lookup)
import Data.Maybe (fromMaybe)

analyse :: Expr -> Either String TypeScheme
analyse e = getlast <$> analyseVerbose e
            where getlast (_,_,_, res) = res

analyseVerbose :: Expr -> Either String (TypeScheme, Constraints, Map AnnotationVar Label, TypeScheme)
analyseVerbose e = do
                     (ts, constr) <- infer e
                     lblmap <- solve constr
                     let result = replaceLabels lblmap ts
                     return (ts, constr, lblmap, result)

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
