{-# LANGUAGE NamedFieldPuns #-}

module TypeInference (
  infer
) where

import AST
import Constraint
import Type

import Data.Map as Map (Map, empty, lookup, union, insert, singleton)
import Data.Set as Set (Set, empty, insert, member, toList, union, map, singleton)
import Data.Maybe (fromMaybe)

import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Trans.Except

type TypeEnvironment = Map Id TypeScheme

-- TypeEnvironment helper functions

addTo :: TypeEnvironment -> [(Id, TypeScheme)] -> TypeEnvironment
addTo = foldr update
        where update (id, ty) = Map.insert id ty

getType :: TypeEnvironment -> Id -> Either String TypeScheme
getType env id = case Map.lookup id env of
                   Nothing -> Left $ "Identifier not found: " ++ id
                   Just t  -> Right t

data Substitution = Substitution {typeMap :: Map TypeVar Type, annoMap ::  Map AnnotationVar AnnotationVar}
                    deriving (Show)

emptySubs :: Substitution
emptySubs = newSubs Map.empty Map.empty

newSubs :: Map TypeVar Type -> Map AnnotationVar AnnotationVar -> Substitution
newSubs typeMap annoMap = Substitution {typeMap, annoMap};

-- substitute labelled type
substitute :: Substitution -> LabelledType -> LabelledType
substitute s (LabelledType t l) = LabelledType (substituteType s t) (substituteLabel s l)

substituteAnno :: Substitution -> AnnotationVar -> AnnotationVar
substituteAnno s a = fromMaybe a (Map.lookup a (annoMap s))

substituteLabel :: Substitution -> Label -> Label
substituteLabel s (LabelVar a) = LabelVar $ substituteAnno s a
substituteLabel _ l = l

substituteType :: Substitution -> Type -> Type
substituteType s (TVar v) = fromMaybe (TVar v) (Map.lookup v (typeMap s))
substituteType s (TFun lt1 lt2)  = TFun (substitute s lt1) (substitute s lt2)
substituteType s (TPair lt1 lt2) = TPair (substitute s lt1) (substitute s lt2)
substituteType s (TArray lt) = TArray (substitute s lt)
substituteType s (TList lt)  = TList (substitute s lt)

substituteType _ t = t -- Nat and Bool

-- substitute type stored in the env
substituteEnv :: Substitution -> TypeEnvironment -> TypeEnvironment
substituteEnv substMap = fmap update
                         where update = substituteTS substMap

-- substitute type in TypeScheme
substituteTS :: Substitution -> TypeScheme -> TypeScheme
substituteTS substMap (Forall v ts) = Forall v (substituteTS substMap ts)
substituteTS substMap (Type lt) = Type (substitute substMap lt)

substituteConstr :: Substitution -> Constraint -> Constraint
substituteConstr s = fmap (substituteAnno s)

substituteConstrs :: Substitution -> Constraints -> Constraints
substituteConstrs sub = Set.map (substituteConstr sub)

infixr 9 .+
-- subNew should be obtained after subOld
(.+) :: Substitution -> Substitution -> Substitution
(.+) subNew subOld = Substitution {
                        typeMap = typeMapUnion,
                        annoMap = annoMapUnion
                      }
                      where
                        unionSub :: Ord k => (Substitution -> a -> a) -> (Substitution -> Map k a) -> Map k a
                        unionSub subsFunc field = field subNew `Map.union` fmap (subsFunc subNew) (field subOld)
                        annoMapUnion = unionSub substituteAnno annoMap
                        typeMapUnion = unionSub substituteType typeMap


data InferenceContext = InferenceContext { currentTypeVar :: Int, currentAnnVar :: Int, currentExpr :: Expr }

type InferenceState = ExceptT String (State InferenceContext)

runInference :: InferenceState a -> InferenceContext -> (Either String a, InferenceContext)
runInference is = runState (runExceptT is)

evalInference :: InferenceState a -> InferenceContext -> Either String a
evalInference is ctx = fst (runInference is ctx)

newContext :: InferenceContext
newContext = InferenceContext {currentTypeVar = 0, currentAnnVar = 0, currentExpr = Nat 0} -- Nat 0 is just dummy expression

ctcError :: String -> InferenceState a
ctcError msg = do
                   e <- getCurrentExpr
                   throwE $ msg ++ " in expression: " ++ showInline e

freshVar :: InferenceState TypeVar
freshVar = do
          ctx <- get
          let current = currentTypeVar ctx
          put ctx { currentTypeVar = current + 1}
          return (TypeVar current)

freshAnnotationVar :: InferenceState AnnotationVar
freshAnnotationVar = do
                       ctx <- get
                       let current = currentAnnVar ctx
                       put ctx {currentAnnVar = current + 1}
                       return (AnnotationVar current)

freshLabelVar :: InferenceState Label
freshLabelVar = LabelVar <$> freshAnnotationVar

fresh :: InferenceState LabelledType
fresh = do
          a <- freshVar
          labelledAnno (TVar a) <$> freshAnnotationVar

getCurrentExpr :: InferenceState Expr
getCurrentExpr = gets currentExpr

setCurrentExpr :: Expr -> InferenceState ()
setCurrentExpr e = do
                      ctx <- get
                      put ctx {currentExpr = e}

-- generalize function of W Algorithm
generalize :: TypeEnvironment -> LabelledType -> InferenceState TypeScheme
generalize env t = do
                      let existingVars = findVars (ftv env) Set.empty t
                      return $ foldr Forall (Type t) (Set.toList existingVars)

ftv :: TypeEnvironment -> Set TypeVar
ftv = foldr collect Set.empty
      where collect (Forall a ts) s = collect ts (Set.insert a s)
            collect (Type ts) s = findVars s s ts

findVars :: Set TypeVar -> Set TypeVar -> LabelledType -> Set TypeVar
findVars ftvs acc (LabelledType t _) = findVarsT ftvs acc t

findVarsT :: Set TypeVar -> Set TypeVar -> Type -> Set TypeVar
findVarsT _ acc TNat  = acc
findVarsT _ acc TBool = acc
findVarsT ftvs acc (TVar v)      = if v `member` ftvs then acc else Set.insert v acc
findVarsT ftvs acc (TFun t1 t2)  = let acc' = findVars ftvs acc t1 in findVars ftvs acc' t2
findVarsT ftvs acc (TArray t)    = findVars ftvs acc t
findVarsT ftvs acc (TPair t1 t2) = let acc' = findVars ftvs acc t1 in findVars ftvs acc' t2
findVarsT ftvs acc (TList t)     = findVars ftvs acc t

-- instantiate function of W Algorithm
instantiate :: TypeScheme -> InferenceState LabelledType
instantiate ts = instantiateReplace ts Map.empty

instantiateReplace :: TypeScheme -> Map TypeVar TypeVar -> InferenceState LabelledType
instantiateReplace (Forall va ts) rep = do
                                          vr <- freshVar
                                          instantiateReplace ts (Map.insert va vr rep)
instantiateReplace (Type l) rep       = return $ if null rep then l else replaceVar rep l

replaceVar :: Map TypeVar TypeVar -> LabelledType -> LabelledType
replaceVar rep (LabelledType t l) = LabelledType (replaceVarT rep t) l

replaceVarT :: Map TypeVar TypeVar -> Type -> Type
replaceVarT _ TNat  = TNat
replaceVarT _ TBool = TBool
replaceVarT rep (TFun t1 t2)  = TFun (replaceVar rep t1) (replaceVar rep t2)
replaceVarT rep (TArray t)    = TArray (replaceVar rep t)
replaceVarT rep (TPair t1 t2) = TPair (replaceVar rep t1) (replaceVar rep t2)
replaceVarT rep (TList t)     = TList (replaceVar rep t)
replaceVarT rep (TVar vold)   = let replacement = Map.lookup vold rep in
                                  case replacement of
                                    Just vnew -> TVar vnew
                                    Nothing   -> TVar vold

-- unify (U) function of W Algorithm
type UnificationFunc = LabelledType -> LabelledType -> InferenceState Substitution

unify :: LabelledType -> LabelledType -> InferenceState Substitution
unify (LabelledType t1 lbl1) (LabelledType t2 lbl2) = do
                                                        s1 <- unifyType unify t1 t2
                                                        let s2 = createLabelSubs lbl1 lbl2
                                                        return (s2 .+ s1)

unifyWithoutLbl :: LabelledType -> LabelledType -> InferenceState Substitution
unifyWithoutLbl (LabelledType t1 _) (LabelledType t2 _) = unifyType unifyWithoutLbl t1 t2

createLabelSubs :: Label -> Label -> Substitution
createLabelSubs (LabelVar a1) (LabelVar a2) = newSubs Map.empty (Map.singleton a1 a2)
createLabelSubs _ _ = emptySubs

unifyType :: UnificationFunc -> Type -> Type -> InferenceState Substitution
unifyType _ TNat       TNat         = return emptySubs
unifyType _ TBool      TBool        = return emptySubs
unifyType uni (TFun x y) (TFun x' y') = do
                                          s1 <- uni x x'
                                          let sub = substitute s1
                                          s2 <- uni (sub y) (sub y')
                                          return (s2 .+ s1)

unifyType uni (TPair x y) (TPair x' y') = do
                                            s1 <- uni x x'
                                            let sub = substitute s1
                                            s2 <- uni (sub y) (sub y')
                                            return (s2 .+ s1)

unifyType uni (TList t1)  (TList t2)  = uni t1 t2
unifyType uni (TArray t1) (TArray t2) = uni t1 t2

-- it should be okay to not check whether a is in ftv(t) since there should be no free variable in t
unifyType _ (TVar a)   t            = return $ newSubs (Map.singleton a t) Map.empty
unifyType _ t          (TVar a)     = return $ newSubs (Map.singleton a t) Map.empty

unifyType _ t1         t2           = ctcError $ "Mismatched types " ++ show t1 ++ " and " ++ show t2

operatorType :: Operator -> InferenceState (LabelledType, LabelledType, LabelledType, Constraints)
operatorType Add = createOpType TNat TNat TNat Nothing
operatorType Subtract = createOpType TNat TNat TNat Nothing
operatorType Multiply = createOpType TNat TNat TNat Nothing
operatorType LessThan = createOpType TNat TNat TBool Nothing
operatorType And = createOpType TBool TBool TBool Nothing
operatorType Or = createOpType TBool TBool TBool Nothing
operatorType Divide = do
                        e <- getCurrentExpr
                        createOpType TNat TNat TNat (Just (LowConf e))

operatorType Equals = do
                         t <- TVar <$> freshVar
                         createOpType t t TBool Nothing

operatorType NotEquals = do
                            t <- TVar <$> freshVar
                            createOpType t t TBool Nothing

createOpType :: Type -> Type -> Type -> Maybe (AnnotationVar -> Constraint) -> InferenceState (LabelledType, LabelledType, LabelledType, Constraints)
createOpType t1 t2 t3 cf = do
                            b <- freshAnnotationVar
                            let make t = LabelledType t (LabelVar b)
                            let cs = case cf of
                                      Nothing -> Set.empty
                                      Just f -> Set.singleton (f b)
                            return (make t1, make t2, make t3, cs)

addConstraintLbl :: Constraints -> Label -> Label -> InferenceState Constraints
addConstraintLbl c (LabelVar b1) (LabelVar b2) = do
                                                    e <- getCurrentExpr
                                                    return $ Set.insert (LowerThan e b1 b2) c
addConstraintLbl c (LabelVar b)  L             = do
                                                    e <- getCurrentExpr
                                                    return $ Set.insert (LowConf e b) c
addConstraintLbl c H             (LabelVar b)  = do
                                                    e <- getCurrentExpr
                                                    return $ Set.insert (HighConf e b) c
addConstraintLbl _ H             L             = ctcError "Trying to cast secret value into public value"
addConstraintLbl c _             _             = return c

type VariantTypeFunc = LabelledType -> Constraints -> InferenceState (LabelledType, Constraints)

-- expandType t1 returns a t2 and constraint such that t1 <= t2 (covariant)
expandType :: LabelledType -> Constraints -> InferenceState (LabelledType, Substitution, Constraints)
expandType t c = do
                   (t', c') <- expandTypeR t c
                   s <- unifyWithoutLbl t t'
                   return (substitute s t', s, substituteConstrs s c')

expandTypeR :: LabelledType -> Constraints -> InferenceState (LabelledType, Constraints)
expandTypeR (LabelledType t1 (LabelVar b1)) c = do
                                                b2 <- freshAnnotationVar
                                                (t2, c2) <- expandTypeT t1 c
                                                e <- getCurrentExpr
                                                let c3 = Set.insert (LowerThan e b1 b2) c2
                                                return (LabelledType t2 (LabelVar b2), c3)

expandTypeR (LabelledType t l) c = do
                                    (t2, cts) <- expandTypeT t c
                                    return (LabelledType t2 l, cts)

-- narrowType t1 returns a t2 and constraint such that t2 <= t1 (contravariant)
narrowType :: LabelledType -> Constraints -> InferenceState (LabelledType, Substitution, Constraints)
narrowType t c = do
                   (t', c') <- narrowTypeR t c
                   s <- unifyWithoutLbl t t'
                   return (substitute s t', s, substituteConstrs s c')

narrowTypeR :: LabelledType -> Constraints -> InferenceState (LabelledType, Constraints)
narrowTypeR (LabelledType t1 (LabelVar b1)) c = do
                                                b2 <- freshAnnotationVar
                                                (t2, c2) <- narrowTypeT t1 c
                                                e <- getCurrentExpr
                                                let c3 = Set.insert (LowerThan e b2 b1) c2
                                                return (LabelledType t2 (LabelVar b2), c3)

narrowTypeR (LabelledType t l) c = do
                                    (t2, cts) <- narrowTypeT t c
                                    return (LabelledType t2 l, cts)

expandTypeT :: Type -> Constraints-> InferenceState (Type, Constraints)
expandTypeT = variantTypeT expandTypeR narrowTypeR

narrowTypeT :: Type -> Constraints-> InferenceState (Type, Constraints)
narrowTypeT = variantTypeT narrowTypeR expandTypeR

variantTypeT :: VariantTypeFunc -> VariantTypeFunc -> Type -> Constraints -> InferenceState (Type, Constraints)
variantTypeT _ _ TNat c = return (TNat, c)
variantTypeT _ _ TBool c = return (TBool, c)

variantTypeT _ _ (TVar _) c = do
                                a <- freshVar
                                return (TVar a, c)

variantTypeT covar contra (TFun t1 t2) c = do
                                            (t1', c1) <- contra t1 c
                                            (t2', c2) <- covar t2 c1
                                            return (TFun t1' t2', c2)

variantTypeT covar contra (TPair t1 t2) c = do
                                              (t1', c1) <- covar t1 c
                                              (t2', c2) <- covar t2 c1
                                              return (TPair t1' t2', c2)

variantTypeT covar contra (TArray t) c = do
                                          (t', c') <- covar t c
                                          return (TArray t', c')     -- TODO: check if covar & contra use is right

variantTypeT covar contra (TList t) c = do
                                          (t', c') <- covar t c
                                          return (TList t', c')     -- TODO: check if covar & contra use is right


relabelType :: LabelledType -> InferenceState (LabelledType, Constraints)
relabelType (LabelledType t l) = do
                                   (t', c) <- relabelTypeT t
                                   (l', c') <- constraintByLabel c l
                                   return (LabelledType t' l', c')

constraintByLabel :: Constraints -> Label -> InferenceState (Label, Constraints)
constraintByLabel c L = do
                          b <- freshAnnotationVar
                          e <- getCurrentExpr
                          return (LabelVar b, Set.insert (LowConf e b) c)
constraintByLabel c H = do
                          b <- freshAnnotationVar
                          e <- getCurrentExpr
                          return (LabelVar b, Set.insert (HighConf e b) c)

constraintByLabel c (LabelVar (AnnotationVar i)) = return (LabelVar (AnnotationVar (-i-1)), c) -- TODO: neg here or in parser?

relabelTypeT :: Type -> InferenceState (Type, Constraints)
relabelTypeT (TFun x y) = do
                            (x', c1) <- relabelType x
                            (y', c2) <- relabelType y
                            return (TFun x' y', Set.union c1 c2)
relabelTypeT (TPair x y) = do
                            (x', c1) <- relabelType x
                            (y', c2) <- relabelType y
                            return (TPair x' y', Set.union c1 c2)
relabelTypeT (TList t) = do
                            (t', c) <- relabelType t
                            return (TList t', c)
relabelTypeT (TArray t) = do
                            (t', c) <- relabelType t
                            return (TArray t', c)

relabelTypeT (TVar (TypeVar i)) = return (TVar (TypeVar (-i - 1)), emptyConstraints) -- TODO: neg here or in parser?

relabelTypeT t = return (t, emptyConstraints)

-- W function of W Algorithm
wAlg :: TypeEnvironment -> Expr -> InferenceState (LabelledType, Substitution, Constraints)
wAlg t e = do
             prevExpr <- getCurrentExpr
             setCurrentExpr e
             result <- runW t e
             setCurrentExpr prevExpr
             return result

runW :: TypeEnvironment -> Expr -> InferenceState (LabelledType, Substitution, Constraints)
runW _   (Nat _)  = do
                      b <- freshAnnotationVar
                      return (labelledAnno TNat b, emptySubs, emptyConstraints)

runW _   (Bool _) = do
                      b <- freshAnnotationVar
                      return (labelledAnno TBool b, emptySubs, emptyConstraints)

runW env (Var id) = do
                      ts <- except $ getType env id
                      ty <- instantiate ts
                      expandType ty emptyConstraints

runW env (Let x e1 e2)  = do
                            (t1, s1, c1) <- wAlg env e1
                            let env' = substituteEnv s1 env
                            tx <- generalize env' t1
                            (t2, s2, c2) <- wAlg (Map.insert x tx env') e2
                            return (t2, s2 .+ s1, Set.union c2 (substituteConstrs s2 c1))

runW env (Fn x expr) = do
                          a <- fresh
                          (ty, s, c1) <- wAlg (Map.insert x (Type a) env) expr

                          tf <- fnType (substitute s a) ty

                          (tf', s1, c2) <- expandType tf (substituteConstrs s c1)
                          return (tf', s1 .+ s, c2)

runW env (Fun f x expr) = do
                            a1 <- fresh
                            a2 <- fresh
                            tf <- fnType a1 a2

                            (tf', s0, c0) <- expandType tf emptyConstraints

                            let env' = substituteEnv s0 $ addTo env [(x, Type a1), (f, Type tf')]

                            (tret, s1, c1) <- wAlg env' expr
                            let s1' = s1 .+ s0

                            s2 <- unify tret (substitute s1' a2)

                            let s = s2 .+ s1'

                            return (substitute s tf, s, substituteConstrs s (Set.union c1 c0))

runW env (App e1 e2)    = do
                            (t1, s1, c1) <- wAlg env e1
                            (t2, s2, c2) <- wAlg (substituteEnv s1 env) e2
                            a <- fresh
                            tfun <- fnType t2 a
                            s3 <- unify (substitute s2 t1) tfun
                            let s4 = s3 .+ s2 .+ s1
                            let c3 = substituteConstrs s4 $ Set.union c2 c1

                            -- tfun outer label must be L, otherwise CT violation
                            c3' <- addConstraintLbl c3 (getLabel $ substitute s4 tfun) L

                            return (substitute s4 a, s4, c3')

runW env (IfThenElse e1 e2 e3) = do
                                  (t1, s1, c1) <- wAlg env e1

                                  let s1Env = substituteEnv s1 env
                                  (t2, s2, c2) <- wAlg s1Env e2

                                  let s2Env = substituteEnv s2 s1Env
                                  (t3, s3, c3) <- wAlg s2Env e3

                                  let s3' = s3 .+ s2 .+ s1

                                  lb <- freshLabelVar

                                  s4 <- unify (substitute s3' t1) (LabelledType TBool lb)
                                  let s4' = s4 .+ s3'

                                  s5 <- unify (substitute s4' t2) (substitute s4' t3)
                                  let s6 = s5 .+ s4'

                                  let subcon = substituteConstrs s6

                                  let c4 = subcon c3 `Set.union` subcon c2 `Set.union` subcon c1
                                  c4' <- addConstraintLbl c4 (substituteLabel s6 lb) L

                                  return (substitute s6 t3, s6, c4')

runW env (Operator op e1 e2) = do
                                 (t1, s1, c1) <- wAlg env e1
                                 let s1Env = substituteEnv s1 env
                                 (t2, s2, c2) <- wAlg s1Env e2

                                 (opT1, opT2, opT, c3) <- operatorType op

                                 let c3' = Set.union c3 $ Set.union c2 (substituteConstrs s2 c1)

                                 s3 <- unify (substitute s2 t1) (substitute s2 opT1)
                                 let s3' = s3 .+ s2 .+ s1

                                 s4 <- unify (substitute s3' t2) (substitute s3' opT2)

                                 let s4' = s4 .+ s3'

                                 return (substitute s4' opT, s4', substituteConstrs s4' c3')

runW env (TypeAnnotation e lt) = do
                                   (t, s1, c) <- wAlg env e
                                   (lt1, cann) <- relabelType lt

                                   s2 <- unify t lt1
                                   let s3 = s2 .+ s1
                                   return (substitute s3 lt1, s3, substituteConstrs s3 $ Set.union cann c)

runW env (Sequence e1 e2) = do
                              (_, s1, c1) <- wAlg env e1
                              let env' = substituteEnv s1 env
                              (t, s2, c2) <- wAlg env' e2
                              return (t, s2 .+ s1, Set.union c2 (substituteConstrs s2 c1))

-- Arrays
runW env (Array el ev) = do
                           (tl, s1, c1) <- wAlg env el
                           s2 <- unify tl (LabelledType TNat L) -- TODO: L constraint, CT violation otherwise
                           let s3 = s2 .+ s1
                           let env' = substituteEnv s3 env
                           (te, s4, c2) <- wAlg env' ev
                           tarray <- arrType te
                           return (tarray, s4 .+ s3, emptyConstraints) -- TODO: constraints

runW env (ArrayRead arr idx) = do
                                  (tarr, s1, c1) <- wAlg env arr
                                  te <- fresh
                                  tarray <- arrType te
                                  s2 <- unify tarr tarray
                                  let s3 = s2 .+ s1
                                  let env' = substituteEnv s3 env
                                  (tidx, s4, c2) <- wAlg env' idx
                                  s5 <- unify tidx (LabelledType TNat L) -- TODO: L constraint, CT violation otherwise
                                  -- TODO: label of te is >= outer label of array

                                  let s = s5 .+ s4 .+ s3
                                  return (substitute s te, s, emptyConstraints) -- TODO: constraints


runW env (ArrayWrite arr idx el) = do
                                      (tarr, s1, c1) <- wAlg env arr
                                      te <- fresh
                                      tarray <- arrType te
                                      s2 <- unify tarr tarray
                                      let s3 = s2 .+ s1
                                      let env1 = substituteEnv s3 env
                                      (tidx, s4, c2) <- wAlg env1 idx
                                      s5 <- unify tidx (LabelledType TNat L) -- TODO: L constraint, CT violation otherwise
                                      let s6 = s5 .+ s4 .+ s3
                                      let env2 = substituteEnv s6 env1
                                      (telm, s7, c3) <- wAlg env2 el
                                      let s8 = s7 .+ s6
                                      s9 <- unify telm (substitute s8 te)
                                      -- TODO: label telm <= label te

                                      return (substitute s9 telm, s9 .+ s8, emptyConstraints) -- TODO: constraints

-- Pairs
runW env (Pair e1 e2)   = do
                            (t1, s1, c1) <- wAlg env e1
                            (t2, s2, c2) <- wAlg (substituteEnv s1 env) e2
                            tp <- pairType (substitute s2 t1) t2
                            let s3 = s2 .+ s1
                            return (tp, s3, substituteConstrs s3 (Set.union c2 c1))

runW env (CasePair e1 x y e2) = do
                                  (tp, s1, c1) <- wAlg env e1
                                  vx <- fresh
                                  vy <- fresh
                                  tpair <- pairType vx vy
                                  s2 <- unify tp tpair
                                  let tx = substitute s2 vx
                                  let ty = substitute s2 vy
                                  let s3 = s2 .+ s1

                                  -- label of tx & ty is >= outer label of pair
                                  -- example: case (x^L, y^L)^H -> x should be ^H

                                  (txe, se1, c2) <- expandType tx (substituteConstrs s3 c1)
                                  (tye, se2, c3) <- expandType ty c2

                                  let s3' = se2 .+ se1 .+ s3

                                  let tx' = substitute s3' txe
                                  let ty' = substitute s3' tye
                                  let tp' = substitute s3' tp

                                  c4 <- addConstraintLbl c3 (getLabel tp') (getLabel tx')
                                  c4' <- addConstraintLbl c4 (getLabel tp') (getLabel ty')

                                  -- recurse to e2

                                  let env' = addTo (substituteEnv s3' env) [(x, Type tx'), (y, Type ty')]
                                  (texp, s4, c5) <- wAlg env' e2

                                  let s5 = s4 .+ s3'

                                  return (texp, s5, Set.union c5 (substituteConstrs s5 c4'))

runW _ Nil   = do
                   t <- fresh
                   return (LabelledType (TList t) L, emptySubs, emptyConstraints) -- TODO: correct constraints? L or type annotate??

runW env (Cons x xs)   = do
                           (tx, s1, c1) <- wAlg env x
                           (txs, s2, c2) <- wAlg (substituteEnv s1 env) xs
                           s3 <- unify txs (LabelledType (TList (substitute s2 tx)) L)
                           return (substitute s3 txs, s3 .+ s2 .+ s1, emptyConstraints) -- TODO: constraints?

runW env (CaseList e1 e2 x1 x2 e3)   = do
                                         (t1, s1, c1) <- wAlg env e1
                                         let env1 = substituteEnv s1 env
                                         -- TODO: t1 outer label must be L, otherwise CT violation
                                         (t2, s2, c2) <- wAlg env1 e2
                                         vx1 <- fresh
                                         vx2 <- fresh
                                         s3 <- unify (substitute s2 t1) (LabelledType (TList vx1) L) --TODO: L
                                         s4 <- unify (substitute s3 vx2) (LabelledType (TList vx1) L) -- TODO: L
                                         let tx1 = substitute s4 (substitute s3 vx1)
                                         let tx2 = substitute s4 (substitute s3 vx2)
                                         let env2 = substituteEnv s2 env1
                                         let env3 = addTo env2 [(x1, Type tx1), (x2, Type tx2)]
                                         (t3, s5, c3) <- wAlg env3 e3
                                         s6 <- unify (substitute (s5 .+ s4.+ s3) t2) t3
                                         return (substitute s6 t3, s6 .+ s5 .+ s4 .+ s3 .+ s2 .+ s1, emptyConstraints) -- TODO: constraints?

-- W Algorithm helper functions
getLabel :: LabelledType -> Label
getLabel (LabelledType _ l) = l

labelledAnno :: Type -> AnnotationVar -> LabelledType
labelledAnno t b = LabelledType t (LabelVar b)

arrType :: LabelledType -> InferenceState LabelledType
arrType t = labelledAnno (TArray t) <$> freshAnnotationVar

fnType :: LabelledType -> LabelledType -> InferenceState LabelledType
fnType x y = labelledAnno (TFun x y) <$> freshAnnotationVar

pairType :: LabelledType -> LabelledType -> InferenceState LabelledType
pairType x y = labelledAnno (TPair x y) <$> freshAnnotationVar

-- |infer runs type inference analysis for an expression
infer :: Expr -> Either String (TypeScheme, Constraints)
infer e = fmap update result
          where result = evalInference (wAlg Map.empty e) newContext
                update (t, _, c) = (Type t, c)
