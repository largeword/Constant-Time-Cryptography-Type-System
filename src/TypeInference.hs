{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TupleSections #-}

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

data Substitution = Substitution {typeMap :: Map TypeVar LabelledType, annoMap ::  Map AnnotationVar AnnotationVar}

emptySubs :: Substitution
emptySubs = newSubs Map.empty Map.empty

newSubs :: Map TypeVar LabelledType -> Map AnnotationVar AnnotationVar -> Substitution
newSubs typeMap annoMap = Substitution {typeMap, annoMap};

-- substitute labelled type
substitute :: Substitution -> LabelledType -> LabelledType
substitute s (LabelledType t l) = substituteType s t (substituteLabel s l)

substituteAnno :: Substitution -> AnnotationVar -> AnnotationVar
substituteAnno s a = fromMaybe a (Map.lookup a (annoMap s))

substituteLabel :: Substitution -> Label -> Label
substituteLabel s (LabelVar a) = LabelVar $ substituteAnno s a
substituteLabel _ l = l

substituteType :: Substitution -> Type -> Label -> LabelledType
substituteType s (TVar v) lbl = case Map.lookup v (typeMap s) of
                                  Just t -> t
                                  Nothing -> LabelledType (TVar v) lbl

substituteType s (TFun lt1 lt2)  lbl = LabelledType (TFun (substitute s lt1) (substitute s lt2)) lbl
substituteType s (TPair lt1 lt2) lbl = LabelledType (TPair (substitute s lt1) (substitute s lt2)) lbl
substituteType s (TArray lt) lbl = LabelledType (TArray (substitute s lt)) lbl
substituteType s (TList lt)  lbl = LabelledType (TList (substitute s lt)) lbl

substituteType _ t lbl = LabelledType t lbl -- Nat and Bool

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
-- substMapNew should be obtained after substMapOld
(.+) :: Substitution -> Substitution -> Substitution
(.+) subNew subOld = Substitution {
                        typeMap = typeMapUnion,
                        annoMap = annoMapUnion
                      }
                      where
                        newAnnoMap = annoMap subNew
                        oldAnnoMap = annoMap subOld
                        annoMapUnion = newAnnoMap `Map.union` fmap (substituteAnno subNew) oldAnnoMap
                        subUpdated = subNew {annoMap = annoMapUnion}
                        newTypeMap = typeMap subUpdated
                        oldTypeMap = typeMap subOld
                        typeMapUnion = newTypeMap `Map.union` fmap (substitute subUpdated) oldTypeMap

data InferenceContext = InferenceContext { currentTypeVar :: Int, currentAnnVar :: Int }

type InferenceState = ExceptT String (State InferenceContext)

runInference :: InferenceState a -> InferenceContext -> (Either String a, InferenceContext)
runInference is = runState (runExceptT is)

evalInference :: InferenceState a -> InferenceContext -> Either String a
evalInference is ctx = fst (runInference is ctx)

newContext :: InferenceContext
newContext = InferenceContext {currentTypeVar = 0, currentAnnVar = 0}  -- why start with 0? Is it possible to be overlapped?

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
unify :: LabelledType -> LabelledType -> InferenceState Substitution
unify (LabelledType t1 lbl1) (LabelledType t2 lbl2) = do
                                                        s1 <- unifyType t1 t2 lbl2
                                                        let s2 = createLabelSubs lbl1 lbl2
                                                        return (s2 .+ s1)

createLabelSubs :: Label -> Label -> Substitution
createLabelSubs (LabelVar a1) (LabelVar a2) = newSubs Map.empty (Map.singleton a1 a2)
createLabelSubs _ _ = emptySubs

unifyType :: Type -> Type -> Label -> InferenceState Substitution
unifyType TNat       TNat         _ = return emptySubs
unifyType TBool      TBool        _ = return emptySubs
unifyType (TFun x y) (TFun x' y') _ = do
                                      s1 <- unify x x'
                                      let sub = substitute s1
                                      s2 <- unify (sub y) (sub y')
                                      return (s2 .+ s1)

unifyType (TPair x y) (TPair x' y') _ = do
                                          s1 <- unify x x'
                                          let sub = substitute s1
                                          s2 <- unify (sub y) (sub y')
                                          return (s2 .+ s1)

unifyType (TList t1)  (TList t2)  _ = unify t1 t2
unifyType (TArray t1) (TArray t2) _ = unify t1 t2

-- it should be okay to not check whether a is in ftv(t) since there should be no free variable in t
unifyType (TVar a)   t            l = return $ newSubs (Map.singleton a (LabelledType t l)) Map.empty
unifyType t          (TVar a)     l = return $ newSubs (Map.singleton a (LabelledType t l)) Map.empty

unifyType t1         t2           _ = throwE $ "Mismatched types " ++ show t1 ++ " and " ++ show t2

operatorType :: Operator -> InferenceState (LabelledType, LabelledType, LabelledType, Constraints)
operatorType Add = createOpType TNat TNat TNat Nothing
operatorType Subtract = createOpType TNat TNat TNat Nothing
operatorType Multiply = createOpType TNat TNat TNat Nothing
operatorType LessThan = createOpType TNat TNat TBool Nothing
operatorType And = createOpType TBool TBool TBool Nothing
operatorType Or = createOpType TBool TBool TBool Nothing
operatorType Divide = createOpType TNat TNat TNat (Just LowConf)

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
addConstraintLbl c (LabelVar b1) (LabelVar b2) = return $ Set.insert (LowerThan b1 b2) c
addConstraintLbl c (LabelVar b)  L             = return $ Set.insert (LowConf b) c
addConstraintLbl c H             (LabelVar b)  = return $ Set.insert (HighConf b) c
addConstraintLbl _ H             L             = throwE "Trying to cast private value into public value"
addConstraintLbl c _             _             = return c

type VariantTypeFunc = LabelledType -> Constraints -> InferenceState (LabelledType, Constraints)

-- expandType t1 returns a t2 and constraint such that t1 <= t2 (covariant)
expandType :: LabelledType -> Constraints -> InferenceState (LabelledType, Constraints)
expandType (LabelledType t1 (LabelVar b1)) c = do
                                                b2 <- freshAnnotationVar
                                                (t2, c2) <- expandTypeT t1 c
                                                let c3 = Set.insert (LowerThan b1 b2) c2
                                                return (LabelledType t2 (LabelVar b2), c3)

expandType (LabelledType t l) c = do
                                    (t2, cts) <- expandTypeT t c
                                    return (LabelledType t2 l, cts)

-- narrowType t1 returns a t2 and constraint such that t2 <= t1 (contravariant)
narrowType :: LabelledType -> Constraints -> InferenceState (LabelledType, Constraints)
narrowType (LabelledType t1 (LabelVar b1)) c = do
                                                b2 <- freshAnnotationVar
                                                (t2, c2) <- narrowTypeT t1 c
                                                let c3 = Set.insert (LowerThan b2 b1) c2
                                                return (LabelledType t2 (LabelVar b2), c3)

narrowType (LabelledType t l) c = do
                                    (t2, cts) <- narrowTypeT t c
                                    return (LabelledType t2 l, cts)

expandTypeT :: Type -> Constraints-> InferenceState (Type, Constraints)
expandTypeT = variantTypeT expandType narrowType

narrowTypeT :: Type -> Constraints-> InferenceState (Type, Constraints)
narrowTypeT = variantTypeT narrowType expandType

variantTypeT :: VariantTypeFunc -> VariantTypeFunc -> Type -> Constraints -> InferenceState (Type, Constraints)
variantTypeT _ _ TNat c = return (TNat, c)
variantTypeT _ _ TBool c = return (TBool, c)

variantTypeT _ _ (TVar a) c = return (TVar a, c)


variantTypeT covar contra (TFun t1 t2) c = do
                                            (t1', c1) <- contra t1 c
                                            (t2', c2) <- covar t2 c1
                                            return (TFun t1 t2', c2)

variantTypeT covar contra (TPair t1 t2) c = do
                                              (t1', c1) <- covar t1 c
                                              (t2', c2) <- covar t2 c1
                                              return (TPair t1 t2', c2) -- TODO: check if covar & contra use is right

variantTypeT covar contra (TArray t) c = do
                                          (t', c') <- covar t c
                                          return (TArray t', c')     -- TODO: check if covar & contra use is right

variantTypeT covar contra (TList t) c = do
                                          (t', c') <- covar t c
                                          return (TList t', c')     -- TODO: check if covar & contra use is right

-- W function of W Algorithm
wAlg :: TypeEnvironment -> Expr -> InferenceState (LabelledType, Substitution, Constraints)
wAlg _   (Nat _)  = do
                      b <- freshAnnotationVar
                      return (labelledAnno TNat b, emptySubs, Set.singleton (LowConf b))

wAlg _   (Bool _) = do
                      b <- freshAnnotationVar
                      return (labelledAnno TBool b, emptySubs, Set.singleton (LowConf b))

wAlg env (Var id) = do
                      ts <- except $ getType env id
                      ty <- instantiate ts
                      return (ty, emptySubs, emptyConstraints)

wAlg env (Let x e1 e2)  = do
                            (t1, s1, c1) <- wAlg env e1
                            let env' = substituteEnv s1 env
                            tx <- generalize env' t1
                            (t2, s2, c2) <- wAlg (Map.insert x tx env') e2
                            return (t2, s2 .+ s1, Set.union c2 (substituteConstrs s2 c1))

wAlg env (Fn x expr) = do
                          a <- fresh
                          (ty, s, c1) <- wAlg (Map.insert x (Type a) env) expr
                          tf <- fnType (substitute s a) ty
                          return (tf, s, substituteConstrs s c1)

wAlg env (Fun f x expr) = do
                            a1 <- fresh
                            a2 <- fresh
                            tf <- fnType a1 a2
                            let env' = addTo env [(x, Type a1), (f, Type tf)]

                            (tret, s1, c1) <- wAlg env' expr
                            s2 <- unify tret (substitute s1 a2)

                            let s = s2 .+ s1
                            let sub = substitute s
                            tfun <- fnType (sub a1) (sub tret)

                            return (tfun, s, substituteConstrs s c1)

wAlg env (App e1 e2)    = do
                            (t1, s1, c1) <- wAlg env e1
                            (t2, s2, c2) <- wAlg (substituteEnv s1 env) e2
                            a <- fresh
                            tfun <- fnType t2 a
                            s3 <- unify (substitute s2 t1) tfun
                            let s4 = s3 .+ s2 .+ s1
                            return (substitute s3 a, s4, Set.union (substituteConstrs s3 c2) (substituteConstrs (s3 .+ s2) c1))

wAlg env (IfThenElse e1 e2 e3) = do
                                  (t1, s1, c1) <- wAlg env e1
                                  let s1Env = substituteEnv s1 env
                                  (t2, s2, c2) <- wAlg s1Env e2
                                  let s2Env = substituteEnv s2 s1Env
                                  (t3, s3, c3) <- wAlg s2Env e3
                                  let s3Env = substituteEnv s3 s2Env
                                  s4 <- unify (substitute s3 (substitute s2 t1)) (LabelledType TBool L)
                                  s5 <- unify (substitute s4 (substitute s3 t2)) (substitute s4 t3)
                                  let s6 = s5 .+ s4 .+ s3 .+ s2 .+ s1
                                  return (substitute s6 t3, s6, Set.union (substituteConstrs (s5 .+ s4) c3) (Set.union (substituteConstrs (s5 .+ s4 .+ s3) c2) (substituteConstrs (s5 .+ s4 .+ s3 .+ s2) c1)))

wAlg env (Operator op e1 e2) = do
                                 (t1, s1, c1) <- wAlg env e1
                                 let s1Env = substituteEnv s1 env
                                 (t2, s2, c2) <- wAlg s1Env e2
                                 (opT1, opT2, opT, c3) <- operatorType op

                                 let c3' = Set.union c3 $ Set.union c2 (substituteConstrs s2 c1)

                                 (t1', c4) <- expandType (substitute s2 t1) c3'
                                 (t2', c5) <- expandType t2 c4

                                 s3 <- unify t1' opT1
                                 s4 <- unify t2' (substitute s3 opT2)
                                 let s5 = s4 .+ s3 .+ s2 .+ s1

                                 return (substitute s5 opT, s5, substituteConstrs s5 c5)

wAlg env (TypeAnnotation e lt) = do
                                   (t, s1, c1) <- wAlg env e
                                   (t', c1') <- expandType t c1

                                   let lt1 = substitute s1 lt
                                   s2 <- unify t' lt1
                                   let getlbl = substituteLabel s2 . getLabel

                                   c2 <- castLabel (substituteConstrs s2 c1') (getlbl t') (getlbl lt1)

                                   return (substitute s2 t', s2 .+ s1, c2)
                                 where castLabel c l H = addConstraintLbl c H l
                                       castLabel c l1 l2 = addConstraintLbl c l1 l2

wAlg env (Sequence e1 e2) = do
                              (_, s1, c1) <- wAlg env e1
                              let env' = substituteEnv s1 env
                              (t, s2, c2) <- wAlg env' e2
                              return (t, s2 .+ s1, Set.union c2 (substituteConstrs s2 c1))

-- Arrays
wAlg env (Array el ev) = do
                           (tl, s1, c1) <- wAlg env el
                           s2 <- unify tl (LabelledType TNat L)
                           let s3 = s2 .+ s1
                           let env' = substituteEnv s3 env
                           (te, s4, c2) <- wAlg env' ev
                           tarray <- arrType te
                           return (tarray, s4 .+ s3, emptyConstraints) -- TODO: constraints?

wAlg env (ArrayRead arr idx) = do
                                  (tarr, s1, c1) <- wAlg env arr
                                  te <- fresh
                                  tarray <- arrType te
                                  s2 <- unify tarr tarray
                                  let s3 = s2 .+ s1
                                  let env' = substituteEnv s3 env
                                  (tidx, s4, c2) <- wAlg env' idx
                                  s5 <- unify tidx (LabelledType TNat L) -- TODO: L??
                                  let s = s5 .+ s4 .+ s3
                                  return (substitute s te, s, emptyConstraints) -- TODO: constraints?


wAlg env (ArrayWrite arr idx el) = do
                                      (tarr, s1, c1) <- wAlg env arr
                                      te <- fresh
                                      tarray <- arrType te
                                      s2 <- unify tarr tarray
                                      let s3 = s2 .+ s1
                                      let env1 = substituteEnv s3 env
                                      (tidx, s4, c2) <- wAlg env1 idx
                                      s5 <- unify tidx (LabelledType TNat L) -- TODO: L??
                                      let s6 = s5 .+ s4 .+ s3
                                      let env2 = substituteEnv s6 env1
                                      (telm, s7, c3) <- wAlg env2 el
                                      let s8 = s7 .+ s6
                                      s9 <- unify telm (substitute s8 te)
                                      return (substitute s9 telm, s9 .+ s8, emptyConstraints) -- TODO: constraints?

-- Pairs
wAlg env (Pair e1 e2)   = do
                            (t1, s1, c1) <- wAlg env e1
                            (t2, s2, c2) <- wAlg (substituteEnv s1 env) e2
                            tp <- pairType (substitute s2 t1) t2
                            return (tp, s2 .+ s1, emptyConstraints) -- TODO: constraints?

wAlg env (CasePair e1 x y e2) = do
                                  (tp, s1, c1) <- wAlg env e1
                                  vx <- fresh
                                  vy <- fresh
                                  tpair <- pairType vx vy
                                  s2 <- unify tp tpair
                                  let tx = substitute s2 vx
                                  let ty = substitute s2 vy
                                  let s3 = s2 .+ s1
                                  let env' = addTo (substituteEnv s3 env) [(x, Type tx), (y, Type ty)]
                                  (texp, s4, c2) <- wAlg env' e2
                                  return (texp, s4 .+ s3, emptyConstraints) -- TODO: constraints?

wAlg _ Nil   = do
                   t <- fresh
                   return (LabelledType (TList t) L, emptySubs, emptyConstraints) -- TODO: correct constraints? L or type annotate??

wAlg env (Cons x xs)   = do
                           (tx, s1, c1) <- wAlg env x
                           (txs, s2, c2) <- wAlg (substituteEnv s1 env) xs
                           s3 <- unify txs (LabelledType (TList (substitute s2 tx)) L)
                           return (substitute s3 txs, s3 .+ s2 .+ s1, emptyConstraints) -- TODO: constraints?

wAlg env (CaseList e1 e2 x1 x2 e3)   = do
                                         (t1, s1, c1) <- wAlg env e1
                                         let env1 = substituteEnv s1 env
                                         (t2, s2, c2) <- wAlg env1 e2
                                         vx1 <- fresh
                                         vx2 <- fresh
                                         s3 <- unify (substitute s2 t1) (LabelledType (TList vx1) L)
                                         s4 <- unify (substitute s3 vx2) (LabelledType (TList vx1) L)
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
arrType t = labelledAnno (TArray t) <$> freshAnnotationVar                 -- TODO: constraint between inner and outer label?

fnType :: LabelledType -> LabelledType -> InferenceState LabelledType
fnType x y = labelledAnno (TFun x y) <$> freshAnnotationVar                -- TODO: constraint between inner and outer label?

pairType :: LabelledType -> LabelledType -> InferenceState LabelledType
pairType x y = labelledAnno (TPair x y) <$> freshAnnotationVar             -- TODO: constraint between inner and outer label?

-- |infer runs type inference analysis for an expression
infer :: Expr -> Either String (TypeScheme, Constraints)
infer e = fmap update result
          where result = evalInference (wAlg Map.empty e) newContext
                update (t, _, c) = (Type t, c)
