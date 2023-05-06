module TypeInference (
  infer
) where

import AST
import Type

import Data.Map as Map (Map, empty, lookup, union, insert, singleton)
import Data.Set as Set (Set, empty, insert, member, toList)
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Trans.Except
import GHC.Int (eqInt32)

type TypeEnvironment = Map Id TypeScheme

-- TypeEnvironment helper functions

addTo :: TypeEnvironment -> [(Id, TypeScheme)] -> TypeEnvironment
addTo = foldr update
        where update (id, ty) = Map.insert id ty

getType :: TypeEnvironment -> Id -> Either String TypeScheme
getType env id = case Map.lookup id env of
                   Nothing -> Left $ "Identifier not found: " ++ id
                   Just t  -> Right t

type Substitution = Map TypeVar LabelledType
--  Map AnnotationVar Label

-- substitute labelled type
substitute :: Substitution -> LabelledType -> LabelledType
substitute substMap (LabelledType t l) = substituteType substMap t l -- TODO: handle label?

substituteType :: Substitution -> Type -> Label -> LabelledType
substituteType s (TVar v) lbl = case Map.lookup v s of
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

infixr 9 .+
-- substMapNew should be obtained after substMapOld
(.+) :: Substitution -> Substitution -> Substitution
(.+) substMapNew substMapOld = substMapNew `union` fmap update substMapOld
                               where update = substitute substMapNew

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

fresh :: InferenceState LabelledType
fresh = (\v -> varType v L) <$> freshVar  -- TODO: need to decide the type label

-- generalize function of W Algorithm
generalize :: TypeEnvironment -> LabelledType -> InferenceState TypeScheme
generalize env t = do
                      let existingVars = findVars (ftv env) Set.empty t
                      return $ foldr Forall (Type t) (Set.toList existingVars)

ftv :: TypeEnvironment -> Set TypeVar
ftv = foldr collect Set.empty
      where collect (Forall a ts) s = collect ts (Set.insert a s)
            collect (Type _) s = s

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

-- Intuitively, the new type label should euqal to the highest one
getNewTypeLabel :: Label -> Label -> Label
getNewTypeLabel H _ = H
getNewTypeLabel _ H = H
getNewTypeLabel (LabelVar (AnnotationVar x)) L = LabelVar (AnnotationVar x)
getNewTypeLabel L (LabelVar (AnnotationVar y)) = LabelVar (AnnotationVar y)
getNewTypeLabel (LabelVar (AnnotationVar x)) (LabelVar (AnnotationVar y)) = LabelVar (AnnotationVar (if x > y then x else y))

getNewTypeLabel _ _ = L -- TODO: just for completing the pattern, remove this later

-- unify (U) function of W Algorithm
unify :: LabelledType -> LabelledType -> InferenceState Substitution
unify (LabelledType t1 lbl1) (LabelledType t2 lbl2) = unifyType t1 t2 lbl -- TODO: handle other label and their unification
                                                    where lbl = getNewTypeLabel lbl1 lbl2

unifyType :: Type -> Type -> Label -> InferenceState Substitution
unifyType TNat       TNat         _ = return Map.empty
unifyType TBool      TBool        _ = return Map.empty
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
unifyType (TVar a)   t            l = return $ Map.singleton a (LabelledType t l)
unifyType t          (TVar a)     l = return $ Map.singleton a (LabelledType t l)

unifyType t1         t2           _ = throwE $ "Mismatched types " ++ show t1 ++ " and " ++ show t2

operatorType :: Operator -> InferenceState (Type, Type, Type)
operatorType Add = return (TNat, TNat, TNat)
operatorType Subtract = return (TNat, TNat, TNat)
operatorType Multiply = return (TNat, TNat, TNat)
operatorType Divide = return (TNat, TNat, TNat)
operatorType LessThan = return (TNat, TNat, TBool)
operatorType And = return (TBool, TBool, TBool)
operatorType Or = return (TBool, TBool, TBool)
operatorType Equals = do
                         t <- freshVar
                         return (TVar t, TVar t, TBool)

operatorType NotEquals = do
                         t <- freshVar
                         return (TVar t, TVar t, TBool)

-- W function of W Algorithm
wAlg :: TypeEnvironment -> Expr -> InferenceState (LabelledType, Substitution)
wAlg _   (Nat _)  = return (lowConf TNat L, Map.empty)  -- TODO: need to decide the type label
wAlg _   (Bool _) = return (lowConf TBool L, Map.empty)  -- TODO: need to decide the type label
wAlg env (Var id) = do
                      ts <- except $ getType env id
                      ty <- instantiate ts
                      return (ty, Map.empty)

wAlg env (Let x e1 e2)  = do
                            (t1, s1) <- wAlg env e1
                            let env' = substituteEnv s1 env
                            tx <- generalize env' t1
                            (t2, s2) <- wAlg (Map.insert x tx env') e2
                            return (t2, s2 .+ s1)

wAlg env (Fn x expr) = do
                          a <- fresh
                          (ty, s) <- wAlg (Map.insert x (Type a) env) expr
                          let tf = fnType (substitute s a) ty
                          return (tf, s)

wAlg env (Fun f x expr) = do
                            a1 <- fresh
                            a2 <- fresh
                            let tf = fnType a1 a2
                            let env' = addTo env [(x, Type a1), (f, Type tf)]

                            (tret, s1) <- wAlg env' expr
                            s2 <- unify tret (substitute s1 a2)

                            let s = s2 .+ s1
                            let sub = substitute s
                            let tfun = fnType (sub a1) (sub tret)

                            return (tfun, s)

wAlg env (App e1 e2)    = do
                            (t1, s1) <- wAlg env e1
                            (t2, s2) <- wAlg (substituteEnv s1 env) e2
                            a <- fresh
                            let tfun = fnType t2 a
                            s3 <- unify (substitute s2 t1) tfun
                            return (substitute s3 a, s3 .+ s2 .+ s1)

wAlg env (IfThenElse e1 e2 e3) = do
                                  (t1, s1) <- wAlg env e1
                                  let s1Env = substituteEnv s1 env
                                  (t2, s2) <- wAlg s1Env e2
                                  let s2Env = substituteEnv s2 s1Env
                                  (t3, s3) <- wAlg s2Env e3
                                  let s3Env = substituteEnv s3 s2Env
                                  s4 <- unify (substitute s3 (substitute s2 t1)) (LabelledType TBool L)
                                  s5 <- unify (substitute s4 (substitute s3 t2)) (substitute s4 t3)
                                  return (substitute s5 (substitute s4 t3), s5 .+ s4 .+ s3 .+ s2 .+ s1)

wAlg env (Operator op e1 e2) = do
                                 (t1, s1) <- wAlg env e1
                                 let s1Env = substituteEnv s1 env
                                 (t2, s2) <- wAlg s1Env e2
                                 (opT1, opT2, opT) <- operatorType op
                                 s3 <- unify (substitute s2 t1) (LabelledType opT1 L)  -- TODO: handling type label
                                 s4 <- unify (substitute s3 t2) (LabelledType opT2 L)  -- TODO: handling type label
                                 return (LabelledType opT L, s4 .+ s3 .+ s2 .+ s1)  -- TODO: handling type label

wAlg env (TypeAnnotation e lt) = do
                                   (t, s1) <- wAlg env e
                                   s2 <- unify t (substitute s1 lt)
                                   return (substitute s2 t, s2 .+ s1) -- TODO: not fully working until label works

wAlg env (Sequence e1 e2) = do
                              (_, s1) <- wAlg env e1
                              let env' = substituteEnv s1 env
                              (t, s2) <- wAlg env' e2
                              return (t, s2 .+ s1)

-- Arrays 
wAlg env (Array el ev) = do
                           (tl, s1) <- wAlg env el
                           s2 <- unify tl (LabelledType TNat L)
                           let s3 = s2 .+ s1
                           let env' = substituteEnv s3 env
                           (te, s4) <- wAlg env' ev
                           return (arrType te, s4 .+ s3)

wAlg env (ArrayRead arr idx) = do
                                  (tarr, s1) <- wAlg env arr
                                  te <- fresh
                                  s2 <- unify tarr (arrType te)
                                  let s3 = s2 .+ s1
                                  let env' = substituteEnv s3 env
                                  (tidx, s4) <- wAlg env' idx
                                  s5 <- unify tidx (LabelledType TNat L) -- TODO: L??
                                  let s = s5 .+ s4 .+ s3
                                  return (substitute s te, s)


wAlg env (ArrayWrite arr idx el) = do
                                      (tarr, s1) <- wAlg env arr
                                      te <- fresh
                                      s2 <- unify tarr (arrType te)
                                      let s3 = s2 .+ s1
                                      let env1 = substituteEnv s3 env
                                      (tidx, s4) <- wAlg env1 idx
                                      s5 <- unify tidx (LabelledType TNat L) -- TODO: L??
                                      let s6 = s5 .+ s4 .+ s3
                                      let env2 = substituteEnv s6 env1
                                      (telm, s7) <- wAlg env2 el
                                      let s8 = s7 .+ s6
                                      s9 <- unify telm (substitute s8 te)
                                      return (substitute s9 telm, s9 .+ s8)

-- Pairs
wAlg env (Pair e1 e2)   = do
                            (t1, s1) <- wAlg env e1
                            (t2, s2) <- wAlg (substituteEnv s1 env) e2
                            let tp = pairType (substitute s2 t1) t2
                            return (tp, s2 .+ s1)

wAlg env (CasePair e1 x y e2) = do
                                  (tp, s1) <- wAlg env e1
                                  vx <- fresh
                                  vy <- fresh
                                  s2 <- unify tp (pairType vx vy)
                                  let tx = substitute s2 vx
                                  let ty = substitute s2 vy
                                  let s3 = s2 .+ s1
                                  let env' = addTo (substituteEnv s3 env) [(x, Type tx), (y, Type ty)]
                                  (texp, s4) <- wAlg env' e2
                                  return (texp, s4 .+ s3)

wAlg _ Nil   = do 
                   t <- fresh
                   return (LabelledType (TList t) L, Map.empty)

wAlg env (Cons x xs)   = do
                           (tx, s1) <- wAlg env x
                           (txs, s2) <- wAlg (substituteEnv s1 env) xs
                           s3 <- unify txs (LabelledType (TList (substitute s2 tx)) L)
                           return (substitute s3 txs, s3 .+ s2 .+ s1)

wAlg env (CaseList e1 e2 x1 x2 e3)   = do
                                         (t1, s1) <- wAlg env e1
                                         let env1 = substituteEnv s1 env
                                         (t2, s2) <- wAlg env1 e2
                                         vx1 <- fresh
                                         vx2 <- fresh
                                         s3 <- unify (substitute s2 t1) (LabelledType (TList vx1) L)
                                         s4 <- unify (substitute s3 vx2) (LabelledType (TList vx1) L)
                                         let tx1 = substitute s4 (substitute s3 vx1)
                                         let tx2 = substitute s4 (substitute s3 vx2)
                                         let env2 = substituteEnv s2 env1
                                         let env3 = addTo env2 [(x1, Type tx1), (x2, Type tx2)]
                                         (t3, s5) <- wAlg env3 e3
                                         s6 <- unify (substitute (s5 .+ s4.+ s3) t2) t3
                                         return (substitute s6 t3, s6 .+ s5 .+ s4 .+ s3 .+ s2 .+ s1)

-- W Algorithm helper functions

lowConf :: Type -> Label -> LabelledType
lowConf t lbl = LabelledType t lbl

varType :: TypeVar -> Label -> LabelledType
varType v lbl = lowConf (TVar v) lbl -- TODO: use annotationvar instead of L?

arrType :: LabelledType -> LabelledType
arrType t = LabelledType (TArray t) L -- TODO: use freshAnnotationVar

fnType :: LabelledType -> LabelledType -> LabelledType
fnType (LabelledType x xlbl) (LabelledType y ylbl) = lowConf (TFun x' y') lbl
                                                     where x' = LabelledType x xlbl
                                                           y' = LabelledType y ylbl
                                                           -- TODO: need more accurate way to decide the new confidential level
                                                           lbl = getNewTypeLabel xlbl ylbl

pairType :: LabelledType -> LabelledType -> LabelledType
pairType (LabelledType x xlbl) (LabelledType y ylbl) = lowConf (TPair x' y') lbl
                                                     where x' = LabelledType x xlbl
                                                           y' = LabelledType y ylbl
                                                           -- TODO: need more accurate way to decide the new confidential level
                                                           lbl = getNewTypeLabel xlbl ylbl

-- |infer runs type inference analysis for an expression
infer :: Expr -> Either String TypeScheme
infer e = fmap (Type . fst) result
          where result = evalInference (wAlg Map.empty e) newContext
