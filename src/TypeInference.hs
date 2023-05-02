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
import Control.Applicative ((<|>))

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

newtype InferenceContext = InferenceContext { currentTypeVar :: Int }

type InferenceState = ExceptT String (State InferenceContext)

runInference :: InferenceState a -> InferenceContext -> (Either String a, InferenceContext)
runInference is = runState (runExceptT is)

evalInference :: InferenceState a -> InferenceContext -> Either String a
evalInference is ctx = fst (runInference is ctx)

newContext :: InferenceContext
newContext = InferenceContext {currentTypeVar = 0}

freshVar :: InferenceState TypeVar
freshVar = do
          ctx <- get
          let current = currentTypeVar ctx
          put ctx { currentTypeVar = current + 1}
          return (TypeVar current)

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

-- unify (U) function of W Algorithm
unify :: LabelledType -> LabelledType -> InferenceState Substitution
unify (LabelledType t1 L) (LabelledType t2 L) = unifyType t1 t2 L -- TODO: handle other label and their unification

-- TODO: fill. implement for Nat, Bool, Fun and Var for now
unifyType :: Type -> Type -> Label -> InferenceState Substitution
unifyType TNat       TNat         _ = return Map.empty
unifyType TBool      TBool        _ = return Map.empty
unifyType (TFun x y) (TFun x' y') _ = do
                                      s1 <- unify x x'
                                      let sub = substitute s1
                                      s2 <- unify (sub y) (sub y')
                                      return (s2 .+ s1)

-- it should be okay to not check whether a is in ftv(t) since there should be no free variable in t
unifyType (TVar a)   t            l = return $ Map.singleton a (LabelledType t l)
unifyType t          (TVar a)     l = return $ Map.singleton a (LabelledType t l)

unifyType t1         t2           _ = throwE $ "Mismatched types " ++ show t1 ++ " and " ++ show t2

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

wAlg env (IfThenElse cd e1 e2) = undefine

wAlg env (Operator op e1 e2) = undefine

wAlg env (TypeAnnotation e lt) = undifine

wAlg env (Sequence e1 e2) = undifine

-- Arrays
wAlg env (Array e1 e2) = undefine

wAlg env (ArrayRead e1 e2) = undefine

wAlg env (ArrayWrite e1 e2 e3) = undefine

-- Pairs
wAlg env (Pair e1 e2)   = do
                            (t1, s1) <- wAlg env e1
                            (t2, s2) <- wAlg (substituteEnv s1 env) e2
                            let tp = pairType (substitute s2 t1) t2
                            return (tp, s2 .+ s1)
                            
wAlg env (CasePair e1 x1 e2 x2)   = undefine

-- Lists
wAlg env Nil   = undefine

wAlg env (Cons x xs)   = undefine

wAlg env (CaseList e1 e2 x1 x2 e3)   = undefine

wAlg env _        = undefined -- TODO: fill

-- W Algorithm helper functions

lowConf :: Type -> Label -> LabelledType
lowConf t lbl = LabelledType t lbl

varType :: TypeVar -> Label -> LabelledType
varType v lbl = lowConf (TVar v) lbl -- TODO: use annotationvar instead of L?

fnType :: LabelledType -> LabelledType -> LabelledType
fnType (LabelledType x xlbl) (LabelledType y ylbl) = lowConf (TFun x' y') lbl
                                                     where x' = LabelledType x xlbl
                                                           y' = LabelledType y ylbl
                                                           -- TODO: need more accurate way to decide the new confidential level
                                                           lbl = if xlbl == H then H else ylbl

pairType :: LabelledType -> LabelledType -> LabelledType
pairType (LabelledType x xlbl) (LabelledType y ylbl) = lowConf (TPair x' y') lbl
                                                     where x' = LabelledType x xlbl
                                                           y' = LabelledType y ylbl
                                                           -- TODO: need more accurate way to decide the new confidential level
                                                           lbl = if xlbl == H then H else ylbl

-- |infer runs type inference analysis for an expression
infer :: Expr -> Either String TypeScheme
infer e = fmap (Type . fst) result
          where result = evalInference (wAlg Map.empty e) newContext
