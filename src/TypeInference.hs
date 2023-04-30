module TypeInference (
  infer
) where

import AST
import Type

import Data.Map as Map (Map, empty, lookup, union, insert, singleton)
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Trans.Except

type TypeEnvironment = Map Id TypeScheme

-- TypeEnvironment helper functions

addTo :: TypeEnvironment -> [(Id, TypeScheme)] -> TypeEnvironment
addTo = foldr update
        where update (id, ty) = insert id ty

getType :: TypeEnvironment -> Id -> Either String TypeScheme
getType env id = case Map.lookup id env of
                   Nothing -> Left $ "Identifier not found: " ++ id
                   Just t  -> Right t

type Substitution = Map TypeVar LabelledType

-- substitute labelled type
substitute :: Substitution -> LabelledType -> LabelledType
substitute substMap (LabelledType t l) = substituteType substMap t l -- TODO: handle label?

substituteType :: Substitution -> Type -> Label -> LabelledType
substituteType substMap (TVar v)       label = case Map.lookup v substMap of
                                                  Just t -> t
                                                  Nothing -> LabelledType (TVar v) label -- TODO: should this be an error?
substituteType substMap (TFun lt1 lt2) label = LabelledType (TFun (substitute substMap lt1) (substitute substMap lt2)) label
substituteType substMap t              label = LabelledType t label -- TODO: TArray, TPair, TList

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
fresh = varType <$> freshVar

-- generalize function of W Algorithm
generalize :: TypeEnvironment -> LabelledType -> InferenceState TypeScheme
generalize env t = do
                      a <- freshVar                    -- TODO: is this enough? need to check a is not in ftv(env) ?
                      return (Forall a (Type t))

-- instantiate function of W Algorithm
instantiate :: TypeScheme -> InferenceState LabelledType
instantiate (Forall _ ts) = instantiate ts
instantiate (Type l)      = return l

-- unify (U) function of W Algorithm
unify :: LabelledType -> LabelledType -> InferenceState Substitution
unify (LabelledType t1 L) (LabelledType t2 L) = unifyType t1 t2 L -- TODO: handle other label and their unification

-- TODO: fill. implement for Nat, Bool, Fun and Var for now
unifyType :: Type -> Type -> Label -> InferenceState Substitution
unifyType TNat       TNat         _ = return empty
unifyType TBool      TBool        _ = return empty
unifyType (TFun x y) (TFun x' y') _ = do
                                      s1 <- unify x x'
                                      let sub = substitute s1
                                      s2 <- unify (sub y) (sub y')
                                      return (s2 .+ s1)

unifyType (TVar a)   t            l = if a `inType` t then throwE $ "Infinite type " ++ show t
                                      else return $ Map.singleton a (LabelledType t l)

unifyType t          (TVar a)     l = if a `inType` t then throwE $ "Infinite type " ++ show t
                                      else return $ Map.singleton a (LabelledType t l)

unifyType t1         t2           _ = throwE $ "Mismatched types " ++ show t1 ++ " and " ++ show t2

-- W function of W Algorithm
wAlg :: TypeEnvironment -> Expr -> InferenceState (LabelledType, Substitution)
wAlg _   (Nat _)  = return (lowConf TNat, empty)
wAlg _   (Bool _) = return (lowConf TBool, empty)
wAlg env (Var id) = do
                      ts <- except $ getType env id
                      ty <- instantiate ts
                      return (ty, empty)

wAlg env (Fn x expr) = do
                          a <- fresh
                          (ty, s) <- wAlg (insert x (Type a) env) expr
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

wAlg env _        = undefined -- TODO: fill

-- W Algorithm helper functions

lowConf :: Type -> LabelledType
lowConf t = LabelledType t L

varType :: TypeVar -> LabelledType
varType v = lowConf (TVar v)

fnType :: LabelledType -> LabelledType -> LabelledType
fnType x y = lowConf (TFun x y)

inType :: TypeVar -> Type -> Bool
inType (TypeVar i1) (TVar (TypeVar i2)) = i1 == i2
inType _ TNat = False
inType _ TBool = False
inType v (TFun t1 t2) = inTypeL v t1 || inTypeL v t2
inType v (TArray t) = inTypeL v t
inType v (TPair t1 t2) = inTypeL v t1 || inTypeL v t2
inType v (TList t) = inTypeL v t

inTypeL :: TypeVar -> LabelledType -> Bool
inTypeL v (LabelledType t _) = inType v t

-- |infer runs type inference analysis for an expression
infer :: Expr -> Either String TypeScheme
infer e = fmap (Type . fst) result
          where result = evalInference (wAlg empty e) newContext
