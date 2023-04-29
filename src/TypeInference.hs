module TypeInference (
  infer
) where

import AST
import Type

import Data.Map (Map, empty, lookup, fromList, toList, union)
import Control.Monad.State
import Control.Monad.Except

type TypeEnvironment = Map Id TypeScheme

type Substitution = Map TypeVar Type

-- TODO: fill. implement for Nat, Bool, Fun and Var for now
substitute :: Substitution -> Type -> Type
substitute substMap (TVar v) = case Data.Map.lookup v substMap of
                                 Just t -> t
                                 Nothing -> TVar v
substitute substMap (TFun lt1 lt2) = TFun (substituteLT substMap lt1) (substituteLT substMap lt2)
substitute substMap t = t

-- substitute labelled type
substituteLT :: Substitution -> LabelledType -> LabelledType
substituteLT substMap (LabelledType t l) = LabelledType (substitute substMap t) l

-- substitute type stored in the env
substituteEnv :: Substitution -> TypeEnvironment -> TypeEnvironment
substituteEnv substMap typeEnv = fromList (substitueTypeList substMap (toList typeEnv))

-- substitute type stored in a list
substitueTypeList :: Substitution -> [(Id, TypeScheme)] -> [(Id, TypeScheme)]
substitueTypeList substMap (t:ts) = case t of
  (id, ts') -> [(id, substitueTS substMap ts')] ++ (substitueTypeList substMap ts)

-- substitute type in TypeScheme
substitueTS :: Substitution -> TypeScheme -> TypeScheme
substitueTS substMap (Forall v ts) = Forall v (substitueTS substMap ts)
substitueTS substMap (Type lt) = Type (substituteLT substMap lt)

infixr 9 .+
-- TODO: fill, substitution composition
-- substMapNew should be obtained after substMapOld
(.+) :: Substitution -> Substitution -> Substitution
(.+) substMapNew substMapOld = union substMapNew (fromList (updateOldSubstList (toList substMapOld) substMapNew))

-- update the old Substitution in form of list with new Substitution
updateOldSubstList :: [(TypeVar, Type)] -> Substitution -> [(TypeVar, Type)]
updateOldSubstList (s:ss) substMapNew = case s of
  (v, TVar v') -> [(v, substitute substMapNew (TVar v'))] ++ updateOldSubstList ss substMapNew
  (v, TFun lt1 lt2) -> [(v, substitute substMapNew (TFun lt1 lt2))] ++ updateOldSubstList ss substMapNew

newtype InferenceContext = InferenceContext { currentTypeVar :: Int }

type InferenceState = ExceptT String (State InferenceContext)

runInference :: InferenceState a -> InferenceContext -> (Either String a, InferenceContext)
runInference is = runState (runExceptT is)

evalInference :: InferenceState a -> InferenceContext -> Either String a
evalInference is ctx = fst (runInference is ctx)

newContext :: InferenceContext
newContext = InferenceContext {currentTypeVar = 0}

fresh :: InferenceState TypeVar
fresh = do
          ctx <- get
          let current = currentTypeVar ctx
          put ctx { currentTypeVar = current + 1}
          return (TypeVar current)

-- generalize function of W Algorithm
generalize :: TypeEnvironment -> Type -> InferenceState TypeScheme
generalize = undefined -- TODO: fill. implement for Nat, Bool, Fun and Var for now

-- instantiate function of W Algorithm
instantiate :: TypeScheme -> InferenceState Type
instantiate = undefined -- TODO: fill

-- unify (U) function of W Algorithm
unify :: Type -> Type -> InferenceState Substitution
unify = undefined -- TODO: fill. implement for Nat, Bool, Fun and Var for now

-- W function of W Algorithm
wAlg :: TypeEnvironment -> Expr -> InferenceState (Type, Substitution)
wAlg = undefined -- TODO: fill

toTypeScheme :: Type -> TypeScheme
toTypeScheme t = Type $ LabelledType t L -- TODO: use proper label analysis instead of this?

infer :: Expr -> Either String TypeScheme
infer e = fmap (toTypeScheme . fst) result
          where result = evalInference (wAlg empty e) newContext
