module TypeInference (
  infer
) where

import AST
import Type

import Data.Map as Map (Map, empty, lookup, fromList, toList, union)
import Control.Monad.State
import Control.Monad.Except

type TypeEnvironment = Map Id TypeScheme

type Substitution = Map TypeVar LabelledType

-- substitute labelled type
substitute :: Substitution -> LabelledType -> LabelledType
substitute substMap (LabelledType t l) = substituteType substMap t l -- TODO: handle label?

substituteType :: Substitution -> Type -> Label -> LabelledType
substituteType substMap (TVar v)       label = case Map.lookup v substMap of
                                                  Just t -> t
                                                  Nothing -> LabelledType (TVar v) label -- TODO: should this be error?
substituteType substMap (TFun lt1 lt2) label = LabelledType (TFun (substitute substMap lt1) (substitute substMap lt2)) label
substituteType substMap t              label = LabelledType t label -- TODO: TArray, TPair, TList

-- substitute type stored in the env
substituteEnv :: Substitution -> TypeEnvironment -> TypeEnvironment
substituteEnv substMap typeEnv = fromList (substituteTypeList substMap (toList typeEnv))

-- substitute type stored in a list
substituteTypeList :: Substitution -> [(Id, TypeScheme)] -> [(Id, TypeScheme)]
substituteTypeList substMap = map update
                              where update (id, ts) = (id, substituteTS substMap ts)

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

fresh :: InferenceState TypeVar
fresh = do
          ctx <- get
          let current = currentTypeVar ctx
          put ctx { currentTypeVar = current + 1}
          return (TypeVar current)

-- generalize function of W Algorithm
generalize :: TypeEnvironment -> LabelledType -> InferenceState TypeScheme
generalize = undefined -- TODO: fill. implement for Nat, Bool, Fun and Var for now

-- instantiate function of W Algorithm
instantiate :: TypeScheme -> InferenceState LabelledType
instantiate = undefined -- TODO: fill

-- unify (U) function of W Algorithm
unify :: LabelledType -> LabelledType -> InferenceState Substitution
unify = undefined -- TODO: fill. implement for Nat, Bool, Fun and Var for now

-- W function of W Algorithm
wAlg :: TypeEnvironment -> Expr -> InferenceState (LabelledType, Substitution)
wAlg = undefined -- TODO: fill

infer :: Expr -> Either String TypeScheme
infer e = fmap (Type . fst) result
          where result = evalInference (wAlg empty e) newContext
