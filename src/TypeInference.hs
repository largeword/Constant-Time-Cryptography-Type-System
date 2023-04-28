module TypeInference (
  infer
) where

import AST
import Type

import Data.Map (Map, empty)
import Control.Monad.State
import Control.Monad.Except

type TypeEnvironment = Map Id TypeScheme

type Substitution = Map TypeVar Type

substitute :: Substitution -> Type -> Type
substitute = undefined -- TODO: fill. implement for Nat, Bool, Fun and Var for now

substituteEnv :: Substitution -> TypeEnvironment -> TypeEnvironment
substituteEnv = undefined -- TODO: fill

infixr 9 .+
(.+) :: Substitution -> Substitution -> Substitution
(.+) = undefined -- TODO: fill, substitution composition

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
