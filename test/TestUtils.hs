module TestUtils (
  reindexVar,
  assertLeft,
  assertRight
) where

import Type
import Data.Map as Map ( Map, empty, insert, lookup )
import Control.Monad.State
import Test.Tasty.HUnit
import Data.List (isInfixOf)
import Data.Char (toLower)

assertRight :: Show a => String -> String -> Either a b -> b
assertRight msg input (Left a)  = error (msg ++ ": " ++ show a ++ "\n  in test input: " ++ input)
assertRight _   _     (Right b) = b

assertLeft :: String -> String -> Either String b -> Assertion
assertLeft msg input (Left e) = if lowercase msg `isInfixOf` lowercase e
                                then assertBool "" True
                                else error (
                                  "Assertion failed: Error must contain " ++ msg ++ ", where the error is " ++ e
                                  ++ "\n  in test input: " ++ input)
                                where lowercase = map toLower
assertLeft msg input (Right _) = error (
                                  "Assertion failed: Test returns Right when error with message '" ++ msg ++ "'is expected"
                                  ++ "\n  in test input: " ++ input)

-- reindexer for renumbering TVar

data Reindexer = Reindexer {current :: Int, mapping :: Map Int Int}

reindexVar :: Type -> Type
reindexVar t = evalState (reindexVarSt t) Reindexer {current = 0, mapping = Map.empty}

reindexVarSt :: Type -> State Reindexer Type
reindexVarSt TNat = return TNat
reindexVarSt TBool = return TBool
reindexVarSt (TFun t1 t2) = TFun <$> appLabel reindexVarSt t1 <*> appLabel reindexVarSt t2
reindexVarSt (TPair t1 t2) = TPair <$> appLabel reindexVarSt t1 <*> appLabel reindexVarSt t2
reindexVarSt (TList t) = TList <$> appLabel reindexVarSt t
reindexVarSt (TArray t) = TArray <$> appLabel reindexVarSt t
reindexVarSt (TVar (TypeVar x)) =
  do
    st <- get
    case Map.lookup x (mapping st) of
      Just v -> return $ tvar v
      Nothing -> do
        let id = current st
        put Reindexer {
            current = current st + 1,
            mapping = Map.insert x id (mapping st)
          }
        return $ tvar id

tvar :: Int -> Type
tvar = TVar . TypeVar

appLabel :: (Applicative m) => (Type -> m Type) -> LabelledType -> m LabelledType
appLabel f (LabelledType t l) = LabelledType <$> f t <*> pure l
