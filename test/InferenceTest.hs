module InferenceTest (
  testInference
) where

import Type
import Data.Map as Map (Map, lookup, insert, empty)

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.State
import TypeInference (infer)
import Data.Either (fromRight)
import Parser (parse)

-- Type Inference Test

testInference :: TestTree
testInference = testGroup "Test Type Inference" [
    testValue,
    testLetFunc,
    testPairCase,
    testArraySeq
  ]

-- test basic value
testValue :: TestTree
testValue = testCase "Nat and Bool Value" $ do
  assertSrcType "3" TNat
  assertSrcType "true" TBool

-- test function and let
testLetFunc :: TestTree
testLetFunc = testCase "Function and Let binding" $ do
  assertSrcType "let id = fn x -> x in id" (tfun (tvar 0) (tvar 0))
  assertSrcType "let id = fn x -> x in id id id id 3" TNat
  assertSrcType "fun loop x -> loop 1" (tfun TNat (tvar 0))

-- test pair & case pair
testPairCase :: TestTree
testPairCase = testCase "Pair and Case Pair expression" $ do
  assertSrcType "(1, false)" (tpair TNat TBool)
  assertSrcType "let id = fn x -> x in id (id 1, id false)" (tpair TNat TBool)
  assertSrcType "let id = fn x -> x in (1, id (id id, 1))" (tpair TNat (tpair (tfun (tvar 0) (tvar 0)) TNat))
  assertSrcType "fn x -> fn y -> (x, y)" (tfun (tvar 0) (tfun (tvar 1) (tpair (tvar 0) (tvar 1))))
  assertSrcType "let pair = fn x -> fn y -> (x, y) in pair 1 3" (tpair TNat TNat)
  assertSrcType "let a = (1, (false, 1)) in case a of (x, y) -> case y of (y1, y2) -> ((y2, x), y1)" (tpair (tpair TNat TNat) TBool)
  assertSrcType "let swap = fn x -> case x of (x, y) -> (y, x) in swap (1, false)" (tpair TBool TNat)
  -- TODO: error cases

testArraySeq :: TestTree
testArraySeq = testCase "Array and Sequence expressions" $ do
  assertSrcType "1; 2; false" TBool
  assertSrcType "let xs = array 10 0 in (xs[0] = 1; xs[1] = 2; xs[xs[0]])" TNat
  assertSrcType "let xs = array 10 (array 10 0) in (xs, xs[1][2])" (tpair (tarray (tarray TNat)) TNat)
  assertSrcType "let xs = array 10 0 in let xt = array 10 true in xt[xs[1]] = false" TBool
  -- TODO: error cases

-- Type Inference Helper Functions

-- constructor helpers

tvar :: Int -> Type
tvar = TVar . TypeVar

tfun :: Type -> Type -> Type
tfun = make2 TFun

tpair :: Type -> Type -> Type
tpair = make2 TPair

tarray :: Type -> Type
tarray = make1 TArray

make1 :: (LabelledType -> Type) -> Type -> Type
make1 f t = f (lowConf t)

make2 :: (LabelledType -> LabelledType -> Type) -> Type -> Type -> Type
make2 f t1 t2 = f (lowConf t1) (lowConf t2)

simpleType :: Type -> TypeScheme
simpleType = Type . lowConf

lowConf :: Type -> LabelledType
lowConf t = LabelledType t L

appLabel :: (Applicative m) => (Type -> m Type) -> LabelledType -> m LabelledType
appLabel f (LabelledType t l) = LabelledType <$> f t <*> pure l

unlabel :: LabelledType -> Type
unlabel (LabelledType t _) = t

-- assertions

assertSrcType :: String -> Type -> Assertion
assertSrcType src ty = assertType (getR $ parseAndInfer src) (simpleType ty)

parseAndInfer :: String -> Either String TypeScheme
parseAndInfer = infer . getR . parse ""

getR :: Either a b -> b
getR = fromRight (error "unreachable")

assertType :: TypeScheme -> TypeScheme -> Assertion
assertType (Forall _ t1) (Forall _ t2) = assertType t1 t2
assertType (Type t1) (Type t2) =
  do
    let reindex = reindexVar . unlabel
    let actual = reindex t1
    let expected = reindex t2
    if compareType actual expected then assertBool "" True
    else assertFailure $
          "Assertion fail: expected " ++ show expected ++
          ", got " ++ show actual

assertType _ _ = assertFailure "Mismatch TypeScheme"

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

-- comparison

compareUnlabel :: LabelledType -> LabelledType -> Bool
compareUnlabel t1 t2 = compareType (unlabel t1) (unlabel t2)

compareType :: Type -> Type -> Bool
compareType TNat TNat = True
compareType TBool TBool = True
compareType (TFun a1 b1) (TFun a2 b2) = compareUnlabel a1 a2 &&
                                        compareUnlabel b1 b2
compareType (TPair a1 b1) (TPair a2 b2) = compareUnlabel a1 a2 &&
                                          compareUnlabel b1 b2

compareType (TList a1) (TList a2) = compareUnlabel a1 a2
compareType (TArray a1) (TArray a2) = compareUnlabel a1 a2

compareType (TVar v1) (TVar v2) = v1 == v2

compareType _ _ = False
