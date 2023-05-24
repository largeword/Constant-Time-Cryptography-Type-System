module InferenceTest (
  testInference
) where

import Constraint (Constraints)
import Type

import Test.Tasty
import Test.Tasty.HUnit

import TypeInference (infer)
import Parser (parse)
import TestUtils (reindexVar, assertRight, assertLeft)

-- Type Inference Test

testInference :: TestTree
testInference = testGroup "Test Type Inference" [
    testValue,
    testLetFunc,
    testIfElse,
    testOp,
    testPairCase,
    testArraySeq,
    testLists
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
  assertSrcType "let f1 = fn x -> let f2 = fn y -> (x, y) in f2 in f1 1" (tfun (tvar 0) (tpair TNat (tvar 0)))
  assertSrcType "fun f x -> if x < 1 then 0 else 1 + f (x - 1)" (tfun TNat TNat)
  assertSrcType "fn m -> fun f x -> m x (f (x-1))" (tfuns [tfuns [TNat, tvar 0, tvar 0], TNat, tvar 0])

  assertTypeMismatch "let add1 = fn x -> x + 1 in add1 true"
  assertTypeMismatch "1 1"

testIfElse :: TestTree
testIfElse = testCase "If-Else expressions" $ do
  assertSrcType "if true then 1 else 1" TNat
  assertSrcType "if true then fn x -> x else fn x -> x + 1" (tfun TNat TNat)
  assertSrcType "fn c -> fn x -> if c then (x < 0) else (x == 3)" (tfuns [TBool, TNat, TBool])
  assertSrcType "let check = fn c -> if c then 1 else 2 in check true" TNat

  assertTypeMismatch "if 1 then 1 else 1"
  assertTypeMismatch "if true then false else 1"
  assertTypeMismatch "let check = fn c -> if c then 1 else 2 in check 1"

testOp :: TestTree
testOp = testCase "Operator expressions" $ do
  assertSrcType "let xs = 1 + 2 in xs" TNat
  assertSrcType "let xs = true && false in xs" TBool
  assertSrcType "let xs = 1 + 2 in let xt = 3 * 4 in xs + xt" TNat
  assertSrcType "let xs = true == false in xs" TBool
  assertSrcType "let xs = true != false in xs" TBool
  assertSrcType "let xs = 1 == 2 in let xt = 3 == 4 in xs && xt" TBool
  assertSrcType "let xs = 1 == 2 in let xt = 3 == 4 in xs || xt" TBool
  assertSrcType "let xs = 1 < 2 in let xt = 3 < 4 in xs && xt" TBool
  assertSrcType "let xs = 1 / 2 in xs" TNat

  assertTypeMismatch "1 == true"
  assertTypeMismatch "1 != false"
  assertTypeMismatch "1 + false"
  assertTypeMismatch "true && 1"

-- test pair & case pair
testPairCase :: TestTree
testPairCase = testCase "Pair and Case Pair expression" $ do
  assertSrcType "(1, false)" (tpair TNat TBool)
  assertSrcType "let id = fn x -> x in id (id 1, id false)" (tpair TNat TBool)
  assertSrcType "let id = fn x -> x in (1, id (id id, 1))" (tpair TNat (tpair (tfun (tvar 0) (tvar 0)) TNat))
  assertSrcType "fn x -> fn y -> (x, y)" (tfuns [tvar 0, tvar 1, tpair (tvar 0) (tvar 1)])
  assertSrcType "let pair = fn x -> fn y -> (x, y) in pair 1 3" (tpair TNat TNat)
  assertSrcType "let a = (1, (false, 1)) in case a of (x, y) -> case y of (y1, y2) -> ((y2, x), y1)" (tpair (tpair TNat TNat) TBool)
  assertSrcType "let swap = fn x -> case x of (x, y) -> (y, x) in swap (1, (false, 1))" (tpair (tpair TBool TNat) TNat)
  assertSrcType "(1, true) == (0, false)" TBool

  assertTypeMismatch "case 1 of (x, y) -> (y, x)"
  assertTypeMismatch "let swap = fn p -> case p of (x, y) -> (y, x) in swap true"
  assertTypeMismatch "let id = fn x -> x in case id of (x, y) -> (y, x)"
  assertTypeMismatch "let add = fn p -> case p of (x, y) -> (x + 1, y + 1) in add (true, true)"
  assertTypeMismatch "case (1, true) of (x, y) -> x == y"

testArraySeq :: TestTree
testArraySeq = testCase "Array and Sequence expressions" $ do
  assertSrcType "1; 2; false" TBool
  assertSrcType "1; 2" TNat
  assertSrcType "fn x -> (1; 2; x)" (tfun (tvar 0) (tvar 0))
  assertSrcType "array 10 true" (tarray TBool)
  assertSrcType "let xs = array 10 0 in (xs[0] = 1; xs[1] = 2; xs[xs[0]])" TNat
  assertSrcType "let xs = array 10 (array 10 0) in (xs, xs[1][2])" (tpair (tarray (tarray TNat)) TNat)
  assertSrcType "let xs = array 10 0 in let xt = array 10 true in xt[xs[1]] = false" TBool
  assertSrcType "fn n -> fn x -> array n x" (tfun TNat (tfun (tvar 0) (tarray (tvar 0))))
  assertSrcType "let pos = fn xs -> fn i -> fn j -> xs[i][j] in pos (array 10 (array 5 0))" (tfun TNat (tfun TNat TNat))

  assertTypeMismatch "array true 10"
  assertTypeMismatch "let xs = array 10 0 in xs[0] = false"
  assertTypeMismatch "let xs = array 10 0 in xs[true]"
  assertTypeMismatch "let xs = array 10 0 in xs[5][3]"
  assertTypeMismatch "let xs = array 10 true in xs[0] + 1"

testLists :: TestTree
testLists = testCase "Lists expressions" $ do
  assertSrcType "let xs = 1 : 2 : [] in xs" (tlist TNat)
  assertSrcType "let xs = true : false : true : [] in xs" (tlist TBool)
  assertSrcType "let xs = 1 : 2 : 3 : [] in case xs of [] -> 0 , y : ys -> y" TNat

  assertTypeMismatch "1 : true : []"
  assertTypeMismatch "let xs = 1 : 2 : 3 : [] in case xs of [] -> true , y : ys -> y"
  assertTypeMismatch "let xs = 1 : 2 : 3 : [] in case xs of [] -> true , y : ys -> y && false"

-- Type Inference Helper Functions

-- constructor helpers

tvar :: Int -> Type
tvar = TVar . TypeVar

tfun :: Type -> Type -> Type
tfun = make2 TFun

tfuns :: [Type] -> Type
tfuns [x, y] = tfun x y
tfuns (x:xs) = tfun x (tfuns xs)
tfuns _ = error "Invalid tfuns construction"

tpair :: Type -> Type -> Type
tpair = make2 TPair

tarray :: Type -> Type
tarray = make1 TArray

tlist :: Type -> Type
tlist = make1 TList

make1 :: (LabelledType -> Type) -> Type -> Type
make1 f t = f (lowConf t)

make2 :: (LabelledType -> LabelledType -> Type) -> Type -> Type -> Type
make2 f t1 t2 = f (lowConf t1) (lowConf t2)

simpleType :: Type -> TypeScheme
simpleType = Type . lowConf

lowConf :: Type -> LabelledType
lowConf t = LabelledType t L

unlabel :: LabelledType -> Type
unlabel (LabelledType t _) = t

-- assertions

assertTypeMismatch :: String -> Assertion
assertTypeMismatch = assertTypeError "mismatched type"

assertTypeError :: String -> String -> Assertion
assertTypeError msg src = assertLeft msg src $ parseAndInfer src

assertSrcType :: String -> Type -> Assertion
assertSrcType src ty = assertType src (fst $ assertRight "Type check failed" src $ parseAndInfer src) (simpleType ty)

parseAndInfer :: String -> Either String (TypeScheme, Constraints)
parseAndInfer src = infer $ assertRight "Parsing failed" src $ parse "" src

assertType :: String -> TypeScheme -> TypeScheme -> Assertion
assertType src (Forall _ t1) (Forall _ t2) = assertType src t1 t2
assertType src (Type t1) (Type t2) =
  do
    let reindex = reindexVar . unlabel
    let actual = reindex t1
    let expected = reindex t2
    if compareType actual expected then assertBool "" True
    else assertFailure $
          "Assertion fail: expected " ++ show expected ++
          ", got " ++ show actual ++ "\n  in test input: " ++ src

assertType src _ _ = assertFailure $ "Mismatch TypeScheme\n  in test input: " ++ src


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
