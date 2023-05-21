module ConstantTimeTest (
  testCT
) where


import Analysis (analyse)

import Type

import Test.Tasty
import Test.Tasty.HUnit
import Parser (parse)
import TestUtils (reindexVar, assertRight, assertLeft)

testCT :: TestTree
testCT = testGroup "Constant Time Test" [
    testSimple,
    testPair,
    testList
  ]

testSimple :: TestTree
testSimple = testCase "Basic and If-Else" $ do
  assertCTCType "let id = fn x -> x in id" $ tfun (tvar 0 L) (tvar 0 L) L
  assertCTCType "3 :: Nat^H" $ tnat H
  assertCTCType "fn a -> if true then a else false :: Bool^H" $ tfun (tbool L) (tbool H) L
  assertCTCType "fn c -> fn a -> if c then a :: Bool^H else false" $ tfuns [tbool L, tbool L, tbool H] L
  assertCTCType "fun f x -> if x < 1 then 0 :: Nat^H else 1 + f (x - 1)" $ tfun (tnat L) (tnat H) L
  assertCTCType "let div3 = fn x -> x / 3 in div3" $ tfun (tnat L) (tnat L) L
  assertCTCType "let add = (fn x -> x + 1) :: (Nat^L -> Nat^L)^H in add" $ tfun (tnat L) (tnat L) H

  assertCTViolation "(3 :: Nat^H) / 1"
  assertCTViolation "if (true :: Bool^H) then 1 else 3"
  assertCTViolation "let div3 = fn x -> x / 3 in div3 (3 :: Nat^H)"
  assertCTViolation "let add = (fn x -> x + 1) :: (Nat^L -> Nat^L)^H in add 1"

testPair :: TestTree
testPair = testCase "Pair and Case Pair" $ do
  assertCTCType "(1, 2) :: (Nat^H, Nat^L)^H" $ tpair (tnat H) (tnat L) H
  assertCTCType "let f1 = fn x -> let f2 = fn y -> (x, y) in f2 in f1 (1 :: Nat^H)"
    $ tfun (tvar 0 L) (tpair (tnat H) (tvar 0 L) L) L
  assertCTCType "let getX = fn p -> let idH = (fn x -> x) :: (a0^H -> a0^H)^L in case idH p of (x, y) -> x in getX"
    $ tfun (tpair (tvar 0 L) (tvar 1 L) L) (tvar 0 H) L
  assertCTCType "let p = (1, 2) :: a0^H in case p of (x, y) -> x+1" $ tnat H

  -- error cases
  assertCTViolation "let p = (1, 2) :: a0^H in case p of (x, y) -> x/3"
  assertCTViolation "let gx = (fn p -> case p of (x, y) -> x / 3) in gx ((1, 2) :: (Nat^H, Nat^H)^L)"

testList :: TestTree
testList = testCase "List and Case List" $ do
  assertCTCType "[]" $ tlist (tvar 0 L) L
  assertCTCType "(1 : []) :: (List Nat^H)^H" $ tlist (tnat H) H
  assertCTCType "let xs = (1 :: Nat^H) : 2 : [] in case xs of y : ys -> y, [] -> 1" $ tnat H
  assertCTCType "fun f l -> case l of x : xs -> x + f l, [] -> 0 :: Nat^H" $ tfun (tlist (tnat L) L) (tnat H) L
  assertCTCType "fun f n -> if n < 1 then [] :: a0^H else (1 :: Nat^H) : f (n - 1)" $ tfun (tnat L) (tlist (tnat H) H) L
  assertCTCType "let sum = fun f l -> case l of x : xs -> x + f l, [] -> 0 :: Nat^H in sum ([])" $ tnat H

  -- error cases
  assertCTViolation "let l = (1 : []) :: (List Nat^H)^H in case l of x : xs -> 1, [] -> 2"
  assertCTViolation "let sum = fun f l -> case l of x : xs -> x + f l, [] -> 0 in sum ([] :: a0^H)"

assertCTCType :: String -> LabelledType -> Assertion
assertCTCType src ty = assertType src (assertRight "Type check failed" src $ parseAndAnalyse src) (Type ty)

assertCTViolation :: String -> Assertion
assertCTViolation = assertCTErr "CT"

assertCTErr :: String -> String -> Assertion
assertCTErr msg src = assertLeft msg src $ parseAndAnalyse src

parseAndAnalyse :: String -> Either String TypeScheme
parseAndAnalyse src = analyse $ assertRight "Parsing failed" src $ parse "" src

assertType :: String -> TypeScheme -> TypeScheme -> Assertion
assertType src (Forall _ t1) (Forall _ t2) = assertType src t1 t2
assertType src (Type t1) (Type t2) =
  do
    let actual = reindex t1
    let expected = reindex t2
    if actual == expected then assertBool "" True
    else assertFailure $
          "Assertion fail: expected " ++ show expected ++
          ", got " ++ show actual ++ "\n  in test input: " ++ src
  where
    reindex (LabelledType t l) = LabelledType (reindexVar t) l

assertType src _ _ = assertFailure $ "Mismatch TypeScheme\n  in test input: " ++ src

-- helpers

tnat :: Label -> LabelledType
tnat = LabelledType TNat

tbool :: Label -> LabelledType
tbool = LabelledType TBool

tvar :: Int -> Label -> LabelledType
tvar i = LabelledType (TVar $ TypeVar i)

tfun :: LabelledType -> LabelledType -> Label -> LabelledType
tfun a b = LabelledType (TFun a b)

tfuns :: [LabelledType] -> Label -> LabelledType
tfuns [x, y] l = tfun x y l
tfuns (x:xs) l = tfun x (tfuns xs l) l
tfuns _ _ = error "Invalid tfuns construction"

tpair :: LabelledType -> LabelledType -> Label -> LabelledType
tpair a b = LabelledType (TPair a b)

tlist :: LabelledType -> Label -> LabelledType
tlist t = LabelledType (TList t)
