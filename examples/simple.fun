--let div3 = fn x -> x / 3 in div3
--fun f x -> if x < 1 then 0 :: Nat^H else 1 + f (x - 1)

--let fa = fn a -> (a ) :: Nat^H in fa
--let a = 1 in a :: Nat^H
--fn a -> if true then a else false :: Bool^H
--fn a -> if a then a :: Bool^H else false
--fn c -> fn a -> if c then a else false :: Bool^H
--fn c -> fn a -> if c then a :: Bool^H else false

--
--let a = 1 in a :: Nat^H


--let c = true :: Bool^H in
--  if c then 1 else 2

 let id = fn x -> x in (id (3 :: Nat^H); id)
