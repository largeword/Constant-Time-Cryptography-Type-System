--((1 :: Nat^H) + 1)
--let a = true in if a then 1 :: Nat^H else 2
--fn a -> if a then a :: Bool^H else false
--let fs = fn x -> x + 1 :: Nat^H in fs


(fn x -> fn y -> (x, y) :: a0^H) :: (Nat^b0 -> (Nat -> (Nat, Nat)^b0))
