{-let xs = (1 :: Nat^H) : 2 : []
in case xs of
  y : ys -> y,
  [] -> 1
-}

let sum = fun f l ->
  case l of
    x : xs -> x + f l,
    [] -> 0 :: Nat^H
  in sum ([])

{-fun f n ->
  if n < 1 then
    [] :: a0^H
  else
    (1 :: Nat^H) : f (n - 1)-}
