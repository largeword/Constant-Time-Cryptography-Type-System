{- let f1 =
  fn x ->
    let f2 = fn y -> (x, y) in f2
in
  f1 (1 :: Nat^H)
-}
{-
let getX = fn p ->
  let idH = (fn x -> x) :: (a0^H -> a0^H)^L in
    case idH p of
      (x, y) -> x
in
  getX
-}

let p = (1, 2) :: a0^H in
  case p of
    (x, y) -> x
