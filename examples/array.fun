{-let xs = array 10 0 in
  let xt = array 5 true in
    (
      xt[1] = false;
      xt[0] = xt[1];
      xs[0] = 1;
      xs[1] = xs[0];
      xt[xs[0]]
    )
-}

let xs = (array 10 0 :: a0^H) in
   (xs, xs[0])

--let xs = (array 10 0 :: (Array Nat^H)^L) in
--    (xs, xs[0])

--let xs = (array 10 0 :: a0^H) in
--    xs[0] = xs[1]

-- let xs = (array 10 0 :: (Array Nat^L)^L) in xs[0] = (1 :: Nat^H)
