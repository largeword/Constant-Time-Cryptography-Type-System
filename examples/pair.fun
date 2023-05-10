let f1 =
  fn x ->
    let f2 = fn y -> (x, y) in f2
in
  f1 1
