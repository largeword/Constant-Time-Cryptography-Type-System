let swap = fn x ->
  case x of
    (x, y) -> (y, x)
in
  swap (1, false)
