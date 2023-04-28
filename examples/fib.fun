fun fib x ->
  if x < 2 then
    1 -- Base case
  else
    fib (x - 1) + fib (x - 2) -- Recursion
