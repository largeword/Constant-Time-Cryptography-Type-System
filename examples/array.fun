let xs = array 10 0 in
  let xt = array 5 true in
    (
      xt[1] = false;
      xt[0] = xt[1];
      xs[0] = 1;
      xs[1] = xs[0];
      xt[xs[0]]
    )
