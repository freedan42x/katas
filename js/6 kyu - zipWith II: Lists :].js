zipWith = (f, xs, ys) =>
  xs && ys ? new Node(f(xs.value, ys.value), zipWith(f, xs.next, ys.next)) : null
