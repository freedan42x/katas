const fix = f => f(t => fix(f)(t));

const factorial = r => n => n <= 1n ? 1n : n * r(n - 1n);

const fibonacci = r => n => n <= 1 ? BigInt(n) : r(n - 1) + r(n - 2);

const foldr = r => f => z => xs =>
  (h => h != undefined ? f(h)(() => r(f)(z)(xs)) : z)(xs.next().value);
