const one = (a, f) =>
  (a.map(e => +f(e)).join``.match(/1/g) || '').length == 1;
