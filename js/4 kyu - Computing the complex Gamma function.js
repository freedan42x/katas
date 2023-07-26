function sin([a, b]) {
  return [Math.sin(a) * Math.cosh(b), Math.cos(a) * Math.sinh(b)];
}

function sqrt([a, b]) {
  const r = Math.sqrt(Math.sqrt(a*a + b*b));
  const theta = Math.atan2(b, a) / 2;
  return [r * Math.cos(theta), r * Math.sin(theta)];
}

function log([a, b]) {
  return [Math.log(a*a + b*b)/2, Math.atan2(b, a)];
}

function pow(z1, z2) {
  return exp(mul(log(z1), z2));
}

function exp([a, b]) {
  const ea = Math.exp(a);
  return [ea * Math.cos(b), ea * Math.sin(b)];
}

function divR(r, [a, b]) {
  const d = a * a + b * b;
  return [r * a / d, -r * b / d];
}

function mul([a, b], [c, d]) {
  return [a * c - b * d, a * d + b * c];
}

function add([a, b], [c, d]) {
  return [a + c, b + d];
}

const g = 7;
const p = [
  0.99999999999980993,
  676.5203681218851,
  -1259.1392167224028,
  771.32342877765313,
  -176.61502916214059,
  12.507343278686905,
  -0.13857109526572012,
  9.9843695780195716e-6,
  1.5056327351493116e-7,
];

function gamma([a, b]) {
  if (b == 0 && (a == 0 || a < 0 && Number.isInteger(a))) return null;
  
  if (a < 0.5) {
    let w = sin([Math.PI * a, Math.PI * b]);
    w = mul(w, gamma([1 - a, -b]));
    return divR(Math.PI, w);
  }
  
  a -= 1;
  let x = [p[0], 0];
  for (let i = 1; i < p.length; i++) {
    x = add(x, divR(p[i], [a + i, b]));
  }

  let t = [a + g + 0.5, b];
  let r = [Math.sqrt(2 * Math.PI), 0];
  r = mul(r, pow(t, [a + 0.5, b]));
  r = mul(r, exp(mul([-1, 0], t)));
  return mul(r, x);
}
