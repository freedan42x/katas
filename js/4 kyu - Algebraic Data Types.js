zero = () => undefined
succ = nat => () => nat
isZero = nat => nat() == undefined

natToInt = nat => nat() ? 1 + natToInt(nat()) : 0
intToNat = int => int ? succ(intToNat(int - 1)) : zero
add = (m, n) => m() ? succ(add(m(), n)) : n
mul = (m, n) => m() ? add(n, mul(m(), n)) : zero
compareTo = (m, n) => 
  isZero(m) && isZero(n) ? 
  0  : isZero(m) ?
  -1 : isZero(n) ?
  1  : compareTo(m(), n())
toString = nat => nat() ? `succ(${toString(nat())})` : 'zero'
