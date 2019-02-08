toChurch = intToChurch;
_add = (m, n) => m + n;
_mul = (m, n) => m * n;
_pow = (m, n) => m ** n;

add = (m, n) => toChurch (_add (churchToInt (m), churchToInt (n)));
mul = (m, n) => toChurch (_mul (churchToInt (m), churchToInt (n)));
pow = (m, n) => toChurch (_pow (churchToInt (m), churchToInt (n)));
