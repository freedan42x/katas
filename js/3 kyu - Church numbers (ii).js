toChurch  = intToChurch
toInt     = churchToInt
_pred     = n => --n
_sub      = (m, n) => m - n
_compare  = (m, n) => m > n ? 1 : m < n ? -1 : 0
_div      = (m, n) => ~~ (m / n)
_mod      = (m, n) => m % n

pred      = n => toChurch (_pred (toInt (n)))
sub       = (m, n) => toChurch (_sub (toInt (m), toInt (n)))
compareTo = (m, n) => _compare (toInt (m), toInt (n))
div       = (m, n) => toChurch (_div (toInt (m), toInt(n)))
mod       = (m, n) => toChurch (_mod (toInt (m), toInt(n)))
