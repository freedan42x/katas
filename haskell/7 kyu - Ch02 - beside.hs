module Ch02.Beside where

import Ch02.Beside.Nat (Nat(Succ, Z))


minus :: Nat -> Nat -> Nat
minus Z _ = Z
minus x Z = x
minus (Succ x) (Succ y) = minus x y

eq :: Nat -> Nat -> Bool
eq Z Z = True
eq (Succ x) (Succ y) = eq x y
eq _ _ = False

delta :: Nat -> Nat -> Nat
delta x y = case minus x y of
  Z -> minus y x
  r -> r

-- | Return `True`, if one argument can be obtained from another with `Succ`
beside :: Nat -> Nat -> Bool
beside = besideN $ Succ Z

-- | Return `True`, if `x` differs from `y` by `n`
besideN :: Nat -> Nat -> Nat -> Bool
besideN n x y = eq n $ delta x y
