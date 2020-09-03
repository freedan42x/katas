module Untyped where


data Nat = O | S Nat

-- Uncomment the following line to add your defintion for D
-- In particular, N here is a little primitive type added to
-- our untyped lambda calculus that can be used to witness
-- what goes on behind the scene.
data D = N Nat | F (D -> D)

-- app takes an untyped function and an untyped term and calculate
-- the resulting terms after application
app :: D -> D -> D
app (F f) x = f x

(!) = app

-- lam takes a function in higher-order abstract syntax (HOAS) and returns
-- an untyped terms representing the function
lam :: (D -> D) -> D
lam = F

-- Now let's define church's number
zero :: D
zero = lam $ \f -> lam $ \x -> x

suc :: D
suc = lam $ \n -> lam $ \f -> lam $ \x -> f ! (n ! f ! x)

-- Some other operations we can define
one :: D
one = app suc zero

plus :: D
plus = lam $ \m -> lam $ \n -> m ! suc ! n

pred :: D
pred = lam $ \n -> lam $ \f -> lam $ \x ->
  n ! (lam $ \g -> lam $ \h -> h ! (g ! f)) ! (lam $ \_ -> x) ! (lam $ \u -> u)

mult :: D
mult = lam $ \m -> lam $ \n -> lam $ \f -> m ! (n ! f)

-- We can even write out the defintion of y-combinator!
ycomb :: D
ycomb = lam $ \f -> (lam $ \x -> f ! (x ! x)) ! (lam $ \x -> f ! (x ! x))

-- And true and false
true :: D
true = lam $ \t -> lam $ \f -> t

false :: D
false = lam $ \t -> lam $ \f -> f

-- What about if-then-else?
ite :: D
ite = lam $ \x -> x

-- with ite, we can define our lovely
-- logical and/or operators
and :: D
and = lam $ \a -> lam $ \b -> ite ! a ! b ! false

or :: D
or = lam $ \a -> lam $ \b -> ite ! a ! true ! b

-- Here is the predicate to test if n is zero
iszero :: D
iszero = lam $ \n -> n ! (lam $ \x -> false) ! true

-- This converts the Church encoding to the Peano encoding of natural numbers
toPeano :: D -> D
toPeano (N _) = error "not a Church number!"
toPeano n     = n `app` (lam suc_nat) `app` (N O)
 where
  suc_nat (N n) = N (S n)
  suc_nat _     = error "stuck!"

-- This converts the Peano encoding to the Church encoding of natural numbers
fromPeano :: D -> D
fromPeano (N O    ) = zero
fromPeano (N (S n)) = app suc (fromPeano (N n))
fromPeano _         = error "not a Peano number!"

showPeano :: D -> Int
showPeano (N O    ) = 0
showPeano (N (S n)) = 1 + showPeano (N n)
showPeano _         = error "AYAYA"
