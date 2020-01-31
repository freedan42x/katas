module TrivialTauto where


p1 :: (a -> b, b -> c) -> a -> c
p1 (f, g) = g . f

p2 :: (a -> b -> c) -> (a, b) -> c
p2 f (a, b) = f a b

p3 :: ((Either a b, a -> c), b -> c) -> c
p3 ((Left  a, f), _) = f a
p3 ((Right b, _), g) = g b
