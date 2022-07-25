module ListsAsFolds (cons,nil,sum,product,iterate,repeat,cycle,replicate,null,length,snoc,append,concat,map,filter,take,drop,splitAt,get,set,any,all,find,findIndex,partition,span,minimumBy,maximumBy,sortBy,foldl,scanl,scanr,reverse,head,tail,init,last,zip,unzip,zipWith) where

import Prelude (const, id, error, flip)
import Preloaded


-- helpers

eq :: Number -> Number -> Boolean
eq m n = and zm zn ? true $ and (not zm) (not zn) ? eq (pred m) (pred n) $ false where
  zm = zero m
  zn = zero n

tails :: List a -> List (List a)
tails xs = foldr xs (\x acc -> cons (cons x $ option (head acc) nil id) acc) $ cons nil nil

opt2l :: Option (List a) -> List a
opt2l opt = option opt nil id

insert :: (a -> a -> Boolean) -> a -> List a -> List a
insert cmp x l = option (head l) (cons x nil) $ \y -> cmp x y ? cons x l $ cons y $ insert cmp x $ opt2l $ tail l

-- primitive operations

cons :: a -> List a -> List a
cons x l = List $ \c e -> c x $ foldr l c e

nil :: List a
nil = List $ const id

-- derived operations

sum, product :: List Number -> Number
sum l = foldr l plus 0
product l = foldr l times 1

-- derived constructors

iterate :: (a -> a) -> a -> List a
iterate f x = cons x $ iterate f $ f x

repeat :: a -> List a
repeat x = cons x $ repeat x

cycle :: List a -> List a
cycle l = null l ? error undefined $ append l $ cycle l

replicate :: Number -> a -> List a
replicate n x = zero n ? nil $ cons x $ replicate (pred n) x

-- more derived operations

null :: List a -> Boolean
null l = foldr l (const $ const false) true

length :: List a -> Number
length l = foldr l (const succ) 0

snoc :: List a -> a -> List a
snoc l x = List $ \c e -> foldr l c $ c x e

append :: List a -> List a -> List a
append l = foldr l (\x f xs -> cons x $ f xs) id

concat :: List (List a) -> List a
concat l = foldr l append nil

map :: (a -> z) -> List a -> List z
map f l = foldr l (\x xs -> cons (f x) xs) nil

filter :: (a -> Boolean) -> List a -> List a
filter p l = foldr l (\x -> p x ? cons x $ id) nil

take :: Number -> List a -> List a
take n l = foldr l (\x r k -> zero k ? nil $ cons x $ r $ pred k) (const nil) n

drop :: Number -> List a -> List a
drop n l = foldr l (\x r k -> zero k ? cons x (r k) $ r $ pred k) (const nil) n

splitAt :: Number -> List a -> Pair (List a) (List a)
splitAt n l = pair (take n l) (drop n l)

get :: Number -> List a -> Option a
get n l = foldr l (\x r k -> zero k ? just x $ r $ pred k) (const nothing) n

set :: Number -> a -> List a -> List a
set n y l = foldr l (\x r k -> cons (eq k n ? y $ x) (r $ succ k)) (const nil) 0

any :: (a -> Boolean) -> List a -> Boolean
any p l = foldr l (\x -> or $ p x) false

all :: (a -> Boolean) -> List a -> Boolean
all p l = foldr l (\x -> and $ p x) true

find :: (a -> Boolean) -> List a -> Option a
find p l = foldr l (\x r -> p x ? just x $ r) nothing

findIndex :: (a -> Boolean) -> List a -> Option Number
findIndex p l = foldr l (\x r k -> p x ? just k $ r $ succ k) (const nothing) 0

partition :: (a -> Boolean) -> List a -> Pair (List a) (List a)
partition p l = pair (filter p l) (filter (\x -> not $ p x) l)

span :: (a -> Boolean) -> List a -> Pair (List a) (List a)
span p l = option (head l) (pair nil nil) $ \x -> p x ? (first (cons x) $ span p $ opt2l $ tail l) $ pair nil l

minimumBy :: (a -> a -> Boolean) -> List a -> Option a
minimumBy cmp l = foldr l (\x oy -> option oy (just x) (\y -> just $ cmp x y ? x $ y)) nothing

maximumBy :: (a -> a -> Boolean) -> List a -> Option a
maximumBy cmp = minimumBy $ \x y -> not $ cmp x y

sortBy :: (a -> a -> Boolean) -> List a -> List a
sortBy cmp l = foldr l (insert cmp) nil

foldl :: List a -> (z -> a -> z) -> z -> z
foldl l f = foldr l (\x r y -> r $ f y x) id 

scanl :: List a -> (z -> a -> z) -> z -> List z
scanl l f z = map (\ys -> foldr ys (flip f) z) $ reverse $ tails $ reverse l

scanr :: List a -> (a -> z -> z) -> z -> List z
scanr l f z = map (\ys -> foldr ys f z) $ tails l

reverse :: List a -> List a
reverse l = foldr l (flip snoc) nil

head :: List a -> Option a
head l = foldr l (\x -> const $ just x) nothing

tail :: List a -> Option (List a)
tail l = null l ? nothing $ just $ drop 1 l

init :: List a -> Option (List a)
init l = foldr l (\x oxs -> option oxs (just nil) (\xs -> just $ cons x xs)) nothing

last :: List a -> Option a
last l = head $ reverse l

zip :: List a -> List b -> List (Pair a b)
zip = zipWith pair

unzip :: List (Pair a b) -> Pair (List a) (List b)
unzip l = foldr l (\p -> uncurry p $ \x y -> double (cons x) (cons y)) $ pair nil nil

newtype RecFold a b = RecFold { runRecFold :: a -> (RecFold a b -> b) -> b }

-- Brazenly stolen from https://doisinkidney.com/posts/2016-04-17-folding-two-at-once.html
-- Sorry, could not figure out a better solution; mine was getting into timed out state
zipWith :: (a -> b -> c) -> List a -> List b -> List c
zipWith f xs ys = foldr xs h (const nil) $ RecFold $ foldr ys g (\_ _ -> nil) where
  g e2 r2 e1 r1 = cons (f e1 e2) $ r1 $ RecFold r2
  h e r x = runRecFold x e r
