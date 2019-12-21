{-# LANGUAGE ScopedTypeVariables, Rank2Types #-}
module ScottEncoding where

import Prelude hiding (null, length, map, foldl, foldr, take, fst, snd, curry, uncurry, concat, zip, (++))

newtype SMaybe a = SMaybe { runMaybe :: forall b. b -> (a -> b) -> b }
newtype SList a = SList { runList :: forall b. b -> (a -> SList a -> b) -> b }
newtype SEither a b = SEither { runEither :: forall c. (a -> c) -> (b -> c) -> c }
newtype SPair a b = SPair { runPair :: forall c. (a -> b -> c) -> c }

toPair :: SPair a b -> (a,b)
toPair p = (fst p, snd p)
fromPair :: (a,b) -> SPair a b
fromPair (a, b) = SPair $ \p -> p a b
fst :: SPair a b -> a
fst (SPair p) = p const
snd :: SPair a b -> b
snd (SPair p) = p $ const id
swap :: SPair a b -> SPair b a
swap p = fromPair (snd p, fst p)
curry :: (SPair a b -> c) -> (a -> b -> c)
curry f a b = f $ fromPair (a, b) 
uncurry :: (a -> b -> c) -> (SPair a b -> c)
uncurry f p = f (fst p) $ snd p

toMaybe :: SMaybe a -> Maybe a
toMaybe (SMaybe f) = f Nothing Just
fromMaybe :: Maybe a -> SMaybe a
fromMaybe Nothing = SMaybe const
fromMaybe (Just a) = SMaybe $ \_ f -> f a
isJust :: SMaybe a -> Bool
isJust (SMaybe f) = f False $ const True
isNothing :: SMaybe a -> Bool
isNothing = not . isJust
catMaybes :: SList (SMaybe a) -> SList a
catMaybes list = runList list (fromList []) $
  \ma mas -> runMaybe ma (catMaybes mas) $
    \a -> a `cons` catMaybes mas

toEither :: SEither a b -> Either a b
toEither (SEither f) = f Left Right
fromEither :: Either a b -> SEither a b
fromEither (Left a) = SEither $ \f _ -> f a
fromEither (Right b) = SEither $ \_ f -> f b
isLeft :: SEither a b -> Bool
isLeft (SEither f) = f (const True) $ const False
isRight :: SEither a b -> Bool
isRight = not . isLeft
partition :: SList (SEither a b) -> SPair (SList a) (SList b)
partition (SList l) = l (SPair $ \p -> p (fromList []) $ fromList [])
  $ \e l -> SPair $ \p -> case isLeft e of
    True -> p (cons (fstEither e) $ fst $ partition l) $ snd $ partition l
    _    -> p (fst $ partition l) $ cons (sndEither e) $ snd $ partition l
  where
    fstEither :: SEither a b -> a
    fstEither (SEither e) = e id (error "oh..")
    sndEither :: SEither a b -> b
    sndEither (SEither e) = e (error "oh..") id
    

toList :: SList a -> [a]
toList (SList f) = f [] $ \x xs -> x : toList xs
fromList :: [a] -> SList a
fromList [] = SList const
fromList (x : xs) = SList $ \_ ys -> ys x $ fromList xs
cons :: a -> SList a -> SList a
cons a xs = fromList $ a : toList xs
concat :: SList a -> SList a -> SList a
concat xs ys = case toList xs of
  [] -> ys
  (z : zs) -> cons z (concat (fromList zs) ys)
null :: SList a -> Bool
null (SList f) = f True $ \_ _ -> False
length :: SList a -> Int
length xs = case toList xs of
  [] -> 0
  (_ : ys) -> succ . length $ fromList ys
map :: (a -> b) -> SList a -> SList b
map f xs = fromList $ f <$> toList xs
zip :: SList a -> SList b -> SList (SPair a b)
zip a b = case (toList a, toList b) of
  ((x : xs), (y : ys)) -> fromPair (x, y) `cons` zip (fromList xs) (fromList ys)
  _ -> fromList []

foldl :: (b -> a -> b) -> b -> SList a -> b
foldl f a l = case toList l of
  [] -> a
  (x : xs) -> foldl f (f a x) $ fromList xs
foldr :: (a -> b -> b) -> b -> SList a -> b
foldr f a l = case toList l of
  [] -> a
  (x : xs) -> f x $ foldr f a $ fromList xs
take :: Int -> SList a -> SList a
take n (SList f) = f (fromList []) $ \x xs -> case n of
  0 -> fromList []
  n -> x `cons` take (n - 1) xs
