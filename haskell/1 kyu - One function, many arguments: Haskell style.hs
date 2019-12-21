{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, GADTs #-}
module PolyvariadicFunctions where


class PolyAdd a where
  polyAdd' :: Int -> a

instance PolyAdd Int where
  polyAdd' = id

instance (a ~ Int, PolyAdd b) => PolyAdd (a -> b) where
  polyAdd' x y = polyAdd' (x + y)

polyAdd :: PolyAdd a => a
polyAdd = polyAdd' 0


class PolyWords a where
  polyWords' :: String -> a

instance PolyWords String where
  polyWords' = id

instance (a ~ String, PolyWords b) => PolyWords (a -> b) where
  polyWords' x y = polyWords' (if null x then y else x ++ " " ++ y)
  
polyWords :: PolyWords a => a
polyWords = polyWords' ""


class PolyList a b | b -> a where
  polyList' :: [a] -> b

instance PolyList a [a] where
  polyList' = id

instance PolyList a b => PolyList a (a -> b) where
  polyList' xs x = polyList' (xs ++ [x])

polyList :: PolyList a b => b
polyList = polyList' []
