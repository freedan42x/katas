module Need where

check :: Eq a => [a] -> a -> Bool
check a b = b `elem` a
