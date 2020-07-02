module Power where


power :: [a] -> [[a]]
power = foldr (\x ys -> ys ++ map (x:) ys) [[]]
