module Find where


data Val = F (Int -> Bool) | I Int

instance Show Val where
  show (F a) = "F " <> "(Int -> Bool)" 
  show (I a) = "I " <> show a

findFunction :: [Val] -> [Int] -> [Int]
findFunction [] xs = xs
findFunction (F f:_) xs = filter f xs
findFunction (_:fs) xs = findFunction fs xs
