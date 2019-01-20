module Amazon where 

countArara :: Int -> String
countArara 1 = "anane"
countArara n
  | even n = unwords $ replicate (n `div` 2) "adak"
  | otherwise = unwords (replicate (n `div` 2) "adak") ++ " anane"
