module MakeChange where


data Change = Change
  { h, q, d, n, p :: Int }
  deriving (Eq, Show)

changeDefault = Change 0 0 0 0 0


makeChange :: Int -> Change
makeChange x = Change h q d n p 
  where
    h = x `div` 50
    x' = x - h * 50
    q = x' `div` 25
    x'' = x' - q * 25
    d = x'' `div` 10
    x''' = x'' - d * 10
    n = x''' `div` 5
    p = x''' - n * 5
