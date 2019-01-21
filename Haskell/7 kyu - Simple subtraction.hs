module SimpleSubtraction where 

solve :: Int -> Int -> [Int]
solve a b
  | a == 0 || b == 0 = [a, b]
  | a >= 2 * b = solve (a - (div a (2 * b)) * 2 * b) b
  | b >= 2 * a = solve a (b - (div b (2 * a)) * 2 * a)
  | otherwise = [a, b]
