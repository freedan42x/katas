module Laziness where


mkPair :: Int -> (Int, Int)
mkPair z = (w - y, z - t)
 where
  w = floor $ (pred $ sqrt (succ $ 8 * fromIntegral z)) / 2
  t = (w ^ 2 + w) `div` 2
  y = z - t

points :: [(Int, Int)]
points = mkPair <$> [0..]

type Matrix = [[Bool]]

findTrue :: Matrix -> (Int, Int)
findTrue = helper points where
  helper ((j, i) : r) m
    | m !! j !! i = (j, i)
    | otherwise = helper r m
