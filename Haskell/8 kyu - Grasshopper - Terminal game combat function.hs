module Health (updateHealth) where

updateHealth :: Double -> Double -> Double
updateHealth h d
  | h - d < 0 = 0
  | otherwise = h - d
