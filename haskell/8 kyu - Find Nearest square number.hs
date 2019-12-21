module NearestSquare where 

nearestSquare :: Int -> Int
nearestSquare n = round (sqrt $ fromIntegral n) ^ 2
