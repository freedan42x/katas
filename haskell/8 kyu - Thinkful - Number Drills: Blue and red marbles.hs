module Blue where

guessBlue :: Int -> Int -> Int -> Int -> Double
guessBlue bs rs bf rf = fromIntegral (bs - bf) / fromIntegral (bs - bf + rs - rf)
