module EvenOrOdd where

evenOrOdd :: Integral a => a -> [Char]
evenOrOdd n = if even n then "Even" else "Odd"
