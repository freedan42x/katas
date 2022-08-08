module Hat where

data Color = WHITE | BLACK deriving (Show, Eq, Enum, Bounded)
data Player = P1 | P2 | P3 | P4 deriving (Show, Eq)

guessHatColor :: (Color, Color, Color, Color) -> Player
guessHatColor (_, b, c, _)
  | b == c = P1
  | otherwise = P2
