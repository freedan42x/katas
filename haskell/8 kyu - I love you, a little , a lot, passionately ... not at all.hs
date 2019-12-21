module Kata (howMuchILoveYou) where

howMuchILoveYou :: Int -> String
howMuchILoveYou 1 = "I love you"
howMuchILoveYou 2 = "a little"
howMuchILoveYou 3 = "a lot"
howMuchILoveYou 4 = "passionately"
howMuchILoveYou 5 = "madly"
howMuchILoveYou 6 = "not at all"
howMuchILoveYou n = howMuchILoveYou $ n - 6
