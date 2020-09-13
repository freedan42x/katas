module FrequencyFrenzy where

import Data.List (nub)


frequency :: Eq a => [a] -> [(a, Int)]
frequency xs = map (\x -> (x, length $ filter (x ==) xs)) $ nub xs
