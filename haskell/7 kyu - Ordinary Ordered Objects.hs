module FrequencyFrenzy where

import Data.List (nub, sortOn)


frequency :: Ord a => [a] -> [(a, Int)]
frequency xs = sortOn fst $ map (\x -> (x, length $ filter (x ==) xs)) $ nub xs
