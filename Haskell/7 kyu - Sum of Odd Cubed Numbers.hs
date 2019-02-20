module OddCubed.JorgeVS.Kata where

oddCubed :: [Int] -> Int
oddCubed = sum . map (^ 3) . filter odd
