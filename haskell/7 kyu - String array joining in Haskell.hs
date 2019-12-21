module JoinedWords where

joinS :: [[Char]] -> [Char] -> [Char]
joinS xs s = drop (length s) $ xs >>= (s ++)
