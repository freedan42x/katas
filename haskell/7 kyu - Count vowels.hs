module CountVowels where

countVowels :: String -> Int
countVowels = length . filter (\e -> e `elem` "aeiou")
