module TheFeastOfManyBeasts where

feast :: String -> String -> Bool
feast b d = b !! 0 == d !! 0 && b !! (length b - 1) == d !! (length d - 1)
