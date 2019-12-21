module MultNumAsStrings where

multiply :: String -> String -> String
multiply a b = show $ read a * read b
