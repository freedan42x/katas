module Kata where

import Data.Char

isOpposite :: String -> String -> Bool
isOpposite "" "" = False
isOpposite s1 s2 = s1 == (map (\e -> if isUpper e then toLower e else toUpper e) s2)
