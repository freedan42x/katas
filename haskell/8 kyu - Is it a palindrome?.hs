module Palindroms where

import Data.Char

isPalindrom :: String -> Bool
isPalindrom str = reverse (map toLower str) == map toLower str
