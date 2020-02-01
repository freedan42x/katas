module Razor where

import Text.Printf


data Razor
  = Lit Int
  | Add Razor Razor
  
interpret :: Razor -> Int
interpret (Lit n)   = n
interpret (Add m n) = interpret m + interpret n

pretty :: Razor -> String
pretty (Lit n)   = show n
pretty (Add m n) = printf "(%s+%s)" (pretty m) (pretty n)
