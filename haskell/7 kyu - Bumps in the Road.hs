module Bumps where

bump :: String -> String
bump str = if length (filter (\i -> i == 'n') str) > 15 then "Car Dead" else "Woohoo!"
