{-# LANGUAGE TypeApplications #-}
module ParseListFromString (parse) where

parse :: String -> [Word]
parse = map (read @Word) . filter (/= "->") . init . words
