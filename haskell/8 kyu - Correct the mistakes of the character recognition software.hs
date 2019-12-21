{-# LANGUAGE LambdaCase #-}
module CodeWars.OCRMistakes where

correct :: String -> String
correct = map (\case '0' -> 'O'; '1' -> 'I'; '5' -> 'S'; e -> e)
