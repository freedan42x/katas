module MiniStringFuck where

format :: String -> String
format "" = []
format ('+' : xs) = "+" ++ format xs
format ('.' : xs) = "." ++ format xs
format (_   : xs) = format xs 

myFirstInterpreter :: String -> String
myFirstInterpreter s = f (format s) 0

f :: String -> Int -> String
f "" _ = []
f ('+' : xs) n
  | n == 256  = f xs 1
  | otherwise = f xs (n + 1)
f ('.' : xs) n = [toEnum n] ++ f xs n
