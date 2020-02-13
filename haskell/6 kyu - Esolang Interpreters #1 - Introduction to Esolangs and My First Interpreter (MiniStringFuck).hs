module MiniStringFuck where


myFirstInterpreter :: String -> String
myFirstInterpreter = f 0
  where
    f _   ""       = ""
    f n   ('.':xs) = toEnum n : f n xs
    f 255 ('+':xs) = f 0 xs
    f n   ('+':xs) = f (n + 1) xs
    f n   (_:xs)   = f n xs
