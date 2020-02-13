{-# LANGUAGE LambdaCase #-}
module Haskell.SylarDoom.Ticker where


interpreter :: String -> String
interpreter = f [0] 0 where
  check cells ix = 
    not $ ix < 0 || length cells <= ix

  replace cells ix op
    | check cells ix = take ix cells ++ [op $ cells !! ix] ++ drop (ix + 1) cells
    | otherwise = cells

  f _ _ "" = ""
  f cells ix (x:xs) =
    case x of
      '>' -> f cells (succ ix) xs
      '<' -> f cells (pred ix) xs
      '*' -> toEnum (if check cells ix then cells !! ix else 0) : f cells ix xs
      '+' -> f (replace cells ix (\case{255 -> 0; n -> succ n})) ix xs
      '-' -> f (replace cells ix (\n -> if n <= 0 then 255 else pred n)) ix xs
      '/' -> f (replace cells ix (const 0)) ix xs
      '!' -> f (cells ++ [0]) ix xs
      _   -> f cells ix xs
