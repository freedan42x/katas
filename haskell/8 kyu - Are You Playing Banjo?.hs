module Banjo where

areYouPlayingBanjo :: String -> String
areYouPlayingBanjo str
  | str !! 0 `elem` ['r', 'R'] = str ++ " plays banjo"
  | otherwise = str ++ " does not play banjo"
