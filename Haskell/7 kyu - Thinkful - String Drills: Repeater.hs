module Kata where
import Control.Monad

repeater :: String -> Int -> String
repeater = (join .) . flip replicate
