module Bonus where

iHazBonus :: Float -> Bool -> String

iHazBonus s b = if b then
  '$' : show (s * 10)
  else '$' : show s
