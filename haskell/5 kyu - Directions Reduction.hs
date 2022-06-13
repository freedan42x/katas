module Codewars.Kata.Reduction where

import Codewars.Kata.Reduction.Direction


reducable :: Direction -> Direction -> Bool
reducable x y = helper x y || helper y x where
  helper x y = case (x, y) of
    (North, South) -> True
    (East , West ) -> True
    _              -> False

dirReduce :: [Direction] -> [Direction]
dirReduce ds = helper [] ds where
  helper prev cur | prev == cur             = prev
  helper _ cur@(x : y : ds) | reducable x y = helper cur ds
  helper prev cur@(x : ds)                  = helper cur (x : helper prev ds)
  helper _    cur                           = cur
