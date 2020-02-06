module InfinitelyNestedRadicalExpressions.Kata (fn) where

fn :: Double -> Double
fn x = (1 + sqrt (1 + 4 * x)) / 2
