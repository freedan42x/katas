module ConcatMe where

-- Make Farmer Thomas happy!

-- The test cases will define concat as "concat = foldr (foldr p q) r"
-- and your goal here is to define "p", "q" and "r"!

p x f xs = x : f xs
q = id
r = []
