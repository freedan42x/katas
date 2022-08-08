module Balanced.Parens where


balancedParens :: Int -> [String]
balancedParens n = helper n n "" where
  helper 0 closed acc = [acc <> replicate closed ')']
  helper _ 0      acc = [acc]
  helper open closed acc =
    let l = helper (open - 1) closed (acc <> "(")
        r = helper open (closed - 1) (acc <> ")")
    in  if closed > open then l <> r else l
