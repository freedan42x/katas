module Codewars.Kata.AllNoneAny where

import Prelude hiding (all, any)


all, none, any :: (a -> Bool) -> [a] -> Bool
all  = (notElem False .) . map
none = (null .) . filter
any  = ((not . null) .) . filter
