module If where

_if :: Bool -> a -> a -> a
_if True x y  = x
_if False x y = y
