module ChainMe (chain) where

chain :: a -> [a -> a] -> a
chain = foldl $ flip ($)
