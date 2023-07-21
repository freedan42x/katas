{-# LANGUAGE DeriveFunctor #-}
module ChanneledState where

import           Data.List

newtype ChanneledState s a =
  ChanneledState ([s] -> (a, [s]))
  deriving Functor

instance Applicative (ChanneledState s) where
  pure x = ChanneledState $ \s -> (x, s)
  ChanneledState f <*> ChanneledState g = ChanneledState $ \ss ->
    let (h, ss' ) = f ss
        (x, ss'') = g ss'
    in  (h x, ss'')

instance Monad (ChanneledState s) where
  ChanneledState f >>= g = ChanneledState $ \ss ->
    let (x, ss')         = f ss
        ChanneledState w = g x
    in  w ss'

type Channel = Int

getFromChannel :: Channel -> ChanneledState s s
getFromChannel chan = ChanneledState $ \ss -> (ss !! chan, ss)

modifyChannel :: Channel -> (s -> s) -> ChanneledState s ()
modifyChannel chan f = ChanneledState $ \ss ->
  let (begin, x : end) = splitAt chan ss in ((), begin <> [f x] <> end)

putInChannel :: Channel -> s -> ChanneledState s ()
putInChannel chan x = modifyChannel chan (const x)

createChannel :: s -> ChanneledState s (Channel)
createChannel x =
  ChanneledState $ \ss -> let chan = length ss in (chan, ss <> [x])

-- Mostly here to generalize the output as to allow more implementation types.
runChannels :: ChanneledState s a -> [s] -> (a, [s])
runChannels (ChanneledState cs) ss = cs ss
