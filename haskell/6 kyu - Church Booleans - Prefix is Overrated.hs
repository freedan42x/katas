{-# LANGUAGE GADTs, TypeFamilies #-}
module ChurchBooleans (n,o,t,a,d,r,x) where

import Preloaded (false, true)


data Loli hentai
data Neko cute ayaya
data Pat baka where
  OwO :: Pat (Loli hentai)
  UwU :: Pat (Neko cute ayaya)

type family Hug x where
  Hug (Loli hentai) = hentai -> hentai -> hentai
  Hug (Neko cute ayaya) = ayaya -> cute -> cute -> cute

n :: Pat loli -> Hug loli
n OwO = false
n UwU = const false
o = const true
t = OwO
a = const id
d = UwU
r = id
x = undefined
