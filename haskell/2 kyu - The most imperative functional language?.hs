module Imperative
  ( def
  , var
  , lit
  , while
  , (+=)
  , (-=)
  , (*=)
  )
where

import           Data.IORef
import           System.IO.Unsafe
import           Control.Monad


type Lang = IO
type Var = IORef

def :: Lang (Var a) -> a
def = unsafePerformIO . readIORef . unsafePerformIO

var :: a -> Lang (Var a)
var = newIORef

lit :: a -> Var a
lit = unsafePerformIO . newIORef

while :: Var a -> (a -> Bool) -> Lang () -> Lang ()
while v p act = readIORef v >>= \x -> when (p x) $ act >> while v p act

binOp :: (a -> a -> a) -> Var a -> Var a -> Lang ()
binOp f v1 v2 = readIORef v2 >>= modifyIORef v1 . flip f

(+=), (-=), (*=) :: Var Integer -> Var Integer -> Lang ()
(+=) = binOp (+)
(-=) = binOp (-)
(*=) = binOp (*)
