{-# LANGUAGE GADTs, MultiParamTypeClasses, FlexibleInstances #-}
module Postfix where


data Push = Push
data Add = Add
data End = End


class Begin instr r where
  begin' :: [Int] -> instr -> r

instance x ~ Int => Begin End x where
  begin' (x:_) End = x

instance (x ~ Int, Begin instr r) => Begin Push (x -> instr -> r) where
  begin' stack Push x = begin' $ x : stack

instance Begin instr r => Begin Add (instr -> r) where
  begin' (x:y:stack) Add = begin' $ x + y : stack


begin :: Begin instr r => instr -> r
begin = begin' []

push  = Push
add   = Add
end   = End
