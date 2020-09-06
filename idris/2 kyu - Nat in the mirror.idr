module PlusComm

import Conat

%access export

{-
What you've just imported:

codata Conat : Type where
  Coz : Conat
  Cos : Conat -> Conat

codata Bisimulation : Conat -> Conat -> Type where
  Biz : Bisimulation Coz Coz
  Bis : {a : Conat} -> {b : Conat} ->
        (Bisimulation a b) ->
        (Bisimulation (Cos a) (Cos b))

MuGen : Conat
MuGen = Cos MuGen
-}

muGenSucc : Bisimulation (Cos MuGen) MuGen
muGenSucc = Bis muGenSucc

public export
Add : Conat -> Conat -> Conat
Add Coz n = n
Add (Cos m) n = Cos (Add m n)

plusZ : (a : Conat) -> Bisimulation a (Add a Coz)
plusZ Coz = Biz
plusZ (Cos n) = Bis (plusZ n)

trans : {a : Conat} -> {b : Conat} -> {c : Conat} 
  -> Bisimulation a b -> Bisimulation b c -> Bisimulation a c
trans Biz Biz = Biz
trans (Bis p) (Bis q) = Bis (trans p q)

refl : (a : Conat) -> Bisimulation a a
refl Coz = Biz
refl (Cos n) = Bis (refl n)

plusS : (a : Conat) -> (b : Conat) -> Bisimulation (Cos (Add a b)) (Add a (Cos b))
plusS Coz n = Bis (refl n)
plusS (Cos m) n = Bis (plusS m n)

-- Idris weak weak, partial implementation is allowed but there's random test
partial
plusCommutative : (a : Conat) -> (b : Conat) ->
                  Bisimulation (Add a b) (Add b a)
plusCommutative Coz n = plusZ n
plusCommutative (Cos m) n = trans (Bis (plusCommutative m n)) (plusS n m)
