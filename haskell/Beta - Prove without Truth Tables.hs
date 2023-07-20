{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module NonPatternMatchingProof (proof) where

import Data.Type.Bool
import Data.Type.Equality

import Prelude (undefined, ($))
import Preloaded


proof :: Bool p -> Bool q -> Bool r -> (p || q) ==> r === (p ==> r) && (q ==> r)
proof p q r = gcastWith (notOrIsAnd p q) $ 
              gcastWith (orCommutative (not p) r) $ 
              gcastWith (orCommutative (not q) r) $ 
              gcastWith (orDistribAndR r (not p) (not q)) $
              gcastWith (orCommutative r (not p &&& not q)) $
              Refl
