{-# LANGUAGE RankNTypes #-}

module Kata where

import Prelude hiding (error, undefined)
import Control.Monad
import KataPreloaded

from = (. ((ap id .) . flip (.) . flip (.))) . (.)
to   = (. (absurd .)) . ($ id)
