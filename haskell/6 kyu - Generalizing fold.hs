{-# LANGUAGE LambdaCase #-}
module Fold where


foldWhile p f z = \case
  x : xs | p r -> foldWhile p f r xs where r = f z x
  _            -> z
