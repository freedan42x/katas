{-# LANGUAGE TemplateHaskell #-}
module Kata.TupleMaker (tuple) where

import Language.Haskell.TH

-- | Creates a lambda that takes `n` arguments and
-- | returns an n-tuple of those arguments.
tuple :: Int -> Q Exp
tuple 1 = [| \x -> x |]
tuple n = do
  names <- mapM (\x -> newName $ "x" <> show x) [0 .. n - 1]
  pure $ LamE (map VarP names) $ TupE $ map (Just . VarE) names
