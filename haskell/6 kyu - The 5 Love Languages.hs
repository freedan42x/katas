module LoveLanguages (loveLanguage) where

import Preloaded
import Control.Monad
import Data.List


loveLanguage :: Partner -> Int -> IO LoveLanguage
loveLanguage partner weeks = do
  r <- forM [Words .. Touch] $ \lang -> do
    m <- replicateM weeks $ response lang partner
    pure $ (lang, length $ filter (Neutral ==) m)
  pure $ fst $ head $ sortOn snd r
