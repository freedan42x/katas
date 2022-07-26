module FunctionEvaluator where

import           Control.Monad
import           Control.Monad.ST
import           Data.STRef
import           Data.Functor
import qualified Data.Map                      as M
import           Data.Maybe


evaluateFunction :: Ord a => (a -> Either b ([a], [b] -> b)) -> a -> b
evaluateFunction f x =
  fromJust $ M.lookup x $ runST $ newSTRef M.empty >>= helper x where

  helper x fsR = do
    b <- case f x of
      Left y -> do
        pure y
      Right (xs, g) -> do
        fs <- readSTRef fsR
        let bsM = sequence $ xs <&> \x' -> case M.lookup x fs of
              Just y -> pure y
              _      -> helper x' fsR <&> fromJust . M.lookup x'

        bs <- bsM
        pure $ g bs

    readSTRef fsR >>= \fs ->
      when (isNothing $ M.lookup x fs) $ modifySTRef fsR $ M.insert x b
    readSTRef fsR
