module TreeByLevels where

import TreeByLevels.TreeNode


level :: TreeNode a -> Int -> [a]
level t n = helper 0 n t where
  helper cur n t
    | cur == n
    = [value t]
    | otherwise
    = let l = fmap (helper (succ cur) n) (left t)
          r = fmap (helper (succ cur) n) (right t)
      in  concat $ l <> r

treeByLevels :: Maybe (TreeNode a) -> [a]
treeByLevels Nothing  = []
treeByLevels (Just t) = concat $ takeWhile (not . null) $ map (level t) [0 ..]
