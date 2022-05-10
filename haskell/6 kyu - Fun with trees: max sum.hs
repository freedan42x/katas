module MaxSum (maxSum) where

import MaxSumPreload

-- defined in MaxSumPreload
-- data TreeNode = Node TreeNode Int TreeNode | Leaf Int | None

maxSum :: TreeNode -> Int
maxSum None = 0
maxSum (Leaf x) = x
maxSum (Node l x r) = x + max (maxSum l) (maxSum r)
