module CountSheep where

countSheep :: Int -> String
countSheep 0 = ""
countSheep n = countSheep (n - 1) ++ (show n ++ " sheep...")
