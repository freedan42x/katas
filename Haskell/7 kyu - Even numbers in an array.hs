module EvenNums where 

evenNumbers :: [Int] -> Int -> [Int]
evenNumbers = flip ((reverse .) . (. filter even) . take) . reverse
