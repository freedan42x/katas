module CalculatingWithFunctions where

type FNum = (Int -> Int) -> Int

plus, minus, times, dividedBy :: FNum -> Int -> Int
plus f x = f $ \y -> x + y
minus f x = f $ \y -> x - y
times f x = f $ \y -> x * y
dividedBy f x = f $ \y -> x `div` y

zero, one, two, three, four, five, six, seven, eight, nine :: FNum
zero f = f 0
one f = f 1
two f = f 2
three f = f 3
four f = f 4
five f = f 5
six f = f 6
seven f = f 7
eight f = f 8
nine f = f 9
