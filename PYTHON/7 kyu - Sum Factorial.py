from functools import reduce
factorial=lambda n:reduce(lambda a,b:a*b,range(1,n+1))
sum_factorial=lambda a:sum(map(factorial,a))
