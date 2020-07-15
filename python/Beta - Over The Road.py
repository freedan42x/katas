over_the_road = lambda a, n: -1 if a>n*2 or n<1 or a<1 else 2*(n-a//2)+(a&1==0)
