from math import log10, floor

count = lambda n: floor(sum(map(log10, range(2, n + 1)))) + 1
