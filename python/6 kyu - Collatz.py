def collatz(n):
    s = ''
    
    while n != 1:
        s += f'{n}->'
        n = 3 * n + 1 if n & 1 else n // 2
    s += '1'
        
    return s
