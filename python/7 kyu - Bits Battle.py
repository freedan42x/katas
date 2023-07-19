def bits_battle(numbers):
    r = 0
    for num in numbers:
        if num == 0: continue
        if num & 1: 
            r += bin(num).count('1')
        else:
            r -= bin(num)[1:].count('0')
    
    if r == 0: return 'tie'
    if r > 0: return 'odds win'
    return 'evens win'
