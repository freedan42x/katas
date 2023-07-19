def strength(num):
    return -strength(-num) if num < 0 else bin(num).count('1')

def bits_war(numbers):
    odds = 0
    evens = 0
    for num in numbers:
        if num == 0: continue
        if num & 1: 
            odds += strength(num)
        else:
            evens += strength(num)
    
    if odds == evens: return 'tie'
    if odds > evens: return 'odds win'
    return 'evens win'
