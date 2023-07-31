def ordinal(number, brief=False):
    if number in (1, 2, 3):
        arr = ['st', 'd', 'd'] if brief else ['st', 'nd', 'rd']
        return arr[number - 1]

    if number < 10 or number % 100 in (11, 12, 13):
        return 'th'    
    
    return ordinal(number % 10, brief)
