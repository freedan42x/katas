def high_and_low(numbers):
    arr = numbers.split(" ")
    arr = list(map(int, arr))
    return str(max(arr)) + " " + str(min(arr))
