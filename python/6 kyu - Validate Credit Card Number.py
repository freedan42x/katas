def validate(n):
    digits = [int(c) for c in str(n)]
    for i in range(len(digits) % 2, len(digits), 2):
        digits[i] *= 2
        if digits[i] > 9:
            digits[i] -= 9
    return sum(digits) % 10 == 0
