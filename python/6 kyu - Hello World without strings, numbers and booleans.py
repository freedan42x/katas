one = int(() == ())
two = one + one
three = two + one
four = two * two
five = four + one
eight = four * two
ten = eight + two
sixteen = eight * two
twenty = ten * two
thirty_two = sixteen * two
sixty_four = thirty_two * two

def hi_all():
    return str().join(map(chr, [
        sixty_four + ten - two,
        sixty_four + thirty_two + five,
        sixty_four * two - twenty,
        sixty_four * two - twenty,
        sixty_four * two - twenty + three,
        thirty_two,
        sixty_four + twenty + three,
        sixty_four * two - twenty + three,
        sixty_four * two - twenty + three * two,
        sixty_four * two - twenty,
        sixty_four + thirty_two + four
    ]))
