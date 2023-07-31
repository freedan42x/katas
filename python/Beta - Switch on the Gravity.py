def switch_gravity(lst):
    done = False
    while not done:
        done = True
        for y in range(len(lst) - 2, -1, -1):
            for x in range(len(lst[y])):
                if lst[y][x] == '#' and lst[y + 1][x] == '-':
                    done = False
                    lst[y][x] = '-'
                    lst[y + 1][x] = '#'
    return lst
