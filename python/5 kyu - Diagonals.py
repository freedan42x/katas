def diagonals(matrix):
    if len(matrix) == 1: return matrix
    
    ds = []

    for y in range(0, len(matrix)):
        ds.append([matrix[y + s][s] for s in range(0, len(matrix) - y)])
        ds.append([matrix[y + s][len(matrix) - s - 1] for s in range(0, len(matrix) - y)])

    for x in range(1, len(matrix)):
        ds.append([matrix[s][x + s] for s in range(0, len(matrix) - x)])
        ds.append([matrix[s][len(matrix) - x - s - 1] for s in range(0, len(matrix) - x)])

    return ds
