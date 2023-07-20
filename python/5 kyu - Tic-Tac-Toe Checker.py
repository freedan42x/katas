def check(board, item):
    for row in range(3):
        if board[row][0] == board[row][1] == board[row][2] == item:
            return True

    for col in range(3):
        if board[0][col] == board[1][col] == board[2][col] == item:
            return True

    if board[0][0] == board[1][1] == board[2][2] == item:
        return True

    if board[0][2] == board[1][1] == board[2][0] == item:
        return True

    return False


def is_solved(board):
    if check(board, 1):
        return 1

    if check(board, 2):
        return 2

    if any(map(lambda i: i == 0, sum(board, []))):
        return -1

    return 0
