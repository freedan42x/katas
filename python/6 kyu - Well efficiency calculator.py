from preloaded import FIELD

def is_efficient(x, y, threshold):
    r = 0.0
    for dx in [-1, 0, 1]:
        nx = x + dx
        if nx < 0 or nx >= 20: continue
        for dy in [-1, 0, 1]:
            ny = y + dy
            if ny < 0 or ny >= 20: continue
            r += float(FIELD[nx][ny])
    return r >= threshold
