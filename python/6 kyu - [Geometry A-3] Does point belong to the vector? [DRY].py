def approx_equal(x, y, eps=1e-4):
    return abs(x - y) <= eps

def inbounds(x, a, b):
    if a > b: a, b = b, a
    return a <= x <= b

def point_in_vector(point, vector):
    x, y = point
    (x1, y1), (x2, y2) = vector

    if x1 == x2:
        return x == x1 and inbounds(y, y1, y2)

    k = (y1 - y2) / (x1 - x2)
    b = y1 - k * x1

    return inbounds(x, x1, x2) \
       and inbounds(y, y1, y2) \
       and approx_equal(y, k*x + b)
