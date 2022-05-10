def find_area(points):
    total = 0
    i = 0
    while i + 1 < len(points):
        p1, p2 = points[i], points[i + 1]
        dx, dy = p1.X - p2.X, p1.Y - p2.Y

        trig_area = abs(dx * dy) / 2
        sq_area = abs(dx) * min(p1.Y, p2.Y)
        total += trig_area + sq_area
        
        i += 1

    return total
