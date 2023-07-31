def unpack(xs):
    if isinstance(xs, (type(None), int, str)):
        return [xs]

    if isinstance(xs, dict):
        return unpack(xs.items())

    return [y for x in xs for y in unpack(x)]
