import re

REQUIRED_ELEMENTS = 'H', 'C', 'N', 'O', 'P', 'Ca'

def best_planet(solar_system, max_size):
    ps = []
    for planet in solar_system:
        elems, sz = planet.split('_')
        elems = re.findall(r'[A-Z][a-z]?', elems)
        sz = int(sz)
        if sz <= max_size and all(e in elems for e in REQUIRED_ELEMENTS):
            ps.append((planet, abs(max_size - sz)))

    ps.sort(key=lambda e: e[1])
    if not ps: return ''
    return ps[0][0]
