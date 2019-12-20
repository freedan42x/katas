# parse([ 1, [ 1, 1 ] ])  -> 'S, N (S, S)'
# parse([ [ [ ], [ ] ] ]) -> 'N (N (), N ())'
def parse(arr):

  if not isinstance(arr, list):
    return '¯\_(ツ)_/¯'
  
  if not any(isinstance(elem, list) for elem in arr):
    return ', '.join(map(lambda _: 'S', arr))
    
  return ', '.join(map(lambda e: f'N ({parse(e)})' if isinstance(e, list) else 'S', arr))


same_structure_as = lambda a, b: parse(a) == parse(b)
