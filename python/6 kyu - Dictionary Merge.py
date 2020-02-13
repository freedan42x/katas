def merge(*dicts):
  result = {}
  for dc in dicts:
    for key in dc:
      result[key] = result.get(key, []) + [dc[key]]
  return result
