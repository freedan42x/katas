def sequence_classifier(arr):
    
    xs = iter(arr)
    codes = []
    while True:
      try:
        x = next(xs)
        y = next(xs)
        if x < y:
          codes.append(1)
        elif x == y:
          codes.append(6)
        else:
          codes.append(3)
      except:
        break
        
    if 1 in codes:   
      if 3 in codes:   
        return 0      
      if 6 in codes:
        return 2
      return 1
    if 3 in codes:
      if 6 in codes:
        return 4
      return 3
    return 5
      
    
