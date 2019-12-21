switcher = lambda arr: ''.join(map(lambda x: {
  '27': '!', '28': '?', '29': ' '}.get(x, chr(123 - int(x))), arr))
