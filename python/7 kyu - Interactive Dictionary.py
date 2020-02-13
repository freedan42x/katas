class Dictionary():
  def __init__(self):
    self.items = {}
    
  def newentry(self, word, definition):
    self.items[word] = definition
    
  def look(self, key):
    return self.items.get(key, f"Can't find entry for {key}")
