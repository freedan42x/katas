class choppable:
    def __init__(self, text):
        self.text = text

    def chop_char(self):
        if len(self.text) == 0: return
        
        c = self.text[0]
        self.text = self.text[1:]
        if c.isalpha() or c == '\'':
            return c
    
        return None

    def chop_word(self):
        buf = ''
        while (len(self.text) > 0
               and (c := self.chop_char()) != None):
            buf += c

        if all(c == '\'' for c in buf):
            return ''
        
        return buf

def top_3_words(text):
    ctext = choppable(text)
    words = {}

    while len(ctext.text) > 0:
        if word := ctext.chop_word().lower():
            if words.get(word):
                words[word] += 1
            else:
                words[word] = 1
    
    return list(k for k, _ in sorted(words.items(), key=lambda item: item[1], reverse=True)[:3])
