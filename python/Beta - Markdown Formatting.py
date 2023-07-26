styles = {
    'b': '**',
    'i': '_',
    'c': '`',
    's': '~~'
}
def cw_format(word, style):
    s = styles[style]
    return s + word + s
