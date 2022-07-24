from copy import deepcopy


class Format:
    def __init__(self, tags=[]):
        self.tags = tags

    @property
    def div(self):
        tags = deepcopy(self.tags)
        tags.append('div')
        return Format(tags)

    @property
    def p(self):
        tags = deepcopy(self.tags)
        tags.append('p')
        return Format(tags)

    @property
    def span(self):
        tags = deepcopy(self.tags)
        tags.append('span')
        return Format(tags)

    @property
    def h1(self):
        tags = deepcopy(self.tags)
        tags.append('h1')
        return Format(tags)
    
    def __call__(self, *args):
        s = ''.join(args)
        r = '{}'

        for tag in self.tags:
            r = r.format(f'<{tag}>{{}}</{tag}>')

        return r.format(s)


format = Format()
