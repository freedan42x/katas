class DimensionsOutOfBoundError(Exception): pass

class Package:
    constraints = {
        'length': (0, 350),
        'width': (0, 300),
        'height': (0, 150),
        'weight': (0, 40)
    }

    def __init__(self, length, width, height, weight):
        self.length = length
        self.width = width
        self.height = height
        self.weight = weight
    
    @property
    def volume(self):
        return self.length * self.width * self.height

    def __setattr__(self, name, value):
        l, h = self.constraints[name]
        if value <= l or value > h:
            raise DimensionsOutOfBoundError(f'Package {name}=={value} out of bounds, should be: {l} < {name} <= {h}')
        super().__setattr__(name, value)
