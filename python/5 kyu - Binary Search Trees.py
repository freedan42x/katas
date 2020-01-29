class Tree:
    
    def __init__(self, root, left=None, right=None):
        assert root and type(root) == Node
        if left: assert type(left) == Tree and left.root < root
        if right: assert type(right) == Tree and root < right.root

        self.left = left
        self.root = root
        self.right = right
        
    def is_leaf(self):
        return not(self.left or self.right)
        
    
    def __str__(self):
        if self.is_leaf():
            return f'[{str(self.root)}]'
        
        left = str(self.left) if self.left else '_'
        right = str(self.right) if self.right else '_'
        return f'[{left} {str(self.root)} {right}]'
    
    def __eq__(self, other):
        return str(self) == str(other)

    def __ne__(self, other):
        return not(self == other)


class Node:
    
    def __init__(self, value, weight=1):
        self.value = value
        self.weight = weight
    
    def __str__(self):
        return str(self.value)   
    
    def __lt__(self, other):
        return self.value < other.value
    
    def __gt__(self, other):
        return self.value > other.value
    
    def __eq__(self, other):
        return self.value == other.value 

    def __ne__(self, other):
        return self.value != other.value 
