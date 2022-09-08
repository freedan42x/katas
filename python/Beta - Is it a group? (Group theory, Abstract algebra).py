class Group:
    # A group is an object with a set and a binary operation attached
    def __init__(self, group_set, binary_operation):
        self.group_set = group_set
        self.binary_operation = binary_operation

    def is_group(self):
        S = self.group_set
        op = self.binary_operation
        
        # The binary operation is closed under the set
        for a in S:
            for b in S:
                if op(a, b) not in S:
                    return False
        
        # The binary operation is associative under the set
        for a in S:
            for b in S:
                for c in S:
                    if op(op(a, b), c) != op(a, op(b, c)):
                        return False

        # There exists an identity element
        I = None
        for I in S:
            if all(op(I, a) == a == op(a, I) for a in S):
                break
        else:
            return False    
        
        # There is an inverse element for each element in the set
        for a in S:
            for b in S:
                if op(a, b) == I == op(b, a):
                    break
            else:
                return False

        return True
