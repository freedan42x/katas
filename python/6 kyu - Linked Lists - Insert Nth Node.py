class Node(object):
    def __init__(self, data):
        self.data = data
        self.next = None
    
def insert_nth(head, index, data):
    if index == 0:
        new = Node(data)
        new.next = head
        return new
    
    new = Node(head.data)
    new.next = insert_nth(head.next, index - 1, data)
    return new
