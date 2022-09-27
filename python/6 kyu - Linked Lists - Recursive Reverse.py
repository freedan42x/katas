class Node(object):
    def __init__(self, data=None, next=None):
        self.data = data
        self.next = next

def reverse(head, acc=None):
    if head:
        return reverse(head.next, Node(head.data, acc))

    return acc
