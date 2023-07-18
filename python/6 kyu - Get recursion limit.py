def fetch_recursion_limit():
    def helper(ptr):
        ptr[0] += 1
        helper(ptr)
    ptr = [0]
    try:
        helper(ptr)
    except RecursionError:
        return ptr[0]+2
