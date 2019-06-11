@countcalls
def replicate(times, number):
    if times <= 0:
        return []
    return [number] + replicate(times - 1, number)
