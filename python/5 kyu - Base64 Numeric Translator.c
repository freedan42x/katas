lang = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'

def base64_to_base10(str):
    result = 0
    for (i, s) in enumerate(str[::-1]):
        result += lang.index(s) * 64 ** i
    return result
