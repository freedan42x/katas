def ip_to_num(ip):
    s = 0x0
    
    for i, oct in enumerate(ip.split('.')):
        s |= int(oct) << (3 - i) * 8
    
    return s

def num_to_ip(num):
    nums = []
    
    for i in range(4):
        nums.append((num >> (3 - i) * 8) & 0xFF)
        
    return '.'.join(map(str, nums))
