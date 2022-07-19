def ip_to_num(ip):
    s = 0x0
    
    for i, oct in enumerate(ip.split('.')):
        s |= int(oct) << (3 - i) * 8
    
    return s

def ips_between(start, end):
    return ip_to_num(end) - ip_to_num(start)
