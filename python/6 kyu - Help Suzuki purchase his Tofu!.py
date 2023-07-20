def buy_tofu(cost, box):
    l = box.split(' ')
    mon = l.count('mon')
    monme = l.count('monme')
    r = cost - monme * 60
    if r < 0 and mon >= cost % 60:
        return [mon, monme, mon + monme * 60, cost // 60 + cost % 60]
    if r > 0 and mon >= r:
        return [mon, monme, mon + monme * 60, monme + r]
    return 'leaving the market'
