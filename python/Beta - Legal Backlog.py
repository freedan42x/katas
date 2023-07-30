def legal_backlog(cases, max_daily):
    days = 0
    cases = [[k, v] for k, v in cases.items()]
    while True:
        n = max_daily

        cases.sort(key=lambda e: e[1], reverse=True)
        print(cases)
        for i, (k, v) in enumerate(cases):
            if n == 0: break
            if v == 0: continue
            cases[i][1] -= 1
            n -= 1

        if n == max_daily: return days
        days += 1
