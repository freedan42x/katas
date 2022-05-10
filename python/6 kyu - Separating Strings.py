sep_str = lambda s: [[w[i] if i < len(w) else '' for w in s.split()] for i in range(max(map(len, s.split())))]
