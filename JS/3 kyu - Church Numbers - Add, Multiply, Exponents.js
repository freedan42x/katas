churchAdd = m => n => f => x => n (f) (m (f) (x))
churchMul = m => n => f => x => n (m (f)) (x)
churchPow = m => n => n (m)
