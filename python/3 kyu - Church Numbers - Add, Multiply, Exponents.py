church_add = lambda m: lambda n: lambda f: lambda x: n (f) (m (f) (x))
church_mul = lambda m: lambda n: lambda f: lambda x: n (m (f)) (x)
church_pow = lambda m: lambda n: n (m)
