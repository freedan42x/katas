const fib = (n, arr = []) => {
    const rec = (i, a, b) => {
        if (i > 0)
            arr.push(a);
        if (i > 1)
            rec(i - 1, b, a + b)
    }
    rec(n, 0, 1);
    return arr;
}
const sumFibs = n => fib(++n).filter(e=>e%2==0).reduce((a,b)=>a+b,0);
