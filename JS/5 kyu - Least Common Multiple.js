const lcm = (...a) => {   
    var q = Math.abs(a[0]);
    for (var i = 1; i < a.length; i++) {
      var b = Math.abs(a[i]), c = q;
      while (q && b)
         q > b ? q %= b : b %= q;
       q = Math.abs(c*a[i])/(q+b);
     }
    return q;
}
