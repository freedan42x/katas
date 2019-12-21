function getDivisorsCnt(n){
    var arr = [];
    for (var i = 0; i <= n; i++) {
      if (n%i===0)
        arr.push(i);
    }
    return arr.length;
}
