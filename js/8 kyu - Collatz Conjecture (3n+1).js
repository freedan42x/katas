var hotpo = function(n){
    if (n == 0) return 0; 
    let i = 0;
    while (n != 1) {
      if (n % 2 == 0) {
        n /= 2;
        i++;
      } else {
        n = 3 * n + 1;
        i++;
      }
    }
    return i;
}
