function minValue(n) {
  var newArr = [], min = 0, acess = true;
  while (n.length >= 1 && acess) {
    if (n.length === 1) acess = false;
    min = Math.min(...n);
    newArr.push(min);
    n = n.filter(n => n != min);
  }
  return +newArr.join('');
}
