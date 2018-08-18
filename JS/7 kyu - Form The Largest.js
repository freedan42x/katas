function maxNumber(n) {
  var newArr = [], max = 0, acess = true, pos;
  n = n.toString().split('').map(Number);
  while (n.length >= 1 && acess) {
    if (n.length === 1) acess = false;
    max = Math.max(...n);
    newArr.push(max);
    pos = n.indexOf(max);
    n.splice(pos, 1);
  }
  return +newArr.join('');
}
