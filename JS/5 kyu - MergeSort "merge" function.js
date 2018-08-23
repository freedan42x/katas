const mergesorted = (a, b) => {
  var n = [a,b].toString().split(',').map(Number), newArr = [], min = 0, acess = true;
  while (n.length >= 1 && acess) {
    if (n.length === 1) acess = false;
    min = Math.min(...n);
    newArr.push(min);
    n.splice(n.indexOf(min), 1);
  }
  return newArr;
};
