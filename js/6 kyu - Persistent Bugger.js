function persistence(num) {
  var i = 0, arr = (''+num).split``;
  while (arr.length > 1) {
    i++;
    arr = (''+arr.reduce((a, b) => a*b)).split``;
  }
  return i;
}
