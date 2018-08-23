const narcissistic = v => {
  var sum = 0, arr = (''+v).split``, n = arr.length;
  for (var i = 0; i < n; i++) {
    sum = sum + Math.pow(arr[i], n);
  }
  return sum == v;
}
