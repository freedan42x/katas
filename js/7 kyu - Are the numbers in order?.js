function inAscOrder(arr) {
  var prev, cur;
  for (var i = 0; i < arr.length; i++) {
    if (i >= 1)
      prev = arr[i-1];
    cur = arr[i];
    if (cur < prev)
      return false;
  }
  return true;
}
