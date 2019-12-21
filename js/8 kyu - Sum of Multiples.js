  var sum = 0;
  if (m <= 0)
    return 'INVALID';
  for (var i = n; i < m; i += n) {
    sum += i;
  }
  return sum;
}
