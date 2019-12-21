const indexEqualsValue = a => {
  var n = a.filter(n => a[n]==n);
  if (n.length >= 1)
    return Math.min(...n);
  return -1;
}
