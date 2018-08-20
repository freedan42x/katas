function getScore(n) {
  for (var add = 50, val = 0, i = 2; i <= n; add += 50, val += add, i++){}
  return val+50;
}
