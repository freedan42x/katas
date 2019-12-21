const countSheep = n => {
  let str = '';
  for (var i = 1; i <= n; i++) {
    str += +i + ' sheep...';
  }
  return str;
}
