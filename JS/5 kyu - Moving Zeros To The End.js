const moveZeros = a => {
  var z = [];
  for (var i = 0; i < a.length; i++) {
      if (a[i] === 0) {
          a.splice(i, 1);
          z.push(0);
          i--;
      }
  }
  return a.concat(z);
}
