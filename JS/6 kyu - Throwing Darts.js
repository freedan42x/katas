const scoreThrows = r => {
  var 
      bonus  = r.every(e => e < 5) ? 100 : 0,
      arr    = r.map(e => e > 10 ? 0 : e < 5 ? 10 : 5),
      sum    = eval(arr.join`+`),
      result = sum + bonus;
  return result || 0;
}
