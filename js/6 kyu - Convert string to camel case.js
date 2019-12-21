function toCamelCase(str){
  if (str !== '') {
    var a, arr;
    if (/\-/.test(str))
      a = '-';
    else
      a = '_';
    arr = str.split(a);
    for (var i = 1; i < arr.length; i++) {
      arr[i] = arr[i][0].toUpperCase() + arr[i].slice(1);
    }
    return arr.join``;
  }
  return '';
}
