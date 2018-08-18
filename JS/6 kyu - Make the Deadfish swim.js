function parse(data) {
  var arr = data.split('');
  var value = 0;
  var _arr = [];
  for (var i = 0; i < arr.length; i++) {
    if (arr[i] === 'i') {
      value += 1;
    }
    if (arr[i] === 'd') {
      value -= 1;
    }
    if (arr[i] === 's') {
      value *= value;
    }
    if (arr[i] === 'o') {
      _arr.push(value);
    }
  }
  return _arr;
}
