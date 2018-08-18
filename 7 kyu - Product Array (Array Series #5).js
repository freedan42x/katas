function productArray(numbers){
  var arr = [];
  for (var i = 0; i < numbers.length; i++) {
    arr.push(numbers.reduce((a, b) => a * b) / numbers[i]);
  }
  return arr;
}
