const squareSum = (numbers, sum = 0) => {
  for (var i = 0; i < numbers.length; i++) {
    var square = numbers[i] * numbers[i];
    sum += square;
    }
    return sum;
}
