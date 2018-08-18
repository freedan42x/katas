function findOutlier(integers) {
  var evenArr = integers.filter(function(num) {
    return num % 2 === 0;
  });
  var oddArr = integers.filter(function(num) {
    return num % 2 !== 0;
  });
  if (evenArr.length === 1) {
    return evenArr[0];
  } else {
    return oddArr[0];
  }
}
