Math.round = function(number) {
  var x = number - ~~number
  return x<0.5?~~number:~~number+1;
};

Math.ceil = function(number) {
  var x = number - ~~number
  return !x?number:~~number+1;
};

Math.floor = function(number) {
  return ~~number;
};
