Array.prototype.min = function () {
return Math.min.apply(Math, this);
}

Array.prototype.max = function () {
return Math.max.apply(Math, this);
}

function sumArray(array) {
  if (array != null && array != '' && array.length > 1)
    return eval(array.join('+')) - array.min() - array.max();
  else
    return 0;
}
