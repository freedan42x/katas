String.prototype.repeat = function(count) {
  for (var str = ''; count > 0; count--) str += this;
  return str;
};
