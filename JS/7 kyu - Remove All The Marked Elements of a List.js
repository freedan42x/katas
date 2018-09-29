Array.prototype.remove_ = function(arr, keys){
  return arr.filter(e=>!keys.includes(e));
}
