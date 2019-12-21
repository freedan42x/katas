function keysAndValues(data){
  var keys=[],values=[];
  for (var i in data) {
    keys.push(i);
    values.push(data[i]);
  }
  return [keys, values]
}
