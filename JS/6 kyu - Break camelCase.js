const solution=str=>{
  var 
    up   = str.match(/[A-Z]/g),
    t    = str.split(/[A-Z]/g),
    arr  = [];
  for (var i = 0; i < t.length; i++) {
    arr.push(up[i-1]+t[i]);
  }
  return arr.join` `.replace(/undefined/g,'');
}
