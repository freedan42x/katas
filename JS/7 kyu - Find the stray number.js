const stray = arr => {
  const
    _arr = arr.sort((a,b)=>a-b),
    val  = (arr[0] === arr [1]) ? arr[arr.length-1] : arr[0];
  return val;
}
