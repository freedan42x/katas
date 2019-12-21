const decodeMorse = s => { 
  var arr = s.replace(/   /g, ' _ ').split(' ');
  for (var i = 0; i < arr.length; i++) {
    if (arr[i] !== '_')
      arr[i] = MORSE_CODE[arr[i]];
  }
  return arr.join('').replace(/_/g, ' ').trim();
}
