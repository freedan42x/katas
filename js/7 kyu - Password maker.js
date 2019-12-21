const _ = {
  'i': '1',
  'o': '0',
  's': '5'
},
makePassword = s =>
  s.match(/\b\w/g).join``.replace(/./gi, e => _[e.toLowerCase()] || e);
