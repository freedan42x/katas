const rot13 = s => {
  const eng = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ',
        rot = 'nopqrstuvwxyzabcdefghijklmNOPQRSTUVWXYZABCDEFGHIJKLM';

  return s.replace(/[a-z]/gi,e=>rot[eng.indexOf(e)]);
}
