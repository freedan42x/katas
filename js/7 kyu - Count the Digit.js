const nbDig = (n, d, r = new RegExp(d, 'g')) =>
  eval(
    [...Array(++n).keys()].map(
      e => ((e * e + '').match(r) || []).length
    ).join`+`
  );
