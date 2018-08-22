const solution = (...a) => a.filter((v,i,a) => a.indexOf(v) !== i).length>=1;
