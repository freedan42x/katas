const reverseNumber=n=>parseInt((/\-/.test(n.toString())?'-':'')+n.toString().replace(/\-/,'').split('').reverse().join(''));
