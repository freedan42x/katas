const twoOldestAges = arr => [arr.sort((a,b)=>b-a)[0]].concat(arr[1]).reverse();
