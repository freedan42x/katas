const toWeirdCase = str => str
                           .split` `
                           .map(e => e
                           .split``
                           .map((e, i) => i & 1 ? 
                           e.toLowerCase() : 
                           e.toUpperCase())
                           .join``)
                           .join` `;
