const camelize = str => str
                        .trim()
                        .toLowerCase()
                        .replace(/[\-_:/'=>]/g,' ')
                        .replace(/\b\w/g,e=>e.toUpperCase())
                        .replace(/\s/g,'');
