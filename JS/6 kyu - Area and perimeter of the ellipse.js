const elipse = (a,b) => 'Area: ' + (Math.PI * a * b)
                  .toFixed(1) + ', perimeter: ' + (Math.PI * (3 / 2 * (a + b) - Math.sqrt(a * b)))
                  .toFixed(1);
