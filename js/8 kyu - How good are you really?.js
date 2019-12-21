const betterThanAverage = (classPoints, yourPoints) => Math.floor(classPoints.reduce((a, sum) => a + sum) / classPoints.length) < yourPoints;
