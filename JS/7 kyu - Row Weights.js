function rowWeights(array){
  var team1 = 0, team2 = 0;
  for (var i = 0; i < array.length; i++) {
    !(i % 2) ? team1 += array[i] : team2 += array[i];
  }
  return [team1, team2];
}
