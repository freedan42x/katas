const checkExam = (ans1, ans2) => {
  let score = 0;
  for (let i = 0; i < ans1.length; i++) {
    if (ans1[i] === ans2[i])
      score += 4;
    else if (ans2[i] === '')
      score += 0;
    else
      score -= 1;
  }
  return score > 0 ? score : 0;
}
