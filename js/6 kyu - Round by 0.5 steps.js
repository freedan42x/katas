function solution(n){
  if (n-~~n > 0.25 && n-~~n < 0.75)
    return ~~n+0.5;
  else if (n-~~n < 0.25)
    return ~~n;
  else
    return ~~n+1;
}
