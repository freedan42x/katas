const solution=(...s)=>{
  const a = s.sort((a,b)=>a-b);
  return a[0]+a[1]+a[0];
}
