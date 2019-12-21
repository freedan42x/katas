const likes = n => {
  switch(n.length) {
    case 0:
      return `no one likes this`;
    case 1:
      return `${n[0]} likes this`;
    case 2:
      return `${n[0]} and ${n[1]} like this`;
    case 3:
      return `${n[0]}, ${n[1]} and ${n[2]} like this`;
    default:
      return `${n[0]}, ${n[1]} and ${n.length-2} others like this`;
  }
}
