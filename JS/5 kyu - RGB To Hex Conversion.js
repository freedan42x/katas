function rgb(r, g, b) {
  this.c = this.c || function (n) {
    return Math.max(Math.min(n, 255), 0)
  };

  return ((1 << 24) + (this.c(r) << 16) + (this.c(g) << 8) + this.c(b)).toString(16).slice(1).toUpperCase();
}
