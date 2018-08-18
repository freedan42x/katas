const combat = function(h, d) {
  if (h > d) {
    return h - d;
  } else {
    return 0;
    return "Health cannot go below 0";
  }
}
