toBin = n =>
  n ? "" + toBin (~~ (n / 2)) + (n % 2) : ""

toBinaryString = n =>
  n ? toBin (n) : "0"
