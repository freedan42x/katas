struct A {
  A operator !() { return {}; }
  bool operator ()() { return true; }
};

#define isParenthesized !A{}
