typedef struct
{
  unsigned long mantissa : 52;
  unsigned long exponent : 11;
  unsigned long sign : 1;
} my_double;

int exponent(double d)
{
  union {
    double d;
    my_double md; 
  } u = {d};
  return u.md.exponent;
}
