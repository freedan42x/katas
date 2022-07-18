typedef unsigned long long ull_t;

template <int m, int n>
struct ackermann
{
  enum : ull_t { value = ackermann<m - 1, ackermann<m, n - 1>::value>::value };
};

template <>
struct ackermann<0, 0>
{
  enum : ull_t { value = 1 };
};

template <int n>
struct ackermann<0, n>
{
  enum : ull_t { value = n + 1 };
};

template <int m>
struct ackermann<m, 0>
{
  enum : ull_t { value = ackermann<m - 1, 1>::value };
};
