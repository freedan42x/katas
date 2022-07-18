typedef unsigned long long ull_t;

constexpr ull_t factorial_impl(int n)
{
  if (n <= 1) return 1;

  return n * factorial_impl(n - 1);
}

template <int x>
struct factorial {
  static constexpr ull_t value = factorial_impl(x);
};
