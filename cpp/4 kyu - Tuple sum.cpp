#include <tuple>

static double r;

void f(int x)
{
  r += x;
}

void f(double x)
{
  r += x;
}

template <typename T>
void f(T t)
{
  (void) t;
}

template <typename... Ts>
void g(Ts... ts)
{
  (f(ts), ...);
}

template <typename... Ts> 
double tuple_sum(const std::tuple<Ts...>& tpl)
{
  r = 0;
  std::apply(g<Ts...>, tpl);
  return r;
}
