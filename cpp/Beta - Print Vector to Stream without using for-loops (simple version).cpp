#include <ostream>
#include <vector>

template <typename T>
void print_vector(std::ostream& os, const std::vector<T>& vec) {
  std::function<void(const T*, size_t)> helper = [&](auto rw, auto sz) {
    if (sz == 0) return;
    os << *rw;
    helper(rw + 1, sz - 1);
  };
  
  helper(vec.data(), vec.size());
}
