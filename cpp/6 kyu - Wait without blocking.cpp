#include <thread>
#include <chrono>

class Timer
{
  const size_t seconds_;
  const std::function<void()> callback_;

public:
  explicit Timer(const size_t seconds, const std::function<void()>& callback)
    : seconds_(seconds), callback_(callback) { };

  void Start() const
  {
    std::thread t{[this]() {
      std::this_thread::sleep_for(std::chrono::seconds(seconds_));
      callback_();
    }};
    t.detach();
  }
};
