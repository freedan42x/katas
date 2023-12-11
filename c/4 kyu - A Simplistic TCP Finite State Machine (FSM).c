#include <stddef.h>

enum event {
	APP_PASSIVE_OPEN, APP_ACTIVE_OPEN, APP_SEND, APP_CLOSE,
  APP_TIMEOUT, RCV_SYN, RCV_ACK, RCV_SYN_ACK, RCV_FIN, RCV_FIN_ACK
};

enum state {
	ERROR, CLOSED, LISTEN, SYN_SENT, SYN_RCVD, ESTABLISHED,
  CLOSE_WAIT, LAST_ACK, FIN_WAIT_1, FIN_WAIT_2, CLOSING, TIME_WAIT,
};

#define EVENT_COUNT (RCV_FIN_ACK + 1)
#define STATE_COUNT (TIME_WAIT + 1)

static const enum state table[STATE_COUNT][EVENT_COUNT] = {
  [CLOSED] = {
    [APP_PASSIVE_OPEN] = LISTEN,
    [APP_ACTIVE_OPEN] = SYN_SENT
  },
  [LISTEN] = {
    [RCV_SYN] = SYN_RCVD,
    [APP_SEND] = SYN_SENT,
    [APP_CLOSE] = CLOSED
  },
  [SYN_RCVD] = {
    [APP_CLOSE] = FIN_WAIT_1,
    [RCV_ACK] = ESTABLISHED
  },
  [SYN_SENT] = {
    [RCV_SYN] = SYN_RCVD,
    [RCV_SYN_ACK] = ESTABLISHED,
    [APP_CLOSE] = CLOSED
  },
  [ESTABLISHED] = {
    [APP_CLOSE] = FIN_WAIT_1,
    [RCV_FIN] = CLOSE_WAIT
  },
  [FIN_WAIT_1] = {
    [RCV_FIN] = CLOSING,
    [RCV_FIN_ACK] = TIME_WAIT,
    [RCV_ACK] = FIN_WAIT_2
  },
  [CLOSING] = {
    [RCV_ACK] = TIME_WAIT
  },
  [FIN_WAIT_2] = {
    [RCV_FIN] = TIME_WAIT
  },
  [TIME_WAIT] = {
    [APP_TIMEOUT] = CLOSED
  },
  [CLOSE_WAIT] = {
    [APP_CLOSE] = LAST_ACK
  },
  [LAST_ACK] = {
    [RCV_ACK] = CLOSED
  }
};

enum state get_TCP_state (size_t n, const enum event events[n])
{
  enum state s = CLOSED;
  for (size_t i = 0; i < n; i++) {
    s = table[s][events[i]];
    if (s == ERROR) break;
  }
	return s;
}
