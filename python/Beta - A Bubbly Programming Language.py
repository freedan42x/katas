import operator


push = 'Tesla'
end  = 'Senpai'
add  = 'I'
sub  = 'love'
mul  = 'you'
div  = '<3'

ops = {
  add: operator.add,
  sub: operator.sub,
  mul: operator.mul,
  div: operator.floordiv
}

start = lambda c, s=[]: (
  s[0] if c == end else (
    lambda x: (
      lambda c: (
        start(c, [x] + s)
      )
    )
  ) if c == push else (
    lambda c_: (
      start(c_, [ops[c](s[0], s[1])] + s[2:])
    )
  )
)
