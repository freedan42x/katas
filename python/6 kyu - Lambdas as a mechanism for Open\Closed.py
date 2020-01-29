spoken    = lambda greeting: greeting + '.'
shouted   = lambda greeting: greeting.upper() + '!'
whispered = lambda greeting: greeting.lower() + '.'

greet = lambda style, msg: style(msg)
