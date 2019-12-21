greet = (name, owner) ->
  "Hello #{if name is owner then 'boss' else 'guest'}"
