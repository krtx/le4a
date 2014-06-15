let makefact maker x =
  if x < 1 then 1 else x * maker maker (x + (-1))
in let fact x = makefact makefact x in fact 10
