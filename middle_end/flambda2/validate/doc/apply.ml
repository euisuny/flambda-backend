let b = 42

let [@inline never] f x = x + b

let rec g x =
  h x + b
and [@inline never] h x = g x

let i = g 10
