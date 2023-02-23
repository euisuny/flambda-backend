let rec f x =
  let a = g x in
  (); a
and g x =
  let a = f x in
  (); a
