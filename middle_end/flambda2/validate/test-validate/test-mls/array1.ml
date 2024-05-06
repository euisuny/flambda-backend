external unsafe_set: 'a array -> int -> 'a -> unit = "%array_unsafe_set"

let map a =
  unsafe_set a 3 10
