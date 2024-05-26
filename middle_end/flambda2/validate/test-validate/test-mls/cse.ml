(* This program is challenging for the validator due to CSE, which changes some
   continuations to take extra arguments (the factored-out expression). *)

[@@@ocaml.flambda_o3]

external unsafe_get: 'a array -> int -> 'a = "%array_unsafe_get"
external unsafe_set: 'a array -> int -> 'a -> unit = "%array_unsafe_set"

let map a =
  unsafe_set a 0 (unsafe_get a 0)
