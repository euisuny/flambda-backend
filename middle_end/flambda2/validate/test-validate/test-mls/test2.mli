val fold_left_map :
  unit -> unit * 'c list
(** [fold_left_map] is  a combination of [fold_left] and [map] that threads an
    accumulator through calls to [f].
    @since 4.11.0
*)
