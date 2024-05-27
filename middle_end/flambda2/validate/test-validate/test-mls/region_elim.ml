(* This gets compiled to a program with a begin_region / end_region pair creating a region
   that is never allocated in. We had to add a special case for this, as does flambda2.
   See [Normalize.remove_corresponding_end_region] and its interactions with the
   [Can_delete_if_unused] case of [step_let] (which fires for [Begin_region] *)

let trim () =
  let _ = ref 0 in
  ()

