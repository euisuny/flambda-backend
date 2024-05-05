(* In this case, the issue was that we weren't reducing the body of copy before
   putting it in the environment.  Then we we would substitute it under a
   opaque_identity (Obj.magic) and never reduce it.  Fixed by reducing the value
   of let-bound things more eagerly.  I think it would be wrong to reduce under
   opaque_identity, since flambda2 itself should not. *)
let copy a =
  let l = 3 in if l = 0 then [||] else [||]

let to_iarray = Obj.magic (copy : 'a array -> 'a array)
