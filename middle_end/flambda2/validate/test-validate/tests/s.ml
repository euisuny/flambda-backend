(* top-level variables are bound to a symbol *)
let x =
  let y = 3 in
  y

(* local variables are bound as statics? simples? *)
(* let y = Sys.opaque_identity in *)
(* if Sys.opaque_identity true then 2 else y 3 *)

(* let rec f x = 3
 * and g y = f y *)
