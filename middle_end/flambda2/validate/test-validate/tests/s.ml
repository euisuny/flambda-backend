(* top-level variables are bound to a symbol *)
(* let x =
 *   let y = 3 in
 *   y *)

type t = A of int | B of int | C of int

let[@inline always] g t =
  match t with
  | A n -> n + 1
  | B n -> n + 2
  | C n -> n + 3

let f x : int =
  let y = if x then A 3 else B 2 in
  g y


(* let f x : int =
 *   let y = if x then true else true in
 *   match y with
 *   | true -> 1
 *   | false -> 3 *)
(* local variables are bound as statics? simples? *)
(* let y = Sys.opaque_identity in *)
(* if Sys.opaque_identity true then 2 else y 3 *)

(* let rec f x = 3
 * and g y = f y *)
