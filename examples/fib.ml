(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*               Pierre Weis, projet Cristal, INRIA Rocquencourt       *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  only by permission.                                                *)
(*                                                                     *)
(***********************************************************************)

(* The Fibonacci function, once more. *)

(*
- Global or toplevel definitions have the syntax let ident = expression;;

- If the definition is recursive, you must write let rec instead of
   let.
*)

let rec fib n =
  if n < 2 then 1 else fib (n - 1) + fib (n - 2)
;;
