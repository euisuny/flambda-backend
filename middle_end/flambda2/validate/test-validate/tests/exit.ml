let rec at_exit f = at_exit f

(* let [@inline never] major : unit -> unit = fun () -> ()
 * let [@inline never] naked_pointers_checked : unit -> bool = fun () -> true *)
external major : unit -> unit = "caml_gc_major"
external naked_pointers_checked : unit -> bool
  = "caml_sys_const_naked_pointers_checked"
let () = if naked_pointers_checked () then at_exit major
