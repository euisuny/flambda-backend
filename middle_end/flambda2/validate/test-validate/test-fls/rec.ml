let foo () =
  let rec g (x : int) =
    ignore (Sys.opaque_identity x);
    g (x + 1)
 in
 g 2
