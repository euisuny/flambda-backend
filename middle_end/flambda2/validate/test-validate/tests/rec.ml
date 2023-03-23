let foo () =
  let rec g (x : int) = g x
  (* (*   (let rec k () = f () in
   *  *   k ())
   *  * and f () = g () *)
   *   let y = g x
   *   in x + y *)
 in
 g 2
