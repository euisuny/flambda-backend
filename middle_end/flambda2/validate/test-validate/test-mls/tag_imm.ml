(* Requires us to transform [prim Tag_imm (simple #0)] into [simple 0] *)

let int32aux () =
  let v = Int32.rem 1l 43l in
  Int32.sub v v > 2l
