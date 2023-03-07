
let g  =
  let rec foo () =
    bar ()
  and bar () =
    foo ()
  in
  bar ()
