let rec rev_append l1 =
  match l1 with
    [] -> []
  | _ :: l -> rev_append l

let rev l = rev_append l

let fold_left_map () = (), rev []
