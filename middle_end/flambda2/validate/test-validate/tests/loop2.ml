external string_length : string -> int = "%string_length"

let valid_float_lexem s =
  let l = string_length s in
  let rec loop i =
    if i >= l then s ^ "." else
      match string_length s with
      | 0 -> loop (i + 1)
      | _ -> s
  in
  loop 0
