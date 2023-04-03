external string_length : string -> int = "%string_length"
external string_get : string -> int -> char = "%string_safe_get"

let valid_float_lexem s =
  let l = string_length s in
  let rec loop i =
    if i >= l then s ^ "." else
      match string_get s i with
      | '0' .. '9' | '-' -> loop (i + 1)
      | _ -> s
  in
  loop 0
