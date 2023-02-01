(* FIXME : is there a way to get around this?*)
let cwd = "/usr/local/home/iyoon/workspaces/validation/flambda-backend/"

let parse_flambda file : Flambda_unit.t =
  match Parse_flambda.parse file with
  | Ok unit -> unit
  | Error e ->
    (match e with
      | Parsing_error (msg, loc) ->
        Format.eprintf "%a:@.Syntax error: %s@." Location.print_loc loc msg
      | Lexing_error (error, loc) ->
        Format.eprintf "%a:@.Lex error: %a@." Location.print_loc loc
          Flambda_lex.pp_error error);
    exit 1

let () =
  print_endline "Running Flambda2 Validator...";
  let _ =
    parse_flambda (cwd ^ "/middle_end/flambda2/validate/test-validate/foo.fl")
  in
  ()
