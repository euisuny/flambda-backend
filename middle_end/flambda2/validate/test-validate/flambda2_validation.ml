open! Validate

(* FIXME : is there a way to get around this?*)
let cwd = "/usr/local/home/iyoon/workspaces/validation/flambda-backend/"

(* Test files *)
let simple =
  "/middle_end/flambda2/validate/test-validate/tests/simple.fl"
let simple_alpha =
  "/middle_end/flambda2/validate/test-validate/tests/simple-alpha.fl"

(* Parsing *)
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

let extension = ".fl"
let filename = simple

let () =
  print_endline "Running Flambda2 Validator ...\n";

  let comp_unit =
    Parse_flambda.make_compilation_unit ~extension ~filename () in
  Compilation_unit.set_current (Some comp_unit);

  let fl_output = parse_flambda (cwd ^ simple) in
  let core_output = flambda_unit_to_core fl_output in

  let fl_output_alpha = parse_flambda (cwd ^ simple_alpha) in
  let core_output_alpha = flambda_unit_to_core fl_output_alpha in

  (* Alpha equivalence check *)
  print Format.std_formatter core_output;
  Format.fprintf Format.std_formatter "@.@.";
  print Format.std_formatter core_output_alpha;

  let alpha_eq = core_eq core_output core_output_alpha in

  Format.fprintf Format.std_formatter "@.@.Alpha_equality:%s "
    (alpha_eq |> Validate.eq_string);

  ()
