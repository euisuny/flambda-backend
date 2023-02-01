open! Validate

(* FIXME : is there a way to get around this?*)
let cwd = "/usr/local/home/iyoon/workspaces/validation/flambda-backend/"
let extension = ".fl"

(* Test files *)
let simple =
  "/middle_end/flambda2/validate/test-validate/tests/simple.fl"
let simple_alpha =
  "/middle_end/flambda2/validate/test-validate/tests/simple-alpha.fl"
let simple_cont =
  "/middle_end/flambda2/validate/test-validate/tests/simple-cont.fl"
let simple_cont_alpha =
  "/middle_end/flambda2/validate/test-validate/tests/simple-cont-alpha.fl"

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

(* Test suite for checking alpha-equivalence checker [Validate.equiv] *)
let alpha_equivalence_suite =
  [(simple, simple_alpha);
   (simple_cont, simple_cont_alpha)]

let check_alpha_equivalence file1 file2 : unit =
  let comp_unit =
    (* IY: Does it matter which file we instantiate the compilation unit with? *)
    Parse_flambda.make_compilation_unit ~extension ~filename:file1 () in
  Compilation_unit.set_current (Some comp_unit);

  let fl_output = parse_flambda (cwd ^ file1) in
  let core_output = flambda_unit_to_core fl_output in

  let fl_output_alpha = parse_flambda (cwd ^ file2) in
  let core_output_alpha = flambda_unit_to_core fl_output_alpha in

  (* Alpha equivalence check *)
  print Format.std_formatter core_output;
  Format.fprintf Format.std_formatter "@.@.";
  print Format.std_formatter core_output_alpha;

  let alpha_eq = core_eq core_output core_output_alpha in

  Format.fprintf Format.std_formatter "@.@.====[Alpha_equivalence:%s]====@.@."
    (alpha_eq |> Validate.eq_string)

let alpha_equivalence_test_suite =
  Format.fprintf Format.std_formatter "Alpha equivalence test suite:@.@.";
  let _ =
    List.map (fun (e1, e2) -> check_alpha_equivalence e1 e2) alpha_equivalence_suite
  in ()

(* Top-level driver for testing *)
let () =
  Format.fprintf Format.std_formatter "Running Flambda2 Validator...@.";
  alpha_equivalence_test_suite;
  ()
