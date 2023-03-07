open! Translate
open! Validate

let get_module_info = Flambda2.get_module_info

(* FIXME : is there a way to get around this?*)
let cwd = "/usr/local/home/iyoon/workspaces/validation/flambda-backend/"
let extension = ".fl"

(** Test file locations **)
let test_dir =
  "/middle_end/flambda2/validate/test-validate/tests/"

let print = Flambda2_core.print

(** Parsing **)
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

(** Test suite for checking alpha-equivalence checker [Validate.equiv].
   To add more test cases, add a pair of files that should be alpha-equivalent
    to this list. **)
(* IY: Why does having [extension] concatenated throw an error? *)
let alpha_equivalence_suite =
  [
    ("simple.fl", "simple-alpha.fl");
    ("simple-cont.fl", "simple-cont-alpha.fl");
    ("simple-static.fl", "simple-static-not-alpha.fl");
    ("closures.fl", "closures-alpha.fl")
  ]

let check_alpha_equivalence file1 file2 : unit =
  let comp_unit =
    (* IY: Does it matter which file we instantiate the compilation unit with? *)
    Parse_flambda.make_compilation_unit ~extension ~filename:file1 () in
  Compilation_unit.set_current (Some comp_unit);

  Format.fprintf Format.std_formatter
   "..............................................................................@.";
  let fl_output = parse_flambda (cwd ^ test_dir ^ file1) in
  let core_output = flambda_unit_to_core fl_output in

  let fl_output_alpha = parse_flambda (cwd ^ test_dir ^ file2) in
  let core_output_alpha = flambda_unit_to_core fl_output_alpha in

  (* Alpha equivalence check *)
  print Format.std_formatter core_output;
  Format.fprintf Format.std_formatter
    "@.------------------------------------------------------------------------------@.";
  print Format.std_formatter core_output_alpha;

  let alpha_eq = Equiv.core_eq core_output core_output_alpha in

  Format.fprintf Format.std_formatter
    "@..............................[α-equivalent?:%s]............................@.@."
    (alpha_eq |> Equiv.eq_string |> String.uppercase_ascii)

let alpha_equivalence_test_suite (_ : unit) =
  Format.fprintf Format.std_formatter "⟪α-Equivalence Test Suite⟫@.@.";
  let _ = List.map (fun (e1, e2) ->
    check_alpha_equivalence e1 e2) alpha_equivalence_suite
  in ()

let simplify_term file : unit =
  let comp_unit =
    Parse_flambda.make_compilation_unit ~extension ~filename:file () in
  Compilation_unit.set_current (Some comp_unit);
  let fl_output :Flambda_unit.t = parse_flambda (cwd ^ test_dir ^ file) in

  let cmx_loader = Flambda_cmx.create_loader ~get_module_info in

  (* IY: What is [round]? *)
  let {Simplify.unit = simplify_result ; _ } =
    Simplify.run ~cmx_loader ~round:0 fl_output in

  Format.fprintf Format.std_formatter
    "@.[Flambda_unit exprs]-------------------------------------------------------@.@.";
  Format.fprintf Format.std_formatter "%a@." Flambda_unit.print fl_output;
  Format.fprintf Format.std_formatter
    "---------------------------↓↓--[simplify]--↓↓-------------------------------@.";
  Format.fprintf Format.std_formatter "%a@.@." Flambda_unit.print simplify_result;

  let src_core = flambda_unit_to_core fl_output in
  let tgt_core = flambda_unit_to_core simplify_result in

  Format.fprintf Format.std_formatter
    "-----------------------------------------------------------------------------@.";
  Format.fprintf Format.std_formatter
   "⟪ Translated Core Exprs ⟫----------------------------------------------------@.";
  Format.fprintf Format.std_formatter
    "-----------------------------------------------------------------------------@.@.";

  print Format.std_formatter src_core;
  Format.fprintf Format.std_formatter
    "@.-----------------------------↓↓--[simplify]--↓↓-------------------------------@.";
  print Format.std_formatter tgt_core;
  Format.fprintf Format.std_formatter
    "@.@.------------------------------------------------------------------------------@."


(* FIXME: Flushing to stdoutput seems to behave erratically, can't factor out the
   stylized breaklines *)
let normalize_term file : unit =
  let comp_unit =
    Parse_flambda.make_compilation_unit ~extension ~filename:file () in
  Compilation_unit.set_current (Some comp_unit);
  let fl_output :Flambda_unit.t = parse_flambda (cwd ^ test_dir ^ file) in

  let cmx_loader = Flambda_cmx.create_loader ~get_module_info in

  (* IY: What is [round]? *)
  let {Simplify.unit = simplify_result ; _ } =
    Simplify.run ~cmx_loader ~round:0 fl_output in

  let src_core = flambda_unit_to_core fl_output in
  let tgt_core = flambda_unit_to_core simplify_result in

  Format.fprintf Format.std_formatter
    "\t\t\t\tNormalizing...\t\t\t@.";
  Format.fprintf Format.std_formatter
    "------------------------------------------------------------------------------@.";

  let src_core = src_core |> normalize in
  let tgt_core = tgt_core |> normalize in

  let alpha_eq = Equiv.core_eq src_core tgt_core in

  Format.fprintf Format.std_formatter
  "@.--------------------------------------------------------------------[original]@.";
  print Format.std_formatter src_core;
  Format.fprintf Format.std_formatter
    "@.-------------------------------------------------------------------[simplified]@.";
  print Format.std_formatter tgt_core;
  Format.fprintf Format.std_formatter
    "@..............................[α-equivalent?:%s]............................."
    (alpha_eq |> Equiv.eq_string |> String.uppercase_ascii);
  Format.fprintf Format.std_formatter
    "@.==============================================================================@. ";
  ()

(** Top-level driver for testing **)
let () =
  (* [Alpha-equivalence tester] *)

  (* Format.fprintf Format.std_formatter "Running Flambda2 Validator...@.@.";
   * alpha_equivalence_test_suite (); *)

  (* [Sanity check] *)

  (* simplify_term "foo.fl";
   * normalize_term "foo.fl"; *)

  (* [Testing let, let-cont binding] *)

  (* simplify_term "let.fl";
   * normalize_term "let.fl"; *)

  (* simplify_term "let2.fl";
   * normalize_term "let2.fl"; *)

  (* [Full FL file generated from `let x = 42`] *)

  (* simplify_term "let3.fl";
   * normalize_term "let3.fl"; *)

  (* simplify_term "scope.fl";
   * normalize_term "scope.fl"; *)

  (* [Closures] *)

  (* simplify_term "apply1.fl";
   * normalize_term "apply1.fl"; *)
  (* simplify_term "apply2.fl";
   * normalize_term "apply2.fl"; *)

  (* [Dead closures are eliminated] *)
  (* simplify_term "apply5.fl";
   * normalize_term "apply5.fl"; *)

  (* simplify_term "apply3.fl";
   * normalize_term "apply3.fl"; *)

  (* [Let bindings can be out-of-order] *)

  (* simplify_term "apply4.fl";
   *  normalize_term "apply4.fl"; *)

  (* [Application] *)

  (* simplify_term "apply.fl";
   * normalize_term "apply.fl"; *)

  (* simplify_term "apply_noinline.fl";
   * normalize_term "apply_noinline.fl"; *)

  (* [Inlining] *)

  (* simplify_term "apply_orig.fl";
   * normalize_term "apply_orig.fl"; *)

  (* simplify_term "noinline.fl";
   * normalize_term "noinline.fl"; *)

  (* [Recursive function] *)

  (* simplify_term "size.fl";
   * normalize_term "size.fl"; *)

  (* [Mutually recursive function] *)

  (* Diverging mutually recursive functions *)
  (* simplify_term "rec.fl";
   * normalize_term "rec.fl"; *)

  (* [Using list] *)

  (* simplify_term "length.fl";
   * normalize_term "length.fl"; *)

  (* 2. test11 :
     [Sets of closures that are mutually recursive to each other]
     [Indirect calls] *)
  (* simplify_term "tests11_simple.fl";
   * normalize_term "tests11_simple.fl"; *)

  (* [Anonymous functions] *)
  (* simplify_term "anon.fl";
   * normalize_term "anon.fl"; *)

  (* The example without partial application works fine *)
  (* simplify_term "tests13_simpler.fl";
   * normalize_term "tests13_simpler.fl"; *)

  (* [Partial application] *)
  (* simplify_term "opaque_partial.fl";
   * normalize_term "opaque_partial.fl"; *)

  (* simplify_term "tests13_simple.fl";
   * normalize_term "tests13_simple.fl"; *)

  (* simplify_term "lengthapply.fl";
   * normalize_term "lengthapply.fl"; *)

  (* simplify_term "tests13_simple2.fl";
   * normalize_term "tests13_simple2.fl"; *)

  (* simplify_term "tests11.fl";
   * normalize_term "tests11.fl"; *)

  (* simplify_term "tests13_simple3.fl";
   * normalize_term "tests13_simple3.fl"; *)

  simplify_term "tests12.fl";
  normalize_term "tests12.fl";

  (* 3. [LetCont : Recursive case] *)

  (* B. Effects *)
  (* [Inlining effectful functions (1) Mutable state] *)

  (* (2) External calls *)


  (* D. Bureaucratic tax *)
  (* Implementing primitive evaluation (arithmetic evaluation..) *)

  (* ----------------------------- *)

  (* More: Stress-testing the validator *)
  (* LATER: Refactor test suite into dune file *)

  ()
