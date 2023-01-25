module Apply = Apply_expr
module Apply_cont = Apply_cont_expr
module Switch = Switch_expr

(* Simplified core of [flambda2] terms *)
type core_exp =
  | Let of let_expr
  | Let_cont of let_cont_expr
  | Apply of Apply.t
  | Apply_cont of Apply_cont.t
  | Switch of Switch.t
  | Invalid of { message : string }

and let_expr = Bound_pattern.t * core_exp

(* representing the recursive continuations, since this subsumes the non-recursive
   cont exprs *)
and let_cont_expr =
  { continuation : Bound_pattern.t * core_exp;
    bound : Bound_pattern.t;
    body : core_exp; }

type eq = bool

let core_eq _e1 _e2 = true

let flambda_unit_to_core = function
  _ -> Invalid { message = "unimplemented" }

let simplify_result_to_core _e =
  Invalid { message = "unimplemented" }

let validate src tgt =
  let ret_cont = Continuation.create ~sort:Toplevel_return () in
  let exn_cont = Continuation.create () in
  let toplevel_my_region = Variable.create "toplevel_my_region" in
  (* FIXME: Need to use renaming here? *)
  let _mk_renaming u =
    let renaming = Renaming.empty in
    let renaming =
      Renaming.add_fresh_continuation renaming
        (Flambda_unit.return_continuation u)
        ~guaranteed_fresh:ret_cont
    in
    let renaming =
      Renaming.add_fresh_continuation renaming
        (Flambda_unit.exn_continuation u)
        ~guaranteed_fresh:exn_cont
    in
    let renaming =
      Renaming.add_fresh_variable renaming
        (Flambda_unit.toplevel_my_region u)
        ~guaranteed_fresh:toplevel_my_region
    in
    renaming
  in
  let src_core = flambda_unit_to_core src in
  let tgt_core = simplify_result_to_core tgt in
  core_eq src_core tgt_core
