open! Flambda

module Result_continuation = struct
  type t = Continuation.t
end

module Exn_continuation = struct
  type t = Continuation.t
end

(* FIXME: Substitute [Simple.t] to [core_exp] *)
module Apply = struct
  type t =
    { callee: Simple.t;
      continuation: Result_continuation.t;
      exn_continuation: Exn_continuation.t;
      args: Simple.t list;
      call_kind: Call_kind.t; }
end

module Apply_cont = struct
  type t =
    { k : Continuation.t;
      args : Simple.t list }
end

module Switch = struct
  type t =
    { scrutinee : Simple.t;
      arms : Apply_cont_expr.t Targetint_31_63.Map.t }
end

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
(* [let k x = e1 in e2]
   e1 = continuation
   k = bound
   body = e2 *)
and let_cont_expr =
  { continuation : Continuation.t; (* FIXME : add code for continuation *)
    bound : Bound_pattern.t;
    body : core_exp; }

(* The most naive equality type, a boolean *)
type eq = bool

(* Simple program context *)
type context = Bound_pattern.t list

(* Closure context, keeping track of the continuation id's *)
type closure_context = Continuation.t list

let rec core_eq_ctx (ctx1:context) (ctx2:context) clo1 clo2 e1 e2 : eq =
  match e1, e2 with
  | Let (b1, e1), Let (b2, e2) ->
    (* Add bound variables to context *)
    core_eq_ctx (b1::ctx1) (b2::ctx2) clo1 clo2 e1 e2
  | Let_cont {continuation = cont1; bound = bound1; body = body1},
    Let_cont {continuation = cont2; bound = bound2; body = body2} ->
    (* [Continuation.t] is the names of the continuations, so this equality check
       checks for [id] equality *)
    Continuation.equal cont1 cont2 &&
    (* Add bound variables to context, continuation id to closure context *)
    core_eq_ctx (bound1::ctx1) (bound2::ctx2) (cont1::clo1) (cont2::clo2) body1 body2
  | Apply { callee = callee1;
            continuation = cont1;
            exn_continuation = exn_cont1;
            args = args1;
            call_kind = kind1 },
    Apply { callee = callee2;
            continuation = cont2;
            exn_continuation = exn_cont2;
            args = args2;
            call_kind = kind2 } -> false
  | Apply_cont _, Apply_cont _ ->
    false
  | Switch _, Switch _ ->
    false
  | Invalid _, Invalid _ -> true

let core_eq = core_eq_ctx [] [] [] []

let rec flambda_expr_to_core (e: expr) : core_exp =
  let e = Expr.descr e in
  match e with
  | Flambda.Let e ->
    Let_expr.pattern_match e ~f:(let_to_core)
  | Flambda.Let_cont e ->
    let_cont_to_core e
  | Flambda.Apply t ->
    Invalid { message = "unimplemented" }
  | Flambda.Apply_cont t ->
    Invalid { message = "unimplemented" }
  | Flambda.Switch t ->
    Invalid { message = "unimplemented" }
  | Flambda.Invalid { message = t }->
    Invalid { message = t }

and let_to_core (var : Bound_pattern.t) ~body : core_exp =
  Let (var, flambda_expr_to_core body)

and let_cont_to_core (e : Let_cont_expr.t) : core_exp =
  match e with
  | Non_recursive
      {handler = h; num_free_occurrences = n; is_applied_with_traps = b} ->
    Invalid { message = "unimplemented" }
  | Recursive r ->
    Recursive_let_cont_handlers.pattern_match
      r ~f:recursive_let_cont_handler_to_core

and recursive_let_cont_handler_to_core ~invariant_params ~body t : core_exp =
  Invalid { message = "unimplemented" }

(* TODO *)
let normalize = fun x -> x

let simplify_result_to_core _e =
  Invalid { message = "unimplemented" }

let validate src tgt =
  let ret_cont = Continuation.create ~sort:Toplevel_return () in
  let exn_cont = Continuation.create () in
  let toplevel_my_region = Variable.create "toplevel_my_region" in
  let mk_renaming u =
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
  let src_body = Expr.apply_renaming (Flambda_unit.body src) (mk_renaming src) in
  (* let tgt_body = Expr.apply_renaming (Flambda_unit.body tgt) (mk_renaming tgt) in *)
  let src_core = flambda_expr_to_core src_body in
  let tgt_core = simplify_result_to_core tgt in
  core_eq src_core tgt_core
