open! Flambda

(* Simplified core of [flambda2] terms *)
(* (1) Simple.t -> core_exp for [Apply*] expressions
   (2) Ignore [Num_occurrences] (which is used for making inlining decisions)
   (3) Ignored traps for now *)

type core_exp =
  | Var of Simple.t
  | Let of let_expr
  | Let_cont of let_cont_expr
  | Apply of apply_expr
  | Apply_cont of apply_cont_expr
  | Switch of switch_expr
  | Invalid of { message : string }

(* [let x = e1 in e]

   [fun x -> e] = let_abst
   [e1] = body *)
and let_expr =
  { let_abst : (Bound_pattern.t, core_exp) Name_abstraction.t;
    body : Flambda.named; }

and let_cont_expr =
  (* Non-recursive case [let k x = e1 in e2]

     [fun x -> e1] = handler
     bound variable [k] = Bound_continuation.t
     [e2] = body (has bound variable [k] in scope) *)
  | Non_recursive of
    { handler : continuation_handler;
      body : (Bound_continuation.t, core_exp) Name_abstraction.t;}

  (* Recursive case, we have a set of (mutually recursive) continuations
     [let rec K x in e] where [K] is a map of continuations
     [x] is the set of invariant parameters
     bound variable [K] is in the scope of [e]

     [x] = invariant_params (Bound_parameters.t)
     [K] = continuation_map
     [e] = body *)
  | Recursive of
    { continuation_map :
        (Bound_parameters.t, continuation_handler_map) Name_abstraction.t;
      body : core_exp; }

and continuation_handler =
  (Bound_parameters.t, core_exp) Name_abstraction.t

and continuation_handler_map =
  continuation_handler Continuation.Map.t

and apply_expr =
  { callee: core_exp;
    continuation: Apply_expr.Result_continuation.t;
    exn_continuation: Continuation.t;
    args: core_exp list;
    call_kind: Call_kind.t; }

and apply_cont_expr =
  { k : Continuation.t;
    args : core_exp list }

and switch_expr =
  { scrutinee : core_exp;
    arms : core_exp Targetint_31_63.Map.t }

let apply_renaming_core_exp = failwith "Unimplemented"
let ids_for_export_core_exp = failwith "Unimplemented"
let apply_renaming_cont_map = failwith "Unimplemented"
let ids_for_export_cont_map = failwith "Unimplemented"

module T0 = struct
  type t = core_exp
  let apply_renaming = apply_renaming_core_exp
  let ids_for_export = ids_for_export_core_exp
end

module ContMap = struct
  type t = continuation_handler_map
  let apply_renaming = apply_renaming_cont_map
  let ids_for_export = ids_for_export_cont_map
end

module Core_let = struct
  module A = Name_abstraction.Make (Bound_pattern) (T0)
  let create (bound_pattern : Bound_pattern.t) (defining_expr : named) body =
    (match defining_expr, bound_pattern with
    | Prim _, Singleton _
    | Simple _, Singleton _
    | Rec_info _, Singleton _
    | Set_of_closures _, Set_of_closures _ -> ()
    | _ , _ -> failwith "[Let.create] Mismatched bound pattern and defining expr");
    Let { let_abst = A.create bound_pattern body; body = defining_expr }
end

module Core_continuation_handler = struct
  module A = Name_abstraction.Make (Bound_parameters) (T0)
  let create = A.create
end

module Core_letrec_body = struct
  module A = Name_abstraction.Make (Bound_continuation) (T0)
  let create = A.create
end

module Core_continuation_map = struct
  module A = Name_abstraction.Make (Bound_parameters) (ContMap)
  let create = A.create
end

(* Translation *)
let simple_to_core (v : Simple.t) : core_exp = Var v

let rec flambda_expr_to_core (e: expr) : core_exp =
  let e = Expr.descr e in
  match e with
  | Flambda.Let t -> let_to_core t
  | Flambda.Let_cont t -> let_cont_to_core t
  | Flambda.Apply t -> apply_to_core t
  | Flambda.Apply_cont t -> apply_cont_to_core t
  | Flambda.Switch t -> switch_to_core t
  | Flambda.Invalid { message = t } -> Invalid { message = t }

and let_to_core (e : Let_expr.t) : core_exp =
  let (var, body) = Let_expr.pattern_match e ~f:(fun var ~body -> (var, body)) in
  Core_let.create var (Let_expr.defining_expr e) (flambda_expr_to_core body)

and let_cont_to_core (e : Let_cont_expr.t) : core_exp =
  match e with
  | Non_recursive
      {handler = h; num_free_occurrences; is_applied_with_traps} ->
    let (contvar, scoped_body) =
      Non_recursive_let_cont_handler.pattern_match
        h ~f:(fun contvar ~body -> (contvar, body)) in
    Let_cont (Non_recursive {
      handler =
        Non_recursive_let_cont_handler.handler h |> cont_handler_to_core;
      body = flambda_expr_to_core scoped_body |>
        Core_letrec_body.create contvar;})

  | Recursive r ->
    let (params, body, handler) = Recursive_let_cont_handlers.pattern_match
      r ~f:(fun ~invariant_params ~body t -> (invariant_params, body, t))in
    Let_cont (Recursive {
      continuation_map =
        Core_continuation_map.create params (cont_handlers_to_core handler);
      body = flambda_expr_to_core body;})

and cont_handler_to_core (e : Continuation_handler.t) : continuation_handler =
  let (var, handler) =
    Continuation_handler.pattern_match e ~f:(fun var ~handler -> (var, handler)) in
  Core_continuation_handler.create var (flambda_expr_to_core handler)

and cont_handlers_to_core (e : Continuation_handlers.t) :
  continuation_handler Continuation.Map.t =
  let e : Continuation_handler.t Continuation.Map.t =
    Continuation_handlers.to_map e in
  Continuation.Map.map cont_handler_to_core e

and apply_to_core (e : Apply.t) : core_exp =
  Apply {
    callee = Apply_expr.callee e |> simple_to_core;
    continuation = Apply_expr.continuation e;
    exn_continuation = Apply_expr.exn_continuation e |>
                        Exn_continuation.exn_handler;
    args = Apply_expr.args e |> List.map simple_to_core;
    call_kind = Apply_expr.call_kind e;}

and apply_cont_to_core (e : Apply_cont.t) : core_exp =
  Apply_cont {
    k = Apply_cont_expr.continuation e;
    args = Apply_cont_expr.args e |> List.map simple_to_core;}

and switch_to_core (e : Switch.t) : core_exp =
  Switch {
    scrutinee = Switch_expr.scrutinee e |> simple_to_core;
    arms = Switch_expr.arms e |> Targetint_31_63.Map.map apply_cont_to_core;}

(* The most naive equality type, a boolean *)
type eq = bool

(* Simple program context *)
module Env = struct
  type t = Bound_pattern.t list (* FIXME *)
  let create () = []
end

let rec normalize (e:core_exp) : core_exp =
  match e with
  | Var _ -> e
  | Let e -> failwith "Unimplemented"
  | Let_cont _ -> failwith "Unimplemented"
  | Apply _ -> failwith "Unimplemented"
  | Apply_cont _ -> failwith "Unimplemented"
  | Switch _ -> failwith "Unimplemented"
  | Invalid _ -> failwith "Unimplemented"

(* Equality between two programs given a context *)
let rec core_eq_ctx (e:Env.t) e1 e2 : eq =
  match e1, e2 with
  | Let _, Let _ -> failwith "Unimplemented"
  | Let_cont _, Let_cont _ -> failwith "Unimplemented"
  | Apply _, Apply _ -> failwith "Unimplemented"
  | Apply_cont _, Apply_cont _ -> failwith "Unimplemented"
  | Switch _, Switch _ -> failwith "Unimplemented"
  | Invalid _, Invalid _ -> failwith "Unimplemented"

let core_eq = Env.create () |> core_eq_ctx

let simulation_relation src tgt =
  let {Simplify.unit = tgt; exported_offsets; cmx; all_code} = tgt in
  let src_core = Flambda_unit.body src |> flambda_expr_to_core in
  let tgt_core = Flambda_unit.body tgt |> flambda_expr_to_core in
  core_eq src_core tgt_core

let validate ~cmx_loader ~round src =
  let tgt = Simplify.run ~cmx_loader ~round src in
  simulation_relation src tgt
