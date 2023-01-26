open! Flambda

(* Simplified core of [flambda2] terms *)
type core_exp =
  | Let of let_expr
  | Let_cont of let_cont_expr
  | Apply of apply_expr
  | Apply_cont of apply_cont_expr
  | Switch of Switch.t
  | Invalid of { message : string }

and let_expr = Bound_pattern.t * core_exp

and let_cont_expr =
  (* Non-recursive case [let k x = e1 in e2]

     [fun x -> e1] = continuation_handler
     bound variable [k] = bound_cont
     [e2] = body (has bound variable [k] in scope) *)
  | Non_recursive of
    { continuation_handler : Bound_parameters.t * core_exp;
      letbound_contvar : Bound_continuation.t;
      body : core_exp; }

  (* Recursive case, we have a set of (mutually recursive) continuations
     [let rec K x in e] where [K] is a map of continuations
     [x] is the set of invariant parameters
     bound variable [K] is in the scope of [e]

     [x] = invariant_params
     [K] = continuation_map
     [e] = body *)
  | Recursive of
    { invariant_params : Bound_parameters.t;
      continuation_map : (Bound_parameters.t * core_exp) Continuation.Map.t;
      body : core_exp; }

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
  { scrutinee : Simple.t;
    arms : Apply_cont_expr.t Targetint_31_63.Map.t }

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
  | Let_cont _, Let_cont _ ->
    (* [Continuation.t] is the names of the continuations, so this equality check
       checks for [id] equality *)
    (* Continuation.equal cont1 cont2 && *)
    (* Add bound variables to context, continuation id to closure context *)
    (* core_eq_ctx (bound1::ctx1) (bound2::ctx2) (cont1::clo1) (cont2::clo2) body1 body2 *)
    failwith "Unimplemented"
  | Apply { callee = callee1;
            continuation = cont1;
            exn_continuation = exn_cont1;
            args = args1;
            call_kind = kind1 },
    Apply { callee = callee2;
            continuation = cont2;
            exn_continuation = exn_cont2;
            args = args2;
            call_kind = kind2 } ->
    failwith "Unimplemented"
  | Apply_cont _, Apply_cont _ ->
    failwith "Unimplemented"
  | Switch _, Switch _ ->
    failwith "Unimplemented"
  | Invalid _, Invalid _ ->
    failwith "Unimplemented"

let core_eq = core_eq_ctx [] [] [] []

let simple_to_core (v : Simple.t) : core_exp =
  failwith "Unimplemented"

let rec flambda_expr_to_core (e: expr) : core_exp =
  let e = Expr.descr e in
  match e with
  | Flambda.Let e -> Let_expr.pattern_match e ~f:(let_to_core)
  | Flambda.Let_cont e -> let_cont_to_core e
  | Flambda.Apply t -> apply_to_core t
  | Flambda.Apply_cont t -> apply_cont_to_core t
  | Flambda.Switch t -> switch_to_core t
  | Flambda.Invalid { message = t } -> Invalid { message = t }

and let_to_core (var : Bound_pattern.t) ~body : core_exp =
  Let (var, flambda_expr_to_core body)

and let_cont_to_core (e : Let_cont_expr.t) : core_exp =
  match e with
  | Non_recursive
      {handler = h; num_free_occurrences; is_applied_with_traps} ->
    let (contvar, scoped_body) =
      Non_recursive_let_cont_handler.pattern_match
        h ~f:(fun contvar ~body -> (contvar, body)) in
    let cont_handler =
      Non_recursive_let_cont_handler.handler h |> cont_handler_to_core in
    Let_cont (Non_recursive {
      continuation_handler = cont_handler;
      letbound_contvar = contvar;
      body = flambda_expr_to_core scoped_body;})

  | Recursive r ->
    let (params, body, handler) = Recursive_let_cont_handlers.pattern_match
      r ~f:(fun ~invariant_params ~body t -> (invariant_params, body, t))in
    Let_cont (Recursive {
      invariant_params = params;
      continuation_map = cont_handlers_to_core handler;
      body = flambda_expr_to_core body;})

and cont_handler_to_core (e : Continuation_handler.t) :
    Bound_parameters.t * core_exp =
  let (var, handler) =
    Continuation_handler.pattern_match e ~f:(fun var ~handler -> (var, handler)) in
  (var, flambda_expr_to_core handler)

and cont_handlers_to_core (e : Continuation_handlers.t) :
  (Bound_parameters.t * core_exp) Continuation.Map.t =
  let e : Continuation_handler.t Continuation.Map.t =
    Continuation_handlers.to_map e in
  Continuation.Map.map cont_handler_to_core e

and apply_to_core (e : Apply.t) : core_exp =
  Apply { callee = Apply_expr.callee e |> simple_to_core;
          continuation = Apply_expr.continuation e;
          exn_continuation = Apply_expr.exn_continuation e |>
                             Exn_continuation.exn_handler;
          args = Apply_expr.args e |> List.map simple_to_core;
          call_kind = Apply_expr.call_kind e;}

and apply_cont_to_core (e : Apply_cont.t) : core_exp =
  failwith "Unimplemented"

and switch_to_core (e : Switch.t) : core_exp =
  failwith "Unimplemented"

(* TODO *)
let normalize = failwith "Unimplemented"

let simplify_result_to_core _e = failwith "Unimplemented"

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
