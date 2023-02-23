open! Flambda
open! Flambda2_core

module P = Flambda_primitive

(** Translation from flambda2 terms to simplified core language **)
let simple_to_core (v : Simple.t) : core_exp = Named (Simple v)

let tagged_immediate_to_core (e : Targetint_31_63.t) : core_exp =
  Named (Simple (Simple.const (Int_ids.Const.tagged_immediate e)))

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
  Core_let.create ~x:var
    ~e1:(Let_expr.defining_expr e |> named_to_core)
    ~e2:(flambda_expr_to_core body)

and named_to_core (e : Flambda.named) : core_exp =
  Named (
    match e with
    | Simple e -> Simple e
    | Prim (t, _) -> Prim (prim_to_core t)
    | Set_of_closures e -> Set_of_closures (set_of_closures_to_core e)
    | Static_consts e -> Static_consts (static_consts_to_core e)
    | Rec_info t -> Rec_info t)

and set_of_closures_to_core (e : Set_of_closures.t) : set_of_closures =
  let function_decls =
    Set_of_closures.function_decls e |> function_declarations_to_core
  in
  let value_slots =
    Set_of_closures.value_slots e |> value_slots_to_core in
  let alloc_mode = Set_of_closures.alloc_mode e in
  { function_decls; value_slots; alloc_mode }

and function_declarations_to_core (e : Function_declarations.t) : function_declarations =
  let funs =
    Function_declarations.funs e |>
    Function_slot.Map.map (fun x -> Id x) in
  let in_order =
    Function_declarations.funs_in_order e |>
    Function_slot.Lmap.map (fun x -> Id x)
  in
  { funs; in_order }

and value_slots_to_core
      (e : (Simple.t * Flambda_kind.With_subkind.t) Value_slot.Map.t) :
  (value_expr * Flambda_kind.With_subkind.t) Value_slot.Map.t =
    Value_slot.Map.map (fun (x, y) -> (Id x, y)) e

and prim_to_core (e : P.t) : primitive =
  match e with
  | Nullary v -> Nullary v
  | Unary (prim, arg) ->
    Unary (prim, Named (Simple arg))
  | Binary (prim, arg1, arg2) ->
    Binary (prim, Named (Simple arg1), Named (Simple arg2))
  | Ternary (prim, arg1, arg2, arg3) ->
    Ternary (prim, Named (Simple arg1), Named (Simple arg2), Named (Simple arg3))
  | Variadic (prim, args) ->
    Variadic (prim, List.map (fun x -> Named (Simple x)) args)

and static_consts_to_core (e : Flambda.static_const_group) :
  Flambda2_core.static_const_group =
  Static_const_group.to_list e |> List.map static_const_or_code_to_core

and static_const_or_code_to_core (e : Flambda.static_const_or_code) :
  Flambda2_core.static_const_or_code =
  match e with
  | Code e -> Code
                (Code0.params_and_body e |>
                 function_params_and_body_to_core)
  | Deleted_code -> Deleted_code
  | Static_const t -> Static_const (static_const_to_core t)

and static_const_to_core (e : Static_const.t) : Flambda2_core.static_const =
  match e with
  | Set_of_closures soc ->
    Static_set_of_closures (set_of_closures_to_core soc)
  | Block (tag, mut, list) ->
    let list = List.map field_of_static_block_to_core list in
    Block (tag, mut, list)
  | Boxed_float v -> Boxed_float v
  | Boxed_int32 v -> Boxed_int32 v
  | Boxed_int64 v -> Boxed_int64 v
  | Boxed_nativeint v -> Boxed_nativeint v
  | Immutable_float_block v -> Immutable_float_block v
  | Immutable_float_array v -> Immutable_float_array v
  | Immutable_value_array v -> Immutable_value_array v
  | Empty_array -> Empty_array
  | Mutable_string {initial_value} -> Mutable_string {initial_value}
  | Immutable_string s -> Immutable_string s

and field_of_static_block_to_core (e : Field_of_static_block.t) : core_exp =
  match e with
  | Symbol e ->
    Named (Simple (Simple.symbol e))
  | Tagged_immediate e -> tagged_immediate_to_core e
  | Dynamically_computed (var, _) ->
    Named (Simple (Simple.var var))

and function_params_and_body_to_core (t : Flambda.function_params_and_body) :
  Flambda2_core.function_params_and_body =
  Function_params_and_body.pattern_match' t
    ~f:(fun (bound: Bound_for_function.t) ~body ->
      Core_function_params_and_body.create bound (flambda_expr_to_core body))

and let_cont_to_core (e : Let_cont_expr.t) : core_exp =
  match e with
  | Non_recursive
      {handler = h; num_free_occurrences = _; is_applied_with_traps = _} ->
    let (contvar, scoped_body) =
      Non_recursive_let_cont_handler.pattern_match
        h ~f:(fun contvar ~body -> (contvar, body)) in
    Let_cont (Non_recursive {
      handler =
        Non_recursive_let_cont_handler.handler h |> cont_handler_to_core;
      body = flambda_expr_to_core scoped_body |>
        Core_letcont_body.create contvar;})

  | Recursive r ->
    let (bound, params, body, handler) = Recursive_let_cont_handlers.pattern_match_bound
      r ~f:(fun bound ~invariant_params ~body t -> (bound, invariant_params, body, t)) in
    Let_cont
      (Recursive (Core_recursive.create bound
        {continuation_map =
            Core_continuation_map.create params (cont_handlers_to_core handler);
         body = flambda_expr_to_core body;}))

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
    continuation = Id (Apply_expr.continuation e);
    exn_continuation = Id (Apply_expr.exn_continuation e |>
                        Exn_continuation.exn_handler);
    apply_args = Apply_expr.args e |> List.map simple_to_core;
    call_kind = Apply_expr.call_kind e;}

and apply_cont_to_core (e : Apply_cont.t) : core_exp =
  Apply_cont {
    k = Apply_cont_expr.continuation e;
    args = Apply_cont_expr.args e |> List.map simple_to_core;}

and switch_to_core (e : Switch.t) : core_exp =
  Switch {
    scrutinee = Switch_expr.scrutinee e |> simple_to_core;
    arms = Switch_expr.arms e |> Targetint_31_63.Map.map apply_cont_to_core;}

let flambda_unit_to_core e : core_exp =
  Flambda_unit.body e |> flambda_expr_to_core
