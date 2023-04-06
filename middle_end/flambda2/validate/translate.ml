open! Flambda
open! Flambda2_core

module P = Flambda_primitive

module Sub = Map.Make (Simple)
type substitutions = core_exp Sub.t

(** Translation from flambda2 terms to simplified core language **)
let simple_to_core (v : Simple.t) : core_exp =
  Expr.create_named
    (Literal (Simple (Simple.without_coercion v)))

let tagged_immediate_to_core (e : Targetint_31_63.t) : core_exp =
  Expr.create_named
     (Literal (Simple (Simple.const (Int_ids.Const.tagged_immediate e))))

let apply_subst (s : substitutions) (e : core_exp) : core_exp =
  core_fmap (fun () v ->
    match v with
    | Simple v ->
      (match Sub.find_opt v s with
       | Some exp -> exp
       | None -> Expr.create_named (Literal (Simple v)))
    | (Cont _ | Res_cont _ | Slot _ | Code_id _) -> Expr.create_named (Literal v))
    () e

let subst_var_slot
      (vars : Bound_var.t list) (phi : Bound_var.t)
      (e : core_exp) (s : substitutions) =
  match descr e with
  | Named (Set_of_closures {function_decls ; value_slots = _}) ->
    let in_order = Function_slot.Lmap.bindings function_decls
    in
    List.fold_left
      (fun s(var, (slot, _)) ->
         (Sub.add (Simple.var (Bound_var.var var))
          (Expr.create_named (Literal (Slot (Bound_var.var phi, Function_slot slot)))) s)) s
      (List.combine vars in_order)
  | (Named (Literal _ | Prim _ | Closure_expr _ | Static_consts _ | Rec_info _) |
     Let _ | Let_cont _ | Apply _ | Apply_cont _ | Lambda _ | Handler _ | Switch _
    | Invalid _ ) ->
    Misc.fatal_error "Expected set of closures"

let subst_static_slot
      (bound : Symbol.t Function_slot.Lmap.t)
      (phi : Bound_var.t) (s : substitutions) : substitutions =
  let bound = Function_slot.Lmap.bindings bound in
  List.fold_left
    (fun s (slot, sym) ->
      (Sub.add (Simple.symbol sym)
        (Expr.create_named (Literal (Slot (Bound_var.var phi, Function_slot slot)))) s)) s bound

let bound_static_to_core (t : Bound_static.Pattern.t) (s : substitutions) :
  Bound_codelike.Pattern.t * substitutions =
  match t with
  | Set_of_closures bound ->
    let phi = Bound_var.create (Variable.create "ϕ") Name_mode.normal in
    (* substitutionsstitute in new variable *)
    let s = subst_static_slot bound phi s in
    (Bound_codelike.Pattern.set_of_closures phi, s)
  | Code v -> (Bound_codelike.Pattern.code v, s)
  | Block_like v -> (Bound_codelike.Pattern.block_like v, s)

let bound_pattern_to_core (t : Bound_pattern.t) (e : core_exp) (s : substitutions):
  Bound_for_let.t * core_exp * substitutions =
  match t with
  | Singleton v -> (Singleton v, e, s)
  | Set_of_closures vars ->
    let phi = Bound_var.create (Variable.create "ϕ") Name_mode.normal
    in
    let s = subst_var_slot vars phi e s in
    (Singleton phi, e, s)
  | Static static ->
    let static, s =
      List.fold_left
        (fun (pat_acc, s) x ->
           let pat, s = bound_static_to_core x s in
           (pat_acc @ [pat], s))
        ([], s)
        (Bound_static.to_list static)
    in
    (Static (Bound_codelike.create static), e, s)

let rec flambda_expr_to_core (e: expr) (s : substitutions) :
  core_exp * substitutions =
  let e = Flambda.Expr.descr e in
  match e with
  | Flambda.Let t -> let_to_core t s
  | Flambda.Let_cont t -> let_cont_to_core t s
  | Flambda.Apply t -> apply_to_core t s
  | Flambda.Apply_cont t -> apply_cont_to_core t s
  | Flambda.Switch t -> switch_to_core t s
  | Flambda.Invalid { message = t } ->
    (Expr.create_invalid t, s)

(* N.B. There is a new binder for [set_of_closures] in the core expression
   language. *)
and let_to_core (e : Let_expr.t) (s : substitutions) :
  core_exp * substitutions =
  Let_expr.pattern_match e
    ~f:(fun var ~body ->
      (* The bound variable, [var], is being passed around for checking whether
         if when a [code_id] is bound, it is an anonymous function (i.e. whether
         the prefix starts with [anon-fn]) *)
      let e1 = Let_expr.defining_expr e |> named_to_core var in
      let x, e1, s = bound_pattern_to_core var e1 s in
      let e2, s = flambda_expr_to_core body s in
      let e2 = apply_subst s e2 in
      (Core_let.create ~x ~e1 ~e2, s))

and named_to_core var (e : Flambda.named) : core_exp =
  Expr.create_named (
    match e with
    | Simple e -> Literal (Simple e)
    | Prim (t, _) -> Prim (prim_to_core t)
    | Set_of_closures e -> Set_of_closures (set_of_closures_to_core e)
    | Static_consts e -> Static_consts (static_consts_to_core var e)
    | Rec_info t -> Rec_info t)

and set_of_closures_to_core (e : Set_of_closures.t) : set_of_closures =
  let function_decls =
    Set_of_closures.function_decls e |> function_declarations_to_core
  in
  let value_slots =
    Set_of_closures.value_slots e |> value_slots_to_core in
  { function_decls; value_slots }

and function_declarations_to_core (e : Function_declarations.t) : function_declarations =
  Function_declarations.funs_in_order e |>
  Function_slot.Lmap.map (fun x -> Expr.create_named (Literal (Code_id x)))

and value_slots_to_core
      (e : (Simple.t) Value_slot.Map.t) : core_exp Value_slot.Map.t =
    Value_slot.Map.map (fun x -> Expr.create_named (Literal (Simple (Simple.without_coercion x)))) e

and prim_to_core (e : P.t) : primitive =
  match e with
  | Nullary v -> Nullary v
  | Unary (prim, arg) ->
    Unary (prim, Expr.create_named (Literal (Simple arg)))
  | Binary (prim, arg1, arg2) ->
    Binary (prim, Expr.create_named (Literal (Simple arg1)), Expr.create_named (Literal (Simple arg2)))
  | Ternary (prim, arg1, arg2, arg3) ->
    Ternary (prim, Expr.create_named (Literal (Simple arg1)),
             Expr.create_named (Literal (Simple arg2)),
             Expr.create_named (Literal (Simple arg3)))
  | Variadic (prim, args) ->
    Variadic (prim,
              List.map (fun x -> Expr.create_named (Literal (Simple x))) args)

and static_consts_to_core var (e : Flambda.static_const_group) :
  Flambda2_core.static_const_group =
  let static_consts = Static_const_group.to_list e
  in
  let bound_consts = Bound_static.to_list (Bound_pattern.must_be_static var)
  in
  List.map (fun (bound, const) ->
    static_const_or_code_to_core bound const)
    (List.combine bound_consts static_consts)

and static_const_or_code_to_core
      var
      (e : Flambda.static_const_or_code):
  Flambda2_core.static_const_or_code =
  match e with
  | Code e ->
    Code (Code0.params_and_body e |>
          function_params_and_body_to_core var)
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
    Expr.create_named (Literal (Simple (Simple.symbol e)))
  | Tagged_immediate e -> tagged_immediate_to_core e
  | Dynamically_computed (var, _) ->
    Expr.create_named (Literal (Simple (Simple.var var)))

and function_params_and_body_to_core
      (var : Bound_static.Pattern.t)
      (t : Flambda.function_params_and_body):
  Flambda2_core.function_params_and_body =
  let name =
    (match var with
     | Code id -> id
     | (Set_of_closures _ | Block_like _) -> Misc.fatal_error "Expected code id")
  in
  let anon =
    String.starts_with ~prefix:"anon-fn[" (Code_id.name name)
  in
  { expr =
      Function_params_and_body.pattern_match' t
        ~f:(fun (bound: Bound_for_function.t) ~body ->
          let my_closure = Bound_for_function.my_closure bound
          in
          let body, _ = flambda_expr_to_core body Sub.empty in
          Core_function_params_and_body.create
            (Bound_var.create my_closure Name_mode.normal)
            (Core_lambda.create
              (Bound_for_lambda.create
                  ~return_continuation:
                    (Bound_for_function.return_continuation bound)
                  ~exn_continuation:
                    (Bound_for_function.exn_continuation bound)
                  ~params:
                    (Bound_for_function.params bound)
                  ~my_region:
                    (Bound_for_function.my_region bound))
              body)
        );
    anon}

(* Accumulate substitutions in both the body and the handler, and substitute in
  the bindings for the whole expression. *)
and let_cont_to_core (e : Let_cont_expr.t) (sub : substitutions) :
  core_exp * substitutions =
  match e with
  | Non_recursive
      {handler = h; num_free_occurrences = _; is_applied_with_traps = _} ->
    Non_recursive_let_cont_handler.pattern_match h
      ~f:(fun contvar ~body ->
        let body, s = flambda_expr_to_core body sub in
        let handler, s =
          cont_handler_to_core
            (Non_recursive_let_cont_handler.handler h) s
        in
        let handler =
          Core_continuation_handler.pattern_match handler
             (fun var handler ->
                 Core_continuation_handler.create var handler)
        in
        let body = Core_letcont_body.create contvar body in
        let exp = Core_letcont.create_non_recursive handler ~body in
        (exp, s))
  | Recursive r ->
    Recursive_let_cont_handlers.pattern_match_bound r
      ~f:
        (fun bound ~invariant_params ~body handler ->
           let body, _ = flambda_expr_to_core body sub in
           let body =
             {continuation_map =
                Core_continuation_map.create invariant_params
                  (cont_handlers_to_core handler sub);
              body}
           in
           let exp = Core_letcont.create_recursive bound body in
           (exp, sub)
        )

and cont_handler_to_core
      (e : Continuation_handler.t) (s : substitutions)
  : continuation_handler * substitutions =
  Continuation_handler.pattern_match e
    ~f:
      (fun var ~handler ->
         let handler, s = flambda_expr_to_core handler s in
         (Core_continuation_handler.create var handler, s))

and cont_handlers_to_core (e : Continuation_handlers.t) (s : substitutions) :
  continuation_handler Continuation.Map.t =
  let e : Continuation_handler.t Continuation.Map.t =
    Continuation_handlers.to_map e in
  Continuation.Map.map
    (fun e ->
       let e, _ = cont_handler_to_core e s in e) e

and apply_to_core (e : Apply.t) (s : substitutions)
  : core_exp * substitutions =
  let e =
    Expr.create_apply {
      callee = Apply_expr.callee e |> simple_to_core;
      continuation = Expr.create_named (Literal (Res_cont (Apply_expr.continuation e)));
      exn_continuation = Expr.create_named (Literal (Cont (Apply_expr.exn_continuation e |>
                                               Exn_continuation.exn_handler)));
      region = Expr.create_named (Literal (Simple (Simple.var (Apply_expr.region e))));
      apply_args = Apply_expr.args e |> List.map simple_to_core }
  in
  e, s

and apply_cont_to_core (e : Apply_cont.t) (s : substitutions)
  : core_exp * substitutions =
  let e =
    Expr.create_apply_cont {
      k = Expr.create_named (Literal (Cont (Apply_cont_expr.continuation e)));
      args = Apply_cont_expr.args e |> List.map simple_to_core;}
  in
  e, s

and switch_to_core (e : Switch.t) (s : substitutions)
  : core_exp * substitutions =
  let e =
    Expr.create_switch {
      scrutinee = Switch_expr.scrutinee e |> simple_to_core;
      arms = Switch_expr.arms e |>
             Targetint_31_63.Map.map
               (fun x -> let e, _ = apply_cont_to_core x s in e)
      ;}
  in
  e, s

let flambda_unit_to_core e : core_exp =
  let e, _ = flambda_expr_to_core (Flambda_unit.body e) Sub.empty in e
