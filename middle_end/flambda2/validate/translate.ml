open! Flambda
open! Flambda2_core

module P = Flambda_primitive

type substitutions = (Simple.t * core_exp) list

(** Translation from flambda2 terms to simplified core language **)
let simple_to_core (s : substitutions) (v : Simple.t) : core_exp =
  let simple = (Simple.without_coercion v) in
  match List.assoc_opt simple s with
  | Some exp -> exp
  | None -> Named (Literal (Simple simple))

let tagged_immediate_to_core (e : Targetint_31_63.t) : core_exp =
  Named (Literal (Simple (Simple.const (Int_ids.Const.tagged_immediate e))))

let apply_subst (s : substitutions) (e : core_exp) : core_exp =
  core_fmap (fun () v ->
    match v with
    | Simple v ->
      (match List.assoc_opt v s with
       | Some exp -> exp
       | None -> Named (Literal (Simple v)))
    | (Cont _ | Res_cont _ | Slot _ | Code_id _) -> Named (Literal v))
    () e

let subst_var_slot_helper
          (var : Bound_var.t) (phi : Bound_var.t) (slot : slot) (e2 : core_exp) =
  core_fmap
    (fun (var, phi, slot) v ->
       match v with
       | Simple v ->
          (if (Simple.same (Simple.var (Bound_var.var var)) v) then
            Named (Literal (Slot (Bound_var.var phi, slot)))
           else Named (Literal (Simple v)))
       | (Cont _ | Res_cont _ | Slot _ | Code_id _) -> Named (Literal v))
    (var, phi, slot) e2

let subst_var_slot
      (vars : Bound_var.t list) (phi : Bound_var.t)
      (e1 : core_exp) (e2 : core_exp)
      (s : substitutions) =
  match e1 with
  | Named (Set_of_closures {function_decls ; value_slots = _}) ->
    let in_order = Function_slot.Lmap.bindings function_decls
    in
    List.fold_left
      (fun (s, acc) (var, (slot, _)) ->
         ((Simple.var (Bound_var.var var),
          Named (Literal (Slot (Bound_var.var phi, Function_slot slot))))::s,
         subst_var_slot_helper var phi (Function_slot slot) acc))
      (s, e2)
      (List.combine vars in_order)
  | (Named (Literal _ | Prim _ | Closure_expr _ | Static_consts _ | Rec_info _) |
     Let _ | Let_cont _ | Apply _ | Apply_cont _ | Lambda _ | Handler _ | Switch _
    | Invalid _ ) ->
    Misc.fatal_error "Expected set of closures"

(* TODO :
   Change substitution helper functions to take general substitutions *)
let subst_static_slot_helper
      (sym : Symbol.t) (phi : Bound_var.t) (slot : slot) (e2 : core_exp) =
  core_fmap
    (fun (sym, phi, slot) v ->
      match v with
      | Simple v ->
        (if (Simple.same (Simple.symbol sym) v) then
          Named (Literal (Slot (Bound_var.var phi, slot)))
        else Named (Literal (Simple v)))
      | (Cont _ | Res_cont _ | Slot _ | Code_id _) -> Named (Literal v))
    (sym, phi, slot) e2

let subst_static_slot
      (bound : Symbol.t Function_slot.Lmap.t) (phi : Bound_var.t)
      (e2 : core_exp)
      (s : substitutions) =
  let bound = Function_slot.Lmap.bindings bound
  in
  let e2 = List.fold_left
    (fun (s, acc) (slot, sym) ->
      ((Simple.symbol sym,
        Named (Literal (Slot (Bound_var.var phi, Function_slot slot))))::s,
       subst_static_slot_helper sym phi (Function_slot slot) acc))
    (s, e2)
    bound
  in
  e2

let bound_static_to_core
      (t : Bound_static.Pattern.t)
      (e1 : core_exp) (e2 : core_exp)
      (s : substitutions) :
  Bound_codelike.Pattern.t * core_exp * core_exp * substitutions =
  match t with
  | Set_of_closures bound ->
    let phi = Bound_var.create (Variable.create "ϕ") Name_mode.normal
    in
    (* Substitute in new variable *)
    let s, exp1 = subst_static_slot bound phi e1 s
    in
    let s, exp2 = subst_static_slot bound phi e2 s
    in
    (Bound_codelike.Pattern.set_of_closures phi, exp1, exp2, s)
  | Code v -> (Bound_codelike.Pattern.code v, e1, e2, s)
  | Block_like v -> (Bound_codelike.Pattern.block_like v, e1, e2, s)

let bound_pattern_to_core
      (t : Bound_pattern.t)
      (e1 : core_exp) (e2 : core_exp)
      (s : substitutions):
  Bound_for_let.t * core_exp * core_exp * substitutions =
  match t with
  | Singleton v -> (Singleton v, e1, e2, s)
  | Set_of_closures vars ->
    let phi = Bound_var.create (Variable.create "ϕ") Name_mode.normal
    in
    (* Substitute in new variable *)
    let s, e2 = subst_var_slot vars phi e1 e2 s
    in
    (Singleton phi, e1, e2, s)
  | Static static ->
    let static, e1, e2, s =
      List.fold_left
        (fun (pat_acc1, acc1, acc2, s) x ->
           let pat, e1, e2, s = bound_static_to_core x acc1 acc2 s in
           (pat_acc1 @ [pat], e1, e2, s))
        ([], e1, e2, s)
        (Bound_static.to_list static)
    in
    (Static (Bound_codelike.create static), e1, e2, s)

let rec flambda_expr_to_core (e: expr) (s : substitutions) :
  core_exp * substitutions =
  let e = Expr.descr e in
  match e with
  | Flambda.Let t -> let_to_core t s
  | Flambda.Let_cont t -> let_cont_to_core t s
  | Flambda.Apply t -> apply_to_core t s
  | Flambda.Apply_cont t -> apply_cont_to_core t s
  | Flambda.Switch t -> switch_to_core t s
  | Flambda.Invalid { message = t } -> (Invalid { message = t }, s)

(* N.B. There is a new binder for [set_of_closures] in the core expression
   language. *)
and let_to_core (e : Let_expr.t) (s : substitutions) :
  core_exp * substitutions =
  Let_expr.pattern_match e
    ~f:(fun var ~body ->
      (* The bound variable, [var], is being passed around for checking whether
         if when a [code_id] is bound, it is an anonymous function (i.e. whether
         the prefix starts with [anon-fn]) *)
      let e1 = Let_expr.defining_expr e |> named_to_core var
      in
      let body, _ = flambda_expr_to_core body s in
      let x, e1, e2, s =
        bound_pattern_to_core var e1 body s
      in
      (Core_let.create ~x ~e1 ~e2, s))

and named_to_core var (e : Flambda.named) : core_exp =
  Named (match e with
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
  Function_slot.Lmap.map (fun x -> Named (Literal (Code_id x)))

and value_slots_to_core
      (e : (Simple.t) Value_slot.Map.t) : core_exp Value_slot.Map.t =
    Value_slot.Map.map (fun x -> Named (Literal (Simple (Simple.without_coercion x)))) e

and prim_to_core (e : P.t) : primitive =
  match e with
  | Nullary v -> Nullary v
  | Unary (prim, arg) ->
    Unary (prim, Named (Literal (Simple arg)))
  | Binary (prim, arg1, arg2) ->
    Binary (prim, Named (Literal (Simple arg1)), Named (Literal (Simple arg2)))
  | Ternary (prim, arg1, arg2, arg3) ->
    Ternary (prim, Named (Literal (Simple arg1)),
             Named (Literal (Simple arg2)),
             Named (Literal (Simple arg3)))
  | Variadic (prim, args) ->
    Variadic (prim,
              List.map (fun x -> Named (Literal (Simple x))) args)

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
    Named (Literal (Simple (Simple.symbol e)))
  | Tagged_immediate e -> tagged_immediate_to_core e
  | Dynamically_computed (var, _) ->
    Named (Literal (Simple (Simple.var var)))

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
          let body, _ = flambda_expr_to_core body [] in
          Core_function_params_and_body.create
            (Bound_var.create my_closure Name_mode.normal)
            (Core_lambda.create
              (Bound_for_lambda.create
                  ~return_continuation:
                    (Bound_for_function.return_continuation bound)
                  ~exn_continuation:
                    (Bound_for_function.exn_continuation bound)
                  ~params:
                    (Bound_for_function.params bound))
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
        (* apply substitutions in both body and handler *)
        let body = apply_subst s body in
        let handler =
          Core_continuation_handler.pattern_match handler
             (fun var handler ->
                 Core_continuation_handler.create var
                   (apply_subst s handler))
        in
        let exp =
          Let_cont (Non_recursive {handler;
            body = body |> Core_letcont_body.create contvar;})
        in
        (exp, s))

  | Recursive r ->
    Recursive_let_cont_handlers.pattern_match_bound r
      ~f:
        (fun bound ~invariant_params ~body handler ->
           let body, s = flambda_expr_to_core body sub in
           (Let_cont
             (Recursive
                (Core_recursive.create bound
                   {continuation_map =
                      Core_continuation_map.create invariant_params
                        (cont_handlers_to_core handler s);
                    body}
                )
             ), sub)
        )

and cont_handler_to_core
      (e : Continuation_handler.t) (s : substitutions)
  : continuation_handler * substitutions =
  Continuation_handler.pattern_match e
    ~f:
      (fun var ~handler ->
         let handler, s = flambda_expr_to_core handler s in
         (Core_continuation_handler.create var handler, s))

and cont_handlers_to_core (e : Continuation_handlers.t) (s : substitutions):
  continuation_handler Continuation.Map.t =
  let e : Continuation_handler.t Continuation.Map.t =
    Continuation_handlers.to_map e in
  Continuation.Map.map
    (fun e ->
       let e, _ = cont_handler_to_core e s in e) e

and apply_to_core (e : Apply.t) (s : substitutions)
  : core_exp * substitutions =
  let e =
    Apply {
      callee = Apply_expr.callee e |> simple_to_core s;
      continuation = Named (Literal (Res_cont (Apply_expr.continuation e)));
      exn_continuation = Named (Literal (Cont (Apply_expr.exn_continuation e |>
                          Exn_continuation.exn_handler)));
      apply_args = Apply_expr.args e |> List.map (simple_to_core s) }
  in
  e, s

and apply_cont_to_core (e : Apply_cont.t) (s : substitutions)
  : core_exp * substitutions =
  let e =
    Apply_cont {
      k = Named (Literal (Cont (Apply_cont_expr.continuation e)));
      args = Apply_cont_expr.args e |> List.map (simple_to_core s);}
  in
  e, s

and switch_to_core (e : Switch.t) (s : substitutions)
  : core_exp * substitutions =
  let e =
    Switch {
      scrutinee = Switch_expr.scrutinee e |> (simple_to_core s);
      arms = Switch_expr.arms e |>
             Targetint_31_63.Map.map
               (fun x ->
                   let e, _ = apply_cont_to_core x s in e)
      ;}
  in
  e, s

let flambda_unit_to_core e : core_exp =
  let e, _ = flambda_expr_to_core (Flambda_unit.body e) [] in e
