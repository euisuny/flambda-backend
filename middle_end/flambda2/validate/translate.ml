open! Flambda
open! Flambda2_core

module P = Flambda_primitive

(* The current compilation unit; initialized to dummy unit *)
let comp_unit : Compilation_unit.t ref =
  ref (Compilation_unit.create Compilation_unit.Prefix.empty
         Compilation_unit.Name.dummy)

(* Subsitutions from old function-pointer-based bindings for function slots to
   Phi-node closures *)
module Sub = Map.Make (Simple)
type substitutions = core_exp Sub.t

type env = substitutions

let create_env = Sub.empty

(** Translation from flambda2 terms to simplified core language **)
let simple_to_core (v : Simple.t) : core_exp =
  Expr.create_named
    (Literal (Simple (Simple.without_coercion v)))

let tagged_immediate_to_core (e : Targetint_31_63.t) : core_exp =
  Expr.create_named
     (Literal (Simple (Simple.const (Int_ids.Const.tagged_immediate e))))

let apply_subst (s : substitutions) (e : core_exp) : core_exp =
  core_fmap (fun () v ->
    match must_be_simple v with
    | Some v ->
      (match Sub.find_opt v s with
       | Some exp -> exp
       | None -> Expr.create_named (Literal (Simple v)))
    | None -> v)
    () e

let subst_var_slot
      (vars : Bound_var.t list)
      (e : core_exp) (s : env) : Bound_for_let.t * env =
  let phivar = Variable.create "ϕ" in
  let phi = Bound_var.create phivar Name_mode.normal in
  match descr e with
  | Named (Set_of_closures soc) ->
    let in_order = SlotMap.bindings soc.function_decls
    in
    let s =
      List.fold_left
      (fun s (var, (slot, _)) ->
         (Sub.add (Simple.var (Bound_var.var var))
          (Expr.create_named (Literal (Slot (Bound_var.var phi, Function_slot slot)))) s)) s
      (List.combine vars in_order)
    in
    (Singleton phi, s)
  | (Named (Literal _ | Prim _ | Closure_expr _ | Static_consts _ | Rec_info _) |
     Let _ | Let_cont _ | Apply _ | Apply_cont _ | Lambda _ | Handler _ | Switch _
    | Invalid _ ) ->
    Misc.fatal_error "Expected set of closures"

let subst_static_slot
      (bound : Symbol.t Function_slot.Lmap.t)
      (phi : Bound_var.t) s =
  let bound = Function_slot.Lmap.bindings bound in
  List.fold_left
  (fun s (slot, sym) ->
    (Sub.add (Simple.symbol sym)
        (Expr.create_named
          (Literal (Slot (Bound_var.var phi, Function_slot slot)))) s))
  s bound

let rec flambda_expr_to_core (e: expr) (s : env) : core_exp * env =
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
and let_to_core (e : Let_expr.t) (s : env) :
  core_exp * env =
  Let_expr.pattern_match e
    ~f:(fun var ~body ->
      (* The bound variable, [var], is being passed around for checking whether
         if when a [code_id] is bound, it is an anonymous function (i.e. whether
         the prefix starts with [anon-fn]) *)
      let x, e1, s = named_to_core var (Let_expr.defining_expr e) s in
      (* let x, e1, s = bound_pattern_to_core var e1 s in *)
      let e2, s = flambda_expr_to_core body s in
      let e2 = apply_subst s e2 in
      match e1 with
      | Some e1 ->
        Core_let.create ~x ~e1 ~e2, s
      | None -> e2, s)

and named_to_core (t : Bound_pattern.t) (e : Flambda.named) (s : env) :
  Bound_for_let.t * core_exp option * env =
  (match t, e with
  | Singleton v, Simple e ->
    let e = Literal (Simple e) in
    (Singleton v, Some (Expr.create_named e), s)
  | Singleton v, Prim (t, _) ->
    let e = Prim (prim_to_core t) in
    (Singleton v, Some (Expr.create_named e), s)
  | Set_of_closures vars, Set_of_closures e ->
    let e = Set_of_closures (set_of_closures_to_core e) |> Expr.create_named in
    let var, s = subst_var_slot vars e s in
    (var, Some e, s)
  | Static static, Static_consts e ->
    let static = Bound_static.to_list static in
    let body = Static_const_group.to_list e in
    let var, group, s =
      static_consts_to_core (List.combine static body) ([], []) s
    in
    let e = Expr.create_named (Static_consts group) in
    let e = apply_subst s e in
    (Static (Bound_codelike.create var), Some e, s)
  | Singleton v, Rec_info t ->
    let e = Expr.create_named (Rec_info t) in
    (Singleton v, Some e, s)
  | _, _ -> Misc.fatal_error "Mismatched let binding with expression")[@ocaml.warning "-4"]

and static_consts_to_core
      (l : (Bound_static.Pattern.t * Static_const_or_code.t) list) (pat_acc, acc) s:
  (Bound_codelike.Pattern.t list) * Flambda2_core.static_const_group * env =
  match l with
  | [] -> pat_acc, acc, s
  | (var, x) :: l ->
    let pat_acc, acc, s =
      (match var, x with
       | Code v, Code e ->
         let e, s =
           Code0.params_and_body e |> function_params_and_body_to_core s var
         in
         (Bound_codelike.Pattern.code v) :: pat_acc,
         (Code e) :: acc, s
       | Block_like v, Static_const t ->
         let e = static_const_to_core t in
         (Bound_codelike.Pattern.block_like v) :: pat_acc,
         (Static_const e) :: acc, s
       | Set_of_closures bound, Static_const (Set_of_closures soc) ->
         let phivar = (Variable.create "ϕ") in
         let phi = Bound_var.create phivar Name_mode.normal in
         (* substitue in new variable *)
         let soc = set_of_closures_to_core soc in
         let s = subst_static_slot bound phi s in
         (Bound_codelike.Pattern.set_of_closures phi)::pat_acc,
         (Static_const (Static_set_of_closures soc))::acc, s
       | Code v, Deleted_code ->
         (Bound_codelike.Pattern.code v) :: pat_acc,
         Deleted_code :: acc, s
       | _, _ -> Misc.fatal_error "Mismatched static consts binding")[@ocaml.warning "-4"]
    in
    static_consts_to_core l (pat_acc, acc) s

and set_of_closures_to_core (e : Set_of_closures.t) : set_of_closures =
  let function_decls =
    Set_of_closures.function_decls e |> function_declarations_to_core
  in
  let value_slots =
    Set_of_closures.value_slots e |> value_slots_to_core in
  { function_decls; value_slots }

and function_declarations_to_core (e : Function_declarations.t) : function_declarations =
    Function_declarations.funs_in_order e |>
    Function_slot.Lmap.map (fun x -> Expr.create_named (Literal (Code_id x))) |>
    Function_slot.Lmap.bindings |> List.to_seq |> SlotMap.of_seq

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

and function_params_and_body_to_core s
      (var : Bound_static.Pattern.t)
      (t : Flambda.function_params_and_body) =
  let name =
    (match var with
     | Code id -> id
     | (Set_of_closures _ | Block_like _) -> Misc.fatal_error "Expected code id")
  in
  let anon =
    String.starts_with ~prefix:"anon-fn[" (Code_id.name name)
  in
  let bound, my_closure, (body, s) =
    Function_params_and_body.pattern_match' t
      ~f:(fun (bound: Bound_for_function.t) ~body ->
        let my_closure = Bound_for_function.my_closure bound in
        bound, my_closure, flambda_expr_to_core body s)
  in
  let expr =
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
  in
  ({expr; anon}, s)

and subst_cont_id (cont : Continuation.t) (e1 : core_exp) (e2 : core_exp) : core_exp =
  core_fmap
    (fun _ x ->
       match must_be_cont x with
       | Some k ->
         if Continuation.equal cont k then e1 else x
       | _ -> x) () e2

and handler_map_to_closures (phi : Variable.t) (v : Bound_parameter.t list)
      (m : continuation_handler_map) : set_of_closures =
  (* for each continuation handler, create a new function slot and a
     lambda expression *)
  let in_order =
    Continuation.Map.fold
      (fun (key : Continuation.t) (e : continuation_handler)
        (fun_decls) ->
       (* add handler as a lambda to set of function decls *)
       let slot =
         Function_slot.create !comp_unit ~name:(Continuation.name key)
           Flambda_kind.With_subkind.any_value
       in
       let e =
         Core_continuation_handler.pattern_match
           e
           (fun params e ->
             let params =
               (Bound_parameters.to_list params) @ v |> Bound_parameters.create
             in
             Core_continuation_handler.create params
                (subst_cont_id key
                   (Expr.create_named (Literal (Slot (phi, Function_slot slot)))) e))
       in
       (* for every occurence of [key] in [e], substitute
          with Slot(phi, Function_slot slot) *)
       let lambda = Expr.create_handler e in
       SlotMap.add slot lambda fun_decls) m
    SlotMap.empty
  in
  { function_decls = in_order;
    value_slots = Value_slot.Map.empty }

(* Accumulate env in both the body and the handler, and substitute in
  the bindings for the whole expression. *)
and let_cont_to_core (e : Let_cont_expr.t) (sub : env) :
  core_exp * env =
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
        let exp = Core_letcont.create handler ~body in
        (exp, s))
  | Recursive r ->
    Recursive_let_cont_handlers.pattern_match_bound r
      ~f:
        (fun bound ~invariant_params ~body handler ->
           let body, _ = flambda_expr_to_core body sub in
           let phi = Variable.create "ϕ" in
           let handlers = cont_handlers_to_core handler sub in
           let clo =
             handler_map_to_closures phi
               (Bound_parameters.to_list invariant_params) handlers
           in
           let in_order = clo.function_decls |> SlotMap.bindings in
           let in_order_with_cont =
             List.combine (Bound_continuations.to_list bound) in_order
           in
           let e2 =
             List.fold_left
               (fun acc (cont, (slot, _)) ->
                  subst_cont_id cont
                    (Expr.create_named (Literal (Slot (phi, Function_slot slot)))) acc)
               body in_order_with_cont
           in
           let e = subst_singleton_set_of_closures ~bound:phi ~clo e2 in
           (e, sub))

and subst_singleton_set_of_closures ~(bound: Variable.t)
      ~(clo : set_of_closures) (e : core_exp) : core_exp =
  match descr e with
  | Named n -> subst_singleton_set_of_closures_named ~bound ~clo n e
  | Let e ->
    let_fix (subst_singleton_set_of_closures ~bound ~clo) e
  | Let_cont e ->
    let_cont_fix (subst_singleton_set_of_closures ~bound ~clo) e
  | Apply e ->
    apply_fix (subst_singleton_set_of_closures ~bound ~clo) e
  | Apply_cont e ->
    apply_cont_fix (subst_singleton_set_of_closures ~bound ~clo) e
  | Lambda e ->
    lambda_fix (subst_singleton_set_of_closures ~bound ~clo) e
  | Handler e ->
    handler_fix (subst_singleton_set_of_closures ~bound ~clo) e
  | Switch e ->
    switch_fix (subst_singleton_set_of_closures ~bound ~clo) e
  | Invalid _ -> e

and subst_singleton_set_of_closures_named ~bound ~clo (n : named) (e : core_exp) : core_exp =
  let f bound (v : literal) =
    (match v with
    | Simple v ->
      (if Simple.same v (Simple.var bound) then
         (let {function_decls; value_slots=_} = clo in
          match SlotMap.bindings function_decls with
          | [(slot, _)] ->
              Expr.create_named (Closure_expr (bound, slot, clo))
          | ([] | _::_)->
            Expr.create_named (Set_of_closures clo))
      else
        Expr.create_named (Literal (Simple v)))
    | Slot (phi, Function_slot slot) ->
      (let decls = SlotMap.bindings clo.function_decls in
       let bound_closure = List.find_opt (fun (x, _) -> x = slot) decls in
       (match bound_closure with
        | None -> e
        | Some (k, _) -> Expr.create_named (Closure_expr (phi, k, clo))
       ))
    | (Cont _ | Res_cont _ | Slot (_, Value_slot _) | Code_id _) ->
      Expr.create_named (Literal v))
  in
  match n with
  | Literal v -> f bound v
  | Prim _ -> prim_fix (subst_singleton_set_of_closures ~bound ~clo) e
  | Closure_expr (phi, slot, set) ->
    let set =
      set_of_closures_fix (subst_singleton_set_of_closures ~bound ~clo) set
    in
    Expr.create_named (Closure_expr (phi, slot, set))
  | Set_of_closures set ->
    let set =
      set_of_closures_fix (subst_singleton_set_of_closures ~bound ~clo) set
    in
    Expr.create_named (Set_of_closures set)
  | Static_consts group ->
    static_const_group_fix (subst_singleton_set_of_closures ~bound ~clo) group
  | Rec_info _ -> e

and cont_handler_to_core
      (e : Continuation_handler.t) (s : env)
  : continuation_handler * env =
  Continuation_handler.pattern_match e
    ~f:
      (fun var ~handler ->
         let handler, s = flambda_expr_to_core handler s in
         (Core_continuation_handler.create var handler, s))

and cont_handlers_to_core (e : Continuation_handlers.t) (s : env) :
  continuation_handler Continuation.Map.t =
  let e : Continuation_handler.t Continuation.Map.t =
    Continuation_handlers.to_map e in
  Continuation.Map.map
    (fun e ->
       let e, _ = cont_handler_to_core e s in e) e

and apply_to_core (e : Apply.t) (s : env)
  : core_exp * env =
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

and apply_cont_to_core (e : Apply_cont.t) (s : env)
  : core_exp * env =
  let e =
    Expr.create_apply_cont {
      k = Expr.create_named (Literal (Cont (Apply_cont_expr.continuation e)));
      args = Apply_cont_expr.args e |> List.map simple_to_core;}
  in
  e, s

and switch_to_core (e : Switch.t) (s : env)
  : core_exp * env =
  let e =
    Expr.create_switch {
      scrutinee = Switch_expr.scrutinee e |> simple_to_core;
      arms = Switch_expr.arms e |>
             Targetint_31_63.Map.map
               (fun x -> let e, _ = apply_cont_to_core x s in e)
      ;}
  in
  e, s

let flambda_unit_to_core e =
  let e, _ =
    flambda_expr_to_core (Flambda_unit.body e) Sub.empty
  in
  e
