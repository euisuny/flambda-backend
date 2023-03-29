open! Flambda
open! Flambda2_core

module P = Flambda_primitive

(** Translation from flambda2 terms to simplified core language **)
let simple_to_core (v : Simple.t) : core_exp =
  Named (Base (Simple (Simple.without_coercion v)))

let tagged_immediate_to_core (e : Targetint_31_63.t) : core_exp =
  Named (Base (Simple (Simple.const (Int_ids.Const.tagged_immediate e))))

let subst_var_slot_helper
          (var : Bound_var.t) (phi : Bound_var.t) (slot : Slot.t) (e2 : core_exp) =
  core_fmap
    (fun (var, phi, slot) v ->
       match v with
       | Simple v ->
          (if (Simple.same (Simple.var (Bound_var.var var)) v) then
            Named (Base (Slot (Bound_var.var phi, slot)))
           else Named (Base (Simple v)))
       | (Slot _) -> Named (Base v))
    (var, phi, slot) e2

let subst_var_slot
      (vars : Bound_var.t list) (phi : Bound_var.t) (e1 : core_exp) (e2 : core_exp) =
  match e1 with
  | Named (Set_of_closures {function_decls ; value_slots = _}) ->
    let in_order = Slot.Lmap.bindings function_decls
    in
    List.fold_left
      (fun acc (var, (slot, _)) ->
         subst_var_slot_helper var phi slot acc)
      e2
      (List.combine vars in_order)
  | (Named (Base _ | Prim _ | Closure_exp _ | Static_consts _ | Rec_info _) |
     Let _ | Apply _ | Apply_cont _ | Lambda _ | Switch _
    | Invalid _ ) ->
    Misc.fatal_error "Expected set of closures"

let make_slot (slot : Function_slot.t) : Slot.t =
  let unit = Function_slot.get_compilation_unit slot in
  let name = Function_slot.name slot in
  let kind = Function_slot.kind slot in
  Slot.create unit ~name kind

let subst_static_slot_helper
      (sym : Symbol.t) (phi : Bound_var.t) (slot : Function_slot.t) (e2 : core_exp) =
  core_fmap
    (fun (sym, phi, slot) v ->
      match v with
      | Simple v ->
        (if (Simple.same (Simple.symbol sym) v) then
          Named (Base (Slot (Bound_var.var phi, slot)))
        else Named (Base (Simple v)))
      | Slot _ -> Named (Base v))
    (sym, phi, make_slot slot) e2

let subst_static_slot
      (bound : Symbol.t Function_slot.Lmap.t) (phi : Bound_var.t) (e2 : core_exp) =
  let bound = Function_slot.Lmap.bindings bound in
  let e2 =
    List.fold_left
      (fun acc (slot, sym) -> subst_static_slot_helper sym phi slot acc)
      e2 bound
  in
  e2

let bound_static_to_core (t : Bound_static.Pattern.t) (e1 : core_exp) (e2 : core_exp) :
  Bound_codelike.Pattern.t * core_exp * core_exp =
  match t with
  | Set_of_closures bound ->
    let phi = Bound_var.create (Variable.create "ϕ") Name_mode.normal in
    (* Substitute in new variable *)
    let exp1 = subst_static_slot bound phi e1 in
    let exp2 = subst_static_slot bound phi e2 in
    (Bound_codelike.Pattern.set_of_closures phi, exp1, exp2)
  | Code v -> (Bound_codelike.Pattern.code v, e1, e2)
  | Block_like v -> (Bound_codelike.Pattern.block_like v, e1, e2)

let bound_pattern_to_core (t : Bound_pattern.t) (e1 : core_exp) (e2 : core_exp) :
  Bound_for_let.t * core_exp * core_exp =
  match t with
  | Singleton v -> (Singleton v, e1, e2)
  | Set_of_closures vars ->
    let phi = Bound_var.create (Variable.create "ϕ") Name_mode.normal
    in
    (* Substitute in new variable *)
    let e2 = subst_var_slot vars phi e1 e2
    in
    (Singleton phi, e1, e2)
  | Static s ->
    let static, e1, e2 =
      List.fold_left
        (fun (pat_acc1, acc1, acc2) x ->
           let pat, e1, e2 = bound_static_to_core x acc1 acc2 in
           (pat_acc1 @ [pat], e1, e2))
        ([], e1, e2)
        (Bound_static.to_list s)
    in
    (Static (Bound_codelike.create static), e1, e2)

let rec flambda_exp_to_core (e: expr) : core_exp =
  let e = Expr.descr e in
  match e with
  | Flambda.Let t -> let_to_core t
  | Flambda.Let_cont t -> let_cont_to_core t
  | Flambda.Apply t -> apply_to_core t
  | Flambda.Apply_cont t -> apply_cont_to_core t
  | Flambda.Switch t -> switch_to_core t
  | Flambda.Invalid { message = t } -> Invalid { message = t }

(* N.B. There is a new binder for [set_of_closures] in the core expession
   language. *)
and let_to_core (e : Let_expr.t) : core_exp =
  Let_expr.pattern_match e
    ~f:(fun var ~body ->
      (* The bound variable, [var], is being passed around for checking whether
         if when a [code_id] is bound, it is an anonymous function (i.e. whether
         the prefix starts with [anon-fn]) *)
      let e1 = Let_expr.defining_expr e |> named_to_core var
      in
      let x, e1, e2 = bound_pattern_to_core var e1 (flambda_exp_to_core body)
      in
      Core_let.create ~x ~e1 ~e2)

and named_to_core var (e : Flambda.named) : core_exp =
  Named (
    match e with
    | Simple e -> Base (Simple e)
    | Prim (t, _) -> Prim (prim_to_core t)
    | Set_of_closures e -> Set_of_closures (set_of_closures_to_core e)
    | Static_consts e -> Static_consts (static_consts_to_core var e)
    | Rec_info t -> Rec_info t)

and set_of_closures_to_core (e : Set_of_closures.t) : set_of_closures =
  failwith "unimplemented"
  (* let function_decls =
   *   Set_of_closures.function_decls e |> function_slots_to_core
   * in
   * let
   *   value_slots = Set_of_closures.value_slots e |> value_slots_to_core
   * in
   * { function_decls; value_slots } *)

and prim_to_core (e : P.t) : primitive =
  match e with
  | Nullary v -> Nullary v
  | Unary (prim, arg) ->
    Unary (prim, Named (Base (Simple arg)))
  | Binary (prim, arg1, arg2) ->
    Binary (prim, Named (Base (Simple arg1)), Named (Base (Simple arg2)))
  | Ternary (prim, arg1, arg2, arg3) ->
    Ternary (prim, Named (Base (Simple arg1)),
             Named (Base (Simple arg2)),
             Named (Base (Simple arg3)))
  | Variadic (prim, args) ->
    Variadic (prim,
              List.map (fun x -> Named (Base (Simple x))) args)

and static_consts_to_core var (e : Flambda.static_const_group) :
  Flambda2_core.static_const_group =
  let static_consts = Static_const_group.to_list e
  in
  let bound_consts = Bound_static.to_list (Bound_pattern.must_be_static var)
  in
  List.map (fun (bound, const) -> static_const_or_code_to_core bound const)
    (List.combine bound_consts static_consts)

and static_const_or_code_to_core var (e : Flambda.static_const_or_code) : core_exp =
  match e with
  | Code e -> Lambda
                (Code0.params_and_body e |>
                 function_params_and_body_to_core var)
  | Deleted_code -> Deleted_code
  | Static_const t -> Static_const (static_const_to_core t)

and static_const_to_core (e : Static_const.t) : Flambda2_core.static_const =
  match e with
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
    Named (Base (Simple (Simple.symbol e)))
  | Tagged_immediate e -> tagged_immediate_to_core e
  | Dynamically_computed (var, _) ->
    Named (Base (Simple (Simple.var var)))

and function_params_and_body_to_core (var : Bound_static.Pattern.t)
      (t : Flambda.function_params_and_body) :
  Flambda2_core.lambda_exp =
  let name =
    (match var with
     | Code id -> id
     | (Set_of_closures _ | Block_like _) -> Misc.fatal_error "Expected code id")
  in
  let anon =
    String.starts_with ~prefix:"anon-fn[" (Code_id.name name)
  in
  { exp =
      Function_params_and_body.pattern_match' t
        ~f:(fun (bound: Bound_for_function.t) ~body ->
          let my_closure = Bound_for_function.my_closure bound
          in
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
              (flambda_exp_to_core body))
        );
    anon}

and let_cont_to_core (e : Let_cont_exp.t) : core_exp =
  failwith "Unimplemented"

and apply_to_core (e : Apply.t) : core_exp =
  Apply {
    callee = Apply_exp.callee e |> simple_to_core;
    continuation = Named (Base (Res_cont (Apply_exp.continuation e)));
    exn_continuation = Named (Base (Cont (Apply_exp.exn_continuation e |>
                        Exn_continuation.exn_handler)));
    apply_args = Apply_exp.args e |> List.map simple_to_core }

and apply_cont_to_core (e : Apply_cont.t) : core_exp =
  Apply_cont {
    k = Named (Base (Cont (Apply_cont_exp.continuation e)));
    args = Apply_cont_exp.args e |> List.map simple_to_core;}

and switch_to_core (e : Switch.t) : core_exp =
  Switch {
    scrutinee = Switch_exp.scrutinee e |> simple_to_core;
    arms = Switch_exp.arms e |> Targetint_31_63.Map.map apply_cont_to_core;}

let flambda_unit_to_core e : core_exp =
  Flambda_unit.body e |> flambda_exp_to_core
