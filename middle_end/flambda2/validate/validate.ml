open! Flambda
open! Flambda2_core

module P = Flambda_primitive

(** Translation from flambda2 terms to simplified core language **)
let simple_to_core (v : Simple.t) : core_exp = Named (Simple v)

let tagged_immediate_to_core e =
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
    | Set_of_closures e -> Set_of_closures e
    | Static_consts e -> Static_consts (static_consts_to_core e)
    | Rec_info t -> Rec_info t)

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
  | Code e -> Code (function_params_and_body_to_code0
                      (Code0.code_metadata e)
                      (Code0.params_and_body e)
                      (Code0.free_names_of_params_and_body e))
  | Deleted_code -> Deleted_code
  | Static_const t -> Static_const (static_const_to_core t)

and static_const_to_core (e : Static_const.t) : Flambda2_core.static_const =
  match e with
  | Set_of_closures soc -> Set_of_closures soc
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
  | Dynamically_computed (var, dbg) ->
    Named (Simple (Simple.var var))

and function_params_and_body_to_code0 metadata (e : Flambda.function_params_and_body) free
  : Flambda2_core.function_params_and_body Code0.t =
  Core_code.create_with_metadata
    ~params_and_body:(function_params_and_body_to_core e)
    ~free_names_of_params_and_body:free
    ~code_metadata:metadata

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

let flambda_unit_to_core e : core_exp =
  Flambda_unit.body e |> flambda_expr_to_core

let _std_print =
  Format.fprintf Format.std_formatter "@. TERM:%a@." print

(** Normalization

    - CBV-style reduction for [let] and [letcont] expressions
    - Assumes that the [typeopt/value_kind] flag is [false] *)

(* Substitution funtions for β-reduction *)

(* [Let-β]
      e[bound\let_body] *)
let rec subst_pattern ~(bound : Bound_pattern.t) ~(let_body : core_exp) (e : core_exp)
  : core_exp =
  match bound with
  | Singleton bound ->
    subst_pattern_singleton ~bound ~let_body e
  | Set_of_closures bound ->
    subst_pattern_set_of_closures ~bound ~let_body e
  | Static bound ->
    subst_pattern_static_list ~bound ~let_body e

and subst_pattern_set_of_closures
      ~(bound : Bound_var.t list) ~(let_body : core_exp) (e : core_exp) : core_exp =
  match e with
  | Named e -> Named (subst_pattern_set_of_closures_named ~bound ~let_body e)
  | Let {let_abst; body} ->
     Core_let.pattern_match {let_abst; body}
       ~f:(fun ~x ~e1 ~e2 ->
          Core_let.create
            ~x
            ~e1:(subst_pattern_set_of_closures ~bound ~let_body e1)
            ~e2:(subst_pattern_set_of_closures ~bound ~let_body e2))
  | Let_cont e ->
      failwith "Unimplemented subst_pattern_set_of_closures: Let_cont"
  | Apply {callee;continuation;exn_continuation;args;call_kind} ->
      failwith "Unimplemented subst_pattern_set_of_closures: Apply"
  | Apply_cont {k;args} ->
     Apply_cont
       { k = k;
         args = List.map (subst_pattern_set_of_closures ~bound ~let_body) args }
  | Switch {scrutinee;arms} ->
      failwith "Unimplemented subst_pattern_set_of_closures: Switch"
  | Invalid _ -> e

and subst_pattern_set_of_closures_named
      ~(bound : Bound_var.t list) ~(let_body : core_exp) (e : named) : named =
  match e with
  | Simple v ->
    let opt_var =
      List.find_opt (fun x -> Simple.same (Simple.var (Bound_var.var x)) v) bound
    in
    (match opt_var with
    | Some var ->
       (match let_body with
       | Named (Set_of_closures soc) -> (Set_of_closures soc)
       | _ -> failwith "Expected set of closures")
    | None -> e)

  | Prim (Variadic (e, args)) ->
    let args =
      List.map (subst_pattern_set_of_closures ~bound ~let_body) args
    in
    (Prim (Variadic (e, args)))
  | Set_of_closures _ ->
      failwith "Unimplemented subst_pattern_set_of_closures: Named Soc"
  | Static_consts [Static_const (Block (tag, mut, list))] ->
    _std_print (Named e); failwith "Need block datatype changed"
  | Static_consts _ ->
      failwith "Unimplemented subst_pattern_set_of_closures: Named Sc"
  | Rec_info _ ->
      failwith "Unimplemented subst_pattern_set_of_closures: Named Ri"
  | _ -> e (*NEXT*)

and subst_pattern_primitive
      ~(bound : Bound_var.t) ~(let_body : core_exp) (e : primitive) : core_exp =
  match e with
  | Nullary _ ->
    failwith "Unimplemented_subst_pattern_primitive_nullary"
  | Unary _ ->
    failwith "Unimplemented_subst_pattern_primitive_unary"
  | Binary (e, a1, a2) ->
    subst_pattern_primitive_binary ~bound ~let_body (e, a1, a2)
  | Ternary _ ->
    failwith "Unimplemented_subst_pattern_primitive"
  | Variadic (e, args) ->
    subst_pattern_primitive_variadic ~bound ~let_body (e, args)

and subst_pattern_primitive_binary
      ~(bound : Bound_var.t) ~(let_body : core_exp)
      ((e, a1, a2) : P.binary_primitive * core_exp * core_exp) : core_exp =
  match e with
  | Block_load (kind, mut) ->
    Named
      (Prim (Binary
               (e,
                subst_pattern ~bound:(Bound_pattern.singleton bound) ~let_body a1,
                subst_pattern ~bound:(Bound_pattern.singleton bound) ~let_body a2)))
  | Array_load _
  | String_or_bigstring_load _
  | Bigarray_load _
  | Phys_equal _
  | Int_arith _
  | Int_shift _
  | Int_comp _
  | Float_arith _
  | Float_comp _ ->
    failwith "Unimplemented_subst_pattern_primitive_binary"

and subst_pattern_primitive_variadic
      ~(bound : Bound_var.t) ~(let_body : core_exp)
      ((e, args) : P.variadic_primitive * core_exp list) =
  match e with
  | Make_block (Values _, _, _) ->
    let args =
      List.map
        (subst_pattern ~bound:(Bound_pattern.singleton bound) ~let_body)
        args
    in
    Named (Prim (Variadic (e, args)))
  | Make_block (Naked_floats, mut, _) ->
    failwith "Unimplemented_subst_pattern_primitive_variadic_make_block_floats"
  | Make_array _ ->
    failwith "Unimplemented_subst_pattern_primitive_variadic"

(* IY: What do coercions do? *)
and simple_to_field_of_static_block (x : Simple.t) (dbg : Debuginfo.t)
      : Field_of_static_block.t =
  Simple.pattern_match' x
   ~var:(fun x ~coercion:_ -> Field_of_static_block.Dynamically_computed (x, dbg))
   ~symbol:(fun x ~coercion:_ -> Field_of_static_block.Symbol x)
   ~const:(fun x ->
      match Int_ids.Const.descr x with
      | Tagged_immediate x -> Field_of_static_block.Tagged_immediate x
      | _ -> failwith "Non-tagged immediates unsupported")

and subst_pattern_singleton
      ~(bound : Bound_var.t) ~(let_body : core_exp) (e : core_exp) : core_exp =
  (match e with
   | Named (Simple s) ->
     let bound : Variable.t = Bound_var.var bound in
     (* TODO: Is it OK to assign a Simple to a Variable? *)
     let bound = Simple.var bound in
     if (Simple.equal s bound) then let_body else e
   | Named (Prim p) ->
     subst_pattern_primitive ~bound ~let_body p
   | Named (Static_consts [Code _ | Deleted_code]) -> e (* NEXT *)
   | Named (Static_consts [Static_const (Block (tag, mut, list))]) ->
      let list =
        List.map
          (fun x -> subst_pattern_singleton ~bound ~let_body x) list
     in
     Named (Static_consts [Static_const (Block (tag, mut, list))])
   | Named (Set_of_closures _) -> e
   | Named (Rec_info _) -> e
   | Let {let_abst; body} ->
     Core_let.pattern_match {let_abst; body}
       ~f:(fun ~x ~e1 ~e2 ->
          Core_let.create
            ~x
            ~e1:(subst_pattern_singleton ~bound ~let_body e1)
            ~e2:(subst_pattern_singleton ~bound ~let_body e2))
   | Let_cont _ ->
     failwith "Unimplemented_subst_letcont"
   | Apply _ ->
     failwith "Unimplemented_subst_apply"
   | Apply_cont {k; args} ->
     Apply_cont
       { k = k;
         args = List.map (subst_pattern_singleton ~bound ~let_body) args }
   | Switch _ ->
     failwith "Unimplemented_subst_switch"
   | Invalid _ -> e)

and subst_block_like
      ~(bound : Symbol.t) ~(let_body : core_exp) (e : named) : core_exp =
  match e with
  | Simple v ->
    if Simple.equal v (Simple.symbol bound) then let_body else Named e
  | Prim (Nullary e) -> Named (Prim (Nullary e))
  | Prim (Unary (e, arg1)) ->
    let arg1 =
      subst_pattern_static ~bound:(Bound_static.Pattern.block_like bound) ~let_body arg1
    in
    Named (Prim (Unary (e, arg1)))
  | Prim (Binary (e, arg1, arg2)) ->
    let arg1 =
      subst_pattern_static ~bound:(Bound_static.Pattern.block_like bound) ~let_body arg1
    in
    let arg2 =
      subst_pattern_static ~bound:(Bound_static.Pattern.block_like bound) ~let_body arg2
    in
    Named (Prim (Binary (e, arg1, arg2)))
  | Prim (Ternary (e, arg1, arg2, arg3)) ->
    let arg1 =
      subst_pattern_static ~bound:(Bound_static.Pattern.block_like bound) ~let_body arg1
    in
    let arg2 =
      subst_pattern_static ~bound:(Bound_static.Pattern.block_like bound) ~let_body arg2
    in
    let arg3 =
      subst_pattern_static ~bound:(Bound_static.Pattern.block_like bound) ~let_body arg3
    in
    Named (Prim (Ternary (e, arg1, arg2, arg3)))
  | Prim (Variadic (e, args)) ->
    let args =
      List.map (subst_pattern_static ~bound:(Bound_static.Pattern.block_like bound) ~let_body) args
    in
    Named (Prim (Variadic (e, args)))
  | Static_consts _ ->
    (* FIXME double-check *) Named e
  | Set_of_closures set ->
    Named e (* NEXT *)
  | Rec_info _ ->
    failwith "Unimplemented_block_like"

(* Set of closures:

   Given the code for its functions and closure variables, the set of closures
    keeps track of the mapping between them.

   i.e. it is the code generated by
    [let f = closure f_0 @f] where [f_0] refers to the code *)
and subst_bound_set_of_closures (bound : Symbol.t Function_slot.Lmap.t) ~let_body (e : named) =
  match e with
  | Simple v -> (Named e)
  | Prim (Nullary e) -> Named (Prim (Nullary e))
  | Prim (Unary (e, arg1)) ->
    let arg1 =
      subst_pattern_static
        ~bound:(Bound_static.Pattern.set_of_closures bound) ~let_body arg1
    in
    Named (Prim (Unary (e, arg1)))
  | Prim (Binary (e, arg1, arg2)) ->
    let arg1 =
      subst_pattern_static
        ~bound:(Bound_static.Pattern.set_of_closures bound) ~let_body arg1
    in
    let arg2 =
      subst_pattern_static
        ~bound:(Bound_static.Pattern.set_of_closures bound) ~let_body arg2
    in
    Named (Prim (Binary (e, arg1, arg2)))
  | Prim (Ternary (e, arg1, arg2, arg3)) ->
    let arg1 =
      subst_pattern_static
        ~bound:(Bound_static.Pattern.set_of_closures bound) ~let_body arg1
    in
    let arg2 =
      subst_pattern_static
        ~bound:(Bound_static.Pattern.set_of_closures bound) ~let_body arg2
    in
    let arg3 =
      subst_pattern_static ~bound:(Bound_static.Pattern.set_of_closures bound) ~let_body arg3
    in
    Named (Prim (Ternary (e, arg1, arg2, arg3)))
  | Prim (Variadic (e, args)) ->
    let args =
      List.map
        (subst_pattern_static ~bound:(Bound_static.Pattern.set_of_closures bound) ~let_body) args
    in
    Named (Prim (Variadic (e, args)))
  | Static_consts _ ->
    (* FIXME double-check *) Named e
  | Set_of_closures set ->
    Named e (* NEXT *)
  | Rec_info _ ->
    failwith "Unimplemented_block_like"

and subst_code_id (bound : Code_id.t) ~(let_body : core_exp) (e : named) : core_exp =
  match e with
  | Simple v -> (Named e)
  | Prim (Nullary e) -> Named (Prim (Nullary e))
  | Prim (Unary (e, arg1)) ->
    let arg1 =
      subst_pattern_static
        ~bound:(Bound_static.Pattern.code bound) ~let_body arg1
    in
    Named (Prim (Unary (e, arg1)))
  | Prim (Binary (e, arg1, arg2)) ->
    let arg1 =
      subst_pattern_static
        ~bound:(Bound_static.Pattern.code bound) ~let_body arg1
    in
    let arg2 =
      subst_pattern_static
        ~bound:(Bound_static.Pattern.code bound) ~let_body arg2
    in
    Named (Prim (Binary (e, arg1, arg2)))
  | Prim (Ternary (e, arg1, arg2, arg3)) ->
    let arg1 =
      subst_pattern_static
        ~bound:(Bound_static.Pattern.code bound) ~let_body arg1
    in
    let arg2 =
      subst_pattern_static
        ~bound:(Bound_static.Pattern.code bound) ~let_body arg2
    in
    let arg3 =
      subst_pattern_static ~bound:(Bound_static.Pattern.code bound) ~let_body arg3
    in
    Named (Prim (Ternary (e, arg1, arg2, arg3)))
  | Prim (Variadic (e, args)) ->
    let args =
      List.map
        (subst_pattern_static ~bound:(Bound_static.Pattern.code bound) ~let_body) args
    in
    Named (Prim (Variadic (e, args)))
  | Set_of_closures _ ->
    (* FIXME double-check *) Named e
  | Static_consts _ ->
    (* FIXME double-check *) Named e
  | Rec_info _ ->
    failwith "Unimplemented_subst_code_id"

and subst_pattern_static
      ~(bound : Bound_static.Pattern.t) ~(let_body : core_exp) (e : core_exp) : core_exp =
  match e with
  | Apply_cont {k ; args} ->
    Apply_cont
      {k = k;
       args = List.map (subst_pattern_static ~bound ~let_body) args}
  | Let {let_abst; body} ->
    Core_let.pattern_match {let_abst; body}
      ~f:(fun ~x ~e1 ~e2 ->
        Core_let.create
          ~x
          ~e1:(subst_pattern_static bound let_body e1)
          ~e2:(subst_pattern_static bound let_body e2))
  | Switch {scrutinee; arms} ->
    Switch
      {scrutinee = subst_pattern_static bound let_body scrutinee;
        arms = Targetint_31_63.Map.map
                 (subst_pattern_static ~bound ~let_body) arms}
  | Named named ->
    (match bound with
     | Block_like bound ->
       subst_block_like ~bound ~let_body named
     | Set_of_closures set ->
       subst_bound_set_of_closures set ~let_body named
     | Code id ->
       subst_code_id id ~let_body named)
  | Let_cont e ->
    (match e with
     | Non_recursive {handler; body} ->
       Let_cont
         (Non_recursive
            { handler =
                Core_continuation_handler.pattern_match handler
                  (fun param exp ->
                      Core_continuation_handler.create
                        param (subst_pattern_static bound let_body exp));
              body =
                Core_letcont_body.pattern_match body
                  (fun cont exp ->
                     Core_letcont_body.create
                       cont (subst_pattern_static bound let_body exp))})
     | Recursive _ ->
       failwith "Unimplemented_static_clo_recursive"
    )
  | Apply _ -> failwith "Unimplemented_subst_pattern_static"
  | Invalid _ -> e

(* NOTE: Be careful with dominator-style [Static] scoping.. *)
and subst_pattern_static_list ~(bound : Bound_static.t) ~let_body e : core_exp =
  let rec subst_pattern_static_list_ s e =
    (match s with
     | [] -> e
     | hd :: tl ->
       subst_pattern_static_list_ tl
         (subst_pattern_static hd let_body e)) in
  subst_pattern_static_list_ (Bound_static.to_list bound) e

(* ∀ p i, p ∈ params -> params[i] = p -> e [p \ args[i]] *)
(* [Bound_parameters] are [Variable]s *)
let rec subst_params
  (params : Bound_parameters.t) (e : core_exp) (args : core_exp list) =
  let param_list =
    Bound_parameters.to_list params |> List.map Bound_parameter.simple
  in
  let param_args = List.combine param_list args in
  match e with
  | Named (Simple s) ->
    (match List.assoc_opt s param_args with
    | Some arg_v -> arg_v
    | None -> e)
  | Named (Prim (Binary (e, a1, a2))) ->
    Named (Prim
       (Binary (e, subst_params params a1 args, subst_params params a2 args)))
  | Named (Prim _) ->
    failwith "Unimplemented_param_named_prim"
  | Named (Set_of_closures _) ->
    failwith "Unimplemented_param_named_clo"
  | Named (Static_consts _ | Rec_info _) -> e
  | Let e ->
    Core_let.pattern_match e
      ~f:(fun ~x ~e1 ~e2 ->
        Core_let.create ~x
          ~e1:(subst_params params e1 args)
          ~e2:(subst_params params e2 args))
  | Apply_cont {k ; args =  args'} ->
    Apply_cont
      {k = k;
       args = List.map (fun x ->
         subst_params params x args) args'}
  | Let_cont _ ->
    failwith "Unimplemented_param_letcont"
  | Apply _ ->
    failwith "Unimplemented_param_apply"
  | Switch _ ->
    failwith "Unimplemented_param_switch"
  | Invalid _ -> e

(* [LetCont-β] *)
let rec subst_cont (cont_e1: core_exp) (k: Bound_continuation.t)
    (args: Bound_parameters.t) (cont_e2: core_exp) : core_exp =
  match cont_e1 with
  | Named _ -> cont_e1
  | Let { let_abst; body } ->
    let bound, e, body =
      Core_let.pattern_match {let_abst; body}
        ~f:(fun ~x ~e1 ~e2 ->
          (x, subst_cont e1 k args cont_e2,
              subst_cont e2 k args cont_e2))
    in
    Core_let.create ~x:bound ~e1:e ~e2:body
  | Let_cont _ ->
    failwith "Unimplemented_letcont"
  | Apply _ ->
    failwith "Unimplemented_apply"
  | Apply_cont {k = cont; args = concrete_args} ->
    if Continuation.equal cont k
    then subst_params args cont_e2 concrete_args
    else
      failwith "Unimplemented_apply_cont"
  | Switch _ ->
    failwith "Unimplemented_subst_cont"
  | Invalid _ -> cont_e1

let eval_prim_nullary (v : P.nullary_primitive) : named =
  failwith "eval_prim_nullary"

let eval_prim_unary (v : P.unary_primitive) (arg : core_exp) : named =
  failwith "eval_prim_unary"

let simple_tagged_immediate ~(const : Simple.t) : Targetint_31_63.t option =
  let constant =
    Simple.pattern_match' const
    ~var:(fun _ ~coercion:_ -> failwith "No variables allowed")
    ~symbol:(fun _ ~coercion:_ -> failwith "No symbols allowed")
    ~const:(fun t -> t)
  in
  match Int_ids.Const.descr constant with
  | Tagged_immediate i -> Some i
  | _ -> None

let eval_prim_binary
      (v : P.binary_primitive) (arg1 : core_exp) (arg2 : core_exp) : named =
  match v with
  | Block_load (Values {tag = Known tag; size; field_kind},
                (Immutable | Immutable_unique)) ->
    (* [arg1] is the block, and [arg2] is the index *)
    (match arg1, arg2 with
     | Named (Static_consts blocks), Named (Simple n) ->
       (* If we can inspect the index, then we can load from the immutable block *)
       if Simple.is_const n then
         (let index = simple_tagged_immediate ~const:n in
          match index with (* TODO: Match on the tags and size? *)
          | Some i -> Static_consts [List.nth blocks (Targetint_31_63.to_int i)]
          | None -> Prim (Binary (v, arg1, arg2)))
       else
         Prim (Binary (v, arg1, arg2))
     | Named (Prim (Variadic (Make_block (kind, Immutable, _), blocks))),
       Named (Simple n) ->
       if Simple.is_const n then
         (let index = simple_tagged_immediate ~const:n in
          match index with (* TODO: Match on the tags and size? *)
          | Some i ->
            (match List.nth blocks (Targetint_31_63.to_int i) with
             | Named n -> n
             | _ -> failwith "Non-name load")
          | None -> Prim (Binary (v, arg1, arg2)))
       else
         Prim (Binary (v, arg1, arg2))
     | _, _ ->
       failwith "Unimplemented immutable block_load")
  | Block_load (Naked_floats _, (Immutable | Immutable_unique)) ->
    failwith "Unimplemented immutable block load: naked_floats"
  | Block_load (kind, Mutable) ->
    failwith "Unimplemented mutable block load"
  | Array_load (_,_)
  | String_or_bigstring_load (_,_)
  | Bigarray_load (_,_,_)
  | Phys_equal _
  | Int_arith (_,_)
  | Int_shift (_,_)
  | Int_comp (_,_)
  | Float_arith _
  | Float_comp _ -> failwith "Unimplemented eval_prim_binary"

let eval_prim_ternary (v : P.ternary_primitive)
      (arg1 : core_exp) (arg2 : core_exp) (arg3 : core_exp) : named =
  failwith "eval_prim_ternary"

let eval_prim_variadic (v : P.variadic_primitive) (args : core_exp list) : named =
  match v with
  | Make_block (Values (tag, [kind]), _mut, _alloc_mode) ->
    (match args with
    | [Named (Simple n)] ->
      (* Reduce make block to immutable block *)
      (* LATER : generalize for taking in a list of arguments *)
      (match Flambda_kind.With_subkind.kind kind with
      | Value ->
          let constant =
            Simple.pattern_match' n
              ~var:(fun _ ~coercion:_ -> failwith "No variables allowed")
              ~symbol:(fun _ ~coercion:_ -> failwith "No symbols allowed")
              ~const:(fun t -> t)
          in
          (match Int_ids.Const.descr constant with
            | Tagged_immediate i ->
              let block = (Block (tag, Immutable, [tagged_immediate_to_core i]))
              in
              Static_consts [(Static_const block)]
            | (Naked_immediate _ | Naked_float _
              | Naked_int32 _ | Naked_int64 _ | Naked_nativeint _) ->
              failwith "Unimplemented constant")
        | (Naked_number _ | Region | Rec_info) ->
          failwith "Unimplemented_eval_prim: making block for non-value kind")
    | _ -> Prim (Variadic (v, args)))
  | Make_block _ ->
    Prim (Variadic (v, args))
  | Make_block (Naked_floats, _, _) ->
    failwith "eval_prim_variadic_naked_floats_unspported"
  | Make_array _ ->
    failwith "eval_prim_variadic_make_array_unspported"

let eval_prim (v : primitive) : named =
  match v with
  | Nullary v -> eval_prim_nullary v
  | Unary (v, arg) -> eval_prim_unary v arg
  | Binary (v, arg1, arg2) -> eval_prim_binary v arg1 arg2
  | Ternary (v, arg1, arg2, arg3) -> eval_prim_ternary v arg1 arg2 arg3
  | Variadic (v, args) -> eval_prim_variadic v args

(* This is a "normalization" of [named] expression, in quotations because there
  is some simple evaluation that occurs for primitive arithmetic expressions *)
let normalize_named (body : named) : named =
  match body with
  | Simple _ (* A [Simple] is a register-sized value *)
  | Set_of_closures _ (* Map of [Code_id]s and [Simple]s corresponding to
                         function and value slots*)
  | Rec_info _ (* Information about inlining recursive calls, an integer variable *)
  | Static_consts _ -> (* [Static_consts] are statically-allocated values *)
    body (* TODO (LATER): For [Static_consts], we might want to implement η-rules for
                 [Blocks]? *)
  | Prim v -> eval_prim v

let rec normalize (e:core_exp) : core_exp =
  match e with
  | Let { let_abst; body } ->
    normalize_let let_abst body
  | Let_cont e ->
    normalize_let_cont e
    |> normalize
  | Apply {callee; continuation; exn_continuation; args; call_kind} ->
    normalize_apply callee continuation exn_continuation args call_kind
    |> normalize
  | Apply_cont {k ; args} ->
    (* The recursive call for [apply_cont] is done for the arguments *)
    normalize_apply_cont k args
  | Switch _ -> failwith "Unimplemented_normalize_switch"
  | Named e -> Named (normalize_named e)
  | Invalid _ -> e

and replace_set_of_closures (e : core_exp) (bound : Bound_var.t list) (static : Symbol.t list) =
  match e with
  | Apply_cont {k ; args} ->
    Apply_cont
      {k = k;
       args = List.map (fun x -> replace_set_of_closures x bound static) args}
  | Let {let_abst; body} ->
    Core_let.pattern_match {let_abst; body}
      ~f:(fun ~x ~e1 ~e2 ->
        Core_let.create
          ~x
          ~e1:(replace_set_of_closures e1 bound static)
          ~e2:(replace_set_of_closures e2 bound static))
  | Switch {scrutinee; arms} ->
    Switch
      {scrutinee =
         replace_set_of_closures scrutinee bound static;
       arms = Targetint_31_63.Map.map
                (fun x -> replace_set_of_closures x bound static) arms}
  | Named named ->
    replace_set_of_closures_named named bound static
  | Let_cont e ->
    (match e with
     | Non_recursive {handler; body} ->
       Let_cont
         (Non_recursive
            { handler =
                Core_continuation_handler.pattern_match handler
                  (fun param exp ->
                      Core_continuation_handler.create
                        param (replace_set_of_closures exp bound static));
              body =
                Core_letcont_body.pattern_match body
                  (fun cont exp ->
                     Core_letcont_body.create
                       cont (replace_set_of_closures exp bound static))})
     | Recursive _ ->
       failwith "Unimplemented_static_clo_recursive"
    )
  | Apply _ -> failwith "Unimplemented_subst_pattern_static"
  | Invalid _ -> e

and replace_set_of_closures_named (e : named) (vars : Bound_var.t list) (static: Symbol.t list) =
  match e with
  | Simple v ->
    let rec find_static vs ss =
      (match vs, ss with
      | [], [] -> Named e
      | v' :: vtl,s :: stl ->
        if (Simple.same v (Simple.var v')) then (Named (Simple (Simple.symbol s))) else Named e)
    in
    find_static (List.map Bound_var.var vars) static

  | Prim (Nullary e) -> Named (Prim (Nullary e))
  | Prim (Unary (e, arg1)) ->
    let arg1 = replace_set_of_closures arg1 vars static in
    Named (Prim (Unary (e, arg1)))
  | Prim (Binary (e, arg1, arg2)) ->
    let arg1 = replace_set_of_closures arg1 vars static in
    let arg2 = replace_set_of_closures arg2 vars static in
    Named (Prim (Binary (e, arg1, arg2)))
  | Prim (Ternary (e, arg1, arg2, arg3)) ->
    let arg1 = replace_set_of_closures arg1 vars static in
    let arg2 = replace_set_of_closures arg2 vars static in
    let arg3 = replace_set_of_closures arg3 vars static in
    Named (Prim (Ternary (e, arg1, arg2, arg3)))
  | Prim (Variadic (e, args)) ->
    let args =
      List.map
        (fun x -> replace_set_of_closures x vars static) args
    in
    Named (Prim (Variadic (e, args)))
  | Static_consts _ ->
    (* FIXME double-check *) Named e
  | Set_of_closures set ->
    Named e (* NEXT *)
  | Rec_info _ ->
    failwith "Unimplemented_block_like"

and named_static_closures vars (e1 : core_exp) (e2 : core_exp)
  : Bound_pattern.t * core_exp * core_exp =
  match e1 with
  | Named (Set_of_closures set) ->
    let function_decls : Code_id.t Function_slot.Lmap.t =
      Set_of_closures.function_decls set |> Function_declarations.funs_in_order in
    let closure_symbols : Symbol.t Function_slot.Lmap.t =
      Function_slot.Lmap.mapi
        (fun function_slot _func_decl ->
           let name =
             function_slot |> Function_slot.rename |> Function_slot.to_string
             |> Linkage_name.of_string
           in
           Symbol.create (Compilation_unit.get_current_exn ()) name)
        function_decls in
    let set : static_const_or_code =
      Static_const (Set_of_closures set) in
    let bound =
      Bound_static.Pattern.set_of_closures closure_symbols |>
      Bound_static.singleton
    in
    let closure_list = closure_symbols |> Function_slot.Lmap.data in
    let e2 = replace_set_of_closures e2 vars closure_list in
    (Bound_pattern.static bound, Named (Static_consts [set]), e2)
  | _ -> failwith "Expected set of closures"

and normalize_let let_abst body : core_exp =
  (* [LetL]
                  e1 ⟶ e1'
     -------------------------------------
     let x = e1 in e2 ⟶ let x = e1' in e2 *)
  let x, e1, e2 =
    Core_let.pattern_match {let_abst; body}
      ~f:(fun ~x ~e1 ~e2 -> (x, normalize e1, e2))
  in
  (* [Let-β]
    let x = v in e2 ⟶ e2 [x\v] *)
  subst_pattern ~bound:x ~let_body:e1 e2 |> normalize

and normalize_let_cont (e:let_cont_expr) : core_exp =
  match e with
  | Non_recursive {handler; body} ->
    let args, e2 =
      Core_continuation_handler.pattern_match handler
        (fun bound body -> (bound, body))
    in
    let k, e1 =
      Core_letcont_body.pattern_match body (fun bound body -> (bound, body))
    in
    (* [LetCont-β]
       e1 where k args = e2 ⟶ e1 [k \ λ args. e2] *)
    subst_cont e1 k args e2
  | Recursive _handlers -> failwith "Unimplemented_recursive"

and normalize_apply _callee _continuation _exn_continuation _args _call_kind : core_exp =
  failwith "Unimplemented_apply"

and normalize_apply_cont k args : core_exp =
  (* [ApplyCont]
            args ⟶ args'
      --------------------------
        k args ⟶ k args'       *)
  Apply_cont {k = k; args = List.map normalize args}

let simulation_relation src tgt =
  let {Simplify.unit = tgt; _} = tgt in
  let src_core = Flambda_unit.body src |> flambda_expr_to_core in
  let tgt_core = Flambda_unit.body tgt |> flambda_expr_to_core in
  Equiv.core_eq src_core tgt_core

(** Top-level validator *)
let validate ~cmx_loader ~round src =
  let tgt = Simplify.run ~cmx_loader ~round src in
  simulation_relation src tgt
