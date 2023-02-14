open! Flambda
open! Flambda2_core
open! Translate

module P = Flambda_primitive

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
  | Let {let_abst; let_body} ->
     Core_let.pattern_match {let_abst; let_body}
       ~f:(fun ~x ~e1 ~e2 ->
          Core_let.create
            ~x
            ~e1:(subst_pattern_set_of_closures ~bound ~let_body e1)
            ~e2:(subst_pattern_set_of_closures ~bound ~let_body e2))
  | Let_cont _ ->
      failwith "Unimplemented subst_pattern_set_of_closures: Let_cont"
  | Apply _ ->
      failwith "Unimplemented subst_pattern_set_of_closures: Apply"
  | Apply_cont {k;args} ->
     Apply_cont
       { k = k;
         args = List.map (subst_pattern_set_of_closures ~bound ~let_body) args }
  | Switch _ ->
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
    | Some _ ->
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
    let list =
      List.map (subst_pattern_set_of_closures ~bound ~let_body) list in
    Static_consts [Static_const (Block (tag, mut, list))]
  | Static_consts _ ->
      failwith "Unimplemented subst_pattern_set_of_closures: Named Sc"
  | Rec_info _ ->
      failwith "Unimplemented subst_pattern_set_of_closures: Named Ri"
  | _ ->
    failwith "Unimplemented_subst_pattern_set_of_closures_named"

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
  | Block_load _ ->
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
  | Make_block (Naked_floats, _, _) ->
    failwith "Unimplemented_subst_pattern_primitive_variadic_make_block_floats"
  | Make_array _ ->
    failwith "Unimplemented_subst_pattern_primitive_variadic"

(* IY: What do coercions do?
   Has to do with inlining, ignore for now *)
and _simple_to_field_of_static_block (x : Simple.t) (dbg : Debuginfo.t)
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
     let bound = Simple.var (Bound_var.var bound) in
     if (Simple.equal s bound) then let_body else e
   | Named (Prim p) ->
     subst_pattern_primitive ~bound ~let_body p
   | Named (Static_consts [Static_const (Block (tag, mut, list))]) ->
      let list =
        List.map
          (fun x -> subst_pattern_singleton ~bound ~let_body x) list
     in
     Named (Static_consts [Static_const (Block (tag, mut, list))])
   | Named (Static_consts _) ->
     failwith "Unimplemented_subst_static_consts"
   | Named (Set_of_closures _) -> e
   | Named (Rec_info _) -> e
   | Let {let_abst; let_body} ->
     Core_let.pattern_match {let_abst; let_body}
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
    failwith "Unimplemented_static_consts"
  | Set_of_closures _ ->
    failwith "Unimplemented_set_of_closures"
  | Rec_info _ ->
    failwith "Unimplemented_block_like"

(* [Set of closures]

   Given the code for its functions and closure variables, the set of closures
    keeps track of the mapping between them.

   i.e. it is the code generated by
    [let f = closure f_0 @f] where [f_0] refers to the code *)
and subst_bound_set_of_closures (bound : Symbol.t Function_slot.Lmap.t) ~let_body
      (e : named) =
  match e with
  | Simple _ -> Named e
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
    failwith "Unimplemented_static_consts"
  | Set_of_closures _ ->
    failwith "Unimplemented_set_of_closures"
  | Rec_info _ ->
    failwith "Unimplemented_block_like"

and subst_code_id (bound : Code_id.t) ~(let_body : core_exp) (e : named) : core_exp =
  match e with
  | Simple _ -> Named e
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
  | Set_of_closures {function_decls; value_slots; alloc_mode} ->
    let in_order : function_expr Function_slot.Lmap.t = function_decls.in_order |>
      Function_slot.Lmap.map
        (fun x ->
          match x with
          | Id code_id ->
            if (Code_id.compare code_id bound = 0)
            then Exp let_body
            else Id code_id
          | Exp e ->
            Exp (subst_pattern_static ~bound:(Bound_static.Pattern.code bound)
                   ~let_body e))
    in
    let function_decls =
      { funs = Function_slot.Map.of_list (Function_slot.Lmap.bindings in_order);
        in_order}
    in
    Named (Set_of_closures {function_decls; value_slots; alloc_mode})
  | Static_consts [Static_const (Block (tag, immutable, exps))] ->
    let exps =
      List.map
        (subst_pattern_static ~bound:(Bound_static.Pattern.code bound) ~let_body) exps
    in
    Named (Static_consts [Static_const (Block (tag, immutable, exps))])
  | Static_consts
      [Static_const
         (Static_set_of_closures ({function_decls; value_slots; alloc_mode}))] ->
    let in_order : function_expr Function_slot.Lmap.t = function_decls.in_order |>
      Function_slot.Lmap.map
        (fun x ->
            match x with
            | Id code_id ->
              if (Code_id.compare code_id bound = 0)
              then Exp let_body
              else Id code_id
            | Exp e ->
              Exp (subst_pattern_static ~bound:(Bound_static.Pattern.code bound)
                    ~let_body e))
    in
    let function_decls =
      { funs = Function_slot.Map.of_list (Function_slot.Lmap.bindings in_order);
        in_order}
    in
    Named (Static_consts [Static_const
      (Static_set_of_closures {function_decls; value_slots; alloc_mode})])
  | Static_consts _ -> Named e
  | Rec_info _ ->
    failwith "Unimplemented_subst_code_id"

and subst_pattern_static
      ~(bound : Bound_static.Pattern.t) ~(let_body : core_exp) (e : core_exp) : core_exp =
  match e with
  | Apply_cont {k ; args} ->
    Apply_cont
      {k = k;
       args = List.map (subst_pattern_static ~bound ~let_body) args}
  | Let {let_abst; let_body} ->
    Core_let.pattern_match {let_abst; let_body}
      ~f:(fun ~x ~e1 ~e2 ->
        Core_let.create
          ~x
          ~e1:(subst_pattern_static ~bound ~let_body e1)
          ~e2:(subst_pattern_static ~bound ~let_body e2))
  | Switch {scrutinee; arms} ->
    Switch
      {scrutinee = subst_pattern_static ~bound ~let_body scrutinee;
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
                        param (subst_pattern_static ~bound ~let_body exp));
              body =
                Core_letcont_body.pattern_match body
                  (fun cont exp ->
                     Core_letcont_body.create
                       cont (subst_pattern_static ~bound ~let_body exp))})
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
         (subst_pattern_static ~bound:hd ~let_body e)) in
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
  | Let { let_abst; let_body } ->
    let bound, e, body =
      Core_let.pattern_match {let_abst; let_body}
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

let eval_prim_nullary (_v : P.nullary_primitive) : named =
  failwith "eval_prim_nullary"

let eval_prim_unary (_v : P.unary_primitive) (_arg : core_exp) : named =
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
  | Block_load (Values {tag = Known _; size = _; field_kind = _},
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
     | Named (Prim (Variadic (Make_block (_, Immutable, _), blocks))),
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
  | Block_load (_kind, _Mutable) ->
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

let eval_prim_ternary (_v : P.ternary_primitive)
      (_arg1 : core_exp) (_arg2 : core_exp) (_arg3 : core_exp) : named =
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
  | Let { let_abst; let_body } ->
    normalize_let let_abst let_body
  | Let_cont e ->
    normalize_let_cont e
    |> normalize
  | Apply {callee; continuation; exn_continuation; apply_args; call_kind} ->
    normalize_apply callee continuation exn_continuation apply_args call_kind
    |> normalize
  | Apply_cont {k ; args} ->
    (* The recursive call for [apply_cont] is done for the arguments *)
    normalize_apply_cont k args
  | Switch _ -> failwith "Unimplemented_normalize_switch"
  | Named e -> Named (normalize_named e)
  | Invalid _ -> e

and normalize_let let_abst body : core_exp =
  (* [LetL]
                  e1 ⟶ e1'
     -------------------------------------
     let x = e1 in e2 ⟶ let x = e1' in e2 *)
  let x, e1, e2 =
    Core_let.pattern_match {let_abst; let_body = body}
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
