open! Flambda
open! Flambda2_core
open! Translate

module P = Flambda_primitive

let _std_print =
  Format.fprintf Format.std_formatter "@. TERM:%a@." print

module Env = struct

  type t =
    { mutable _values : (Simple.t * Flambda_kind.With_subkind.t) Value_slot.Map.t;
      mutable _functions : function_expr Function_slot.Map.t }

  let create () =
    { _values = Value_slot.Map.empty;
      _functions = Function_slot.Map.empty }
end

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
  | Named e -> subst_pattern_set_of_closures_named ~bound ~let_body e
  | Let {let_abst; expr_body} ->
     Core_let.pattern_match {let_abst; expr_body}
       ~f:(fun ~x ~e1 ~e2 ->
          Core_let.create
            ~x
            ~e1:(subst_pattern_set_of_closures ~bound ~let_body e1)
            ~e2:(subst_pattern_set_of_closures ~bound ~let_body e2))
  | Let_cont (Non_recursive {handler; body}) ->
    let handler =
      Core_continuation_handler.pattern_match handler
        (fun param exp ->
           Core_continuation_handler.create param
             (subst_pattern_set_of_closures ~bound ~let_body exp))
    in
    let body =
      Core_letcont_body.pattern_match body
        (fun cont exp ->
           Core_letcont_body.create cont
             (subst_pattern_set_of_closures ~bound ~let_body exp))
    in
    Let_cont (Non_recursive {handler; body})
  | Let_cont (Recursive _) ->
      failwith "Unimplemented subst_pattern_set_of_closures: Let_cont recursive case"
  | Apply {callee; continuation; exn_continuation; apply_args; call_kind} ->
    Apply
      {callee = subst_pattern_set_of_closures ~bound ~let_body callee;
       continuation; exn_continuation;
       apply_args =
         List.map (subst_pattern_set_of_closures ~bound ~let_body) apply_args;
       call_kind}
  | Apply_cont {k;args} ->
     Apply_cont
       { k = k;
         args = List.map (subst_pattern_set_of_closures ~bound ~let_body) args }
  | Switch _ ->
      failwith "Unimplemented subst_pattern_set_of_closures: Switch"
  | Invalid _ -> e

and subst_pattern_set_of_closures_named
      ~(bound : Bound_var.t list) ~(let_body : core_exp) (e : named) : core_exp =
  match e with
  | Simple v ->
    let opt_var =
      List.mapi (fun i x ->
        if Simple.same (Simple.var (Bound_var.var x)) v then Some i else None) bound
      |> List.filter Option.is_some
    in
    (match opt_var with
    | Some i :: _ ->
       (match let_body with
        | Named (Set_of_closures soc) ->
          let decls =
            soc.function_decls.in_order |> Function_slot.Lmap.bindings
          in
          let (slot, _) = List.nth decls i
          in
          Named (Closure_expr (slot, soc))
       | _ -> failwith "Expected set of closures")
    | _ -> Named e)
  | Prim (Unary (e, arg)) ->
    let arg = subst_pattern_set_of_closures ~bound ~let_body arg
    in
    Named (Prim (Unary (e, arg)))
  | Prim (Binary (e, arg1, arg2)) ->
    let arg1 = subst_pattern_set_of_closures ~bound ~let_body arg1
    in
    let arg2 = subst_pattern_set_of_closures ~bound ~let_body arg2
    in
    Named (Prim (Binary (e, arg1, arg2)))
  | Prim (Ternary (e, arg1, arg2, arg3)) ->
    let arg1 = subst_pattern_set_of_closures ~bound ~let_body arg1
    in
    let arg2 = subst_pattern_set_of_closures ~bound ~let_body arg2
    in
    let arg3 = subst_pattern_set_of_closures ~bound ~let_body arg3
    in
    Named (Prim (Ternary (e, arg1, arg2, arg3)))
  | Prim (Variadic (e, args)) ->
    let args =
      List.map (subst_pattern_set_of_closures ~bound ~let_body) args
    in
    Named (Prim (Variadic (e, args)))
  | Set_of_closures {function_decls; value_slots; alloc_mode} ->
    let value_slots =
      List.fold_left (fun value_slots b ->
        Value_slot.Map.map
          (fun (value, k) ->
            match value with
            | Simple_value simple ->
              let bound = Simple.var (Bound_var.var b) in
              if (Simple.equal simple bound)
              then
               (Value_exp let_body, k)
              else (Simple_value simple, k)
            | Value_exp exp ->
              (Value_exp
                 (subst_pattern ~bound:(Bound_pattern.set_of_closures bound)
                    ~let_body exp), k)
          ) value_slots) value_slots bound
    in
    Named (Set_of_closures {function_decls; value_slots; alloc_mode})
  | Closure_expr
      (slot, {function_decls; value_slots; alloc_mode}) ->
    let value_slots =
      List.fold_left (fun value_slots b ->
        Value_slot.Map.map
          (fun (value, k) ->
             match value with
             | Simple_value simple ->
               let bound = Simple.var (Bound_var.var b) in
               if (Simple.equal simple bound)
               then (Value_exp let_body, k)
               else (Simple_value simple, k)
             | Value_exp exp ->
               (Value_exp
                  (subst_pattern ~bound:(Bound_pattern.set_of_closures bound)
                     ~let_body exp), k)
          ) value_slots) value_slots bound
    in
    Named (Closure_expr (slot, {function_decls; value_slots; alloc_mode}))
  | Static_consts [Static_const (Block (tag, mut, list))] ->
    let list =
      List.map (subst_pattern_set_of_closures ~bound ~let_body) list in
    Named (Static_consts [Static_const (Block (tag, mut, list))])
  | Static_consts _ ->
      failwith "Unimplemented subst_pattern_set_of_closures: Named Sc"
  | Rec_info _ ->
    failwith "Unimplemented subst_pattern_set_of_closures: Named Ri"
  | _ ->
    failwith "Unimplemenetd subst_pattern_set_of_closures_named"

and subst_pattern_primitive
      ~(bound : Bound_var.t) ~(let_body : core_exp) (e : primitive) : core_exp =
  match e with
  | Nullary _ -> Named (Prim e)
  | Unary (e, a) ->
    Named
      (Prim (Unary
               (e,
                subst_pattern ~bound:(Bound_pattern.singleton bound) ~let_body a)))
  | Binary (e, a1, a2) ->
    Named
      (Prim (Binary
               (e,
                subst_pattern ~bound:(Bound_pattern.singleton bound) ~let_body a1,
                subst_pattern ~bound:(Bound_pattern.singleton bound) ~let_body a2)))
  | Ternary (e, a1, a2, a3) ->
    Named
      (Prim (Ternary
               (e,
                subst_pattern ~bound:(Bound_pattern.singleton bound) ~let_body a1,
                subst_pattern ~bound:(Bound_pattern.singleton bound) ~let_body a2,
                subst_pattern ~bound:(Bound_pattern.singleton bound) ~let_body a3)))
  | Variadic (e, args) ->
    let args =
      List.map
        (subst_pattern ~bound:(Bound_pattern.singleton bound) ~let_body)
        args
    in
    Named (Prim (Variadic (e, args)))

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
          (fun x ->
             subst_pattern_singleton ~bound ~let_body x) list
     in
     Named (Static_consts [Static_const (Block (tag, mut, list))])
   | Named (Set_of_closures {function_decls; value_slots; alloc_mode}) ->
     let value_slots =
       Value_slot.Map.map
         (fun (value, k) ->
            match value with
            | Simple_value simple ->
              let bound = Simple.var (Bound_var.var bound) in
              if (Simple.equal simple bound)
              then (Value_exp let_body, k)
              else (Simple_value simple, k)
            | Value_exp exp ->
              (Value_exp (subst_pattern_singleton ~bound ~let_body exp), k)
         ) value_slots
     in
     Named (Set_of_closures {function_decls; value_slots; alloc_mode})
   | Named (Closure_expr (slot, {function_decls; value_slots; alloc_mode})) ->
     let value_slots =
       Value_slot.Map.map
         (fun (value, k) ->
            match value with
            | Simple_value simple ->
              let bound = Simple.var (Bound_var.var bound) in
              if (Simple.equal simple bound)
              then (Value_exp let_body, k)
              else (Simple_value simple, k)
            | Value_exp exp ->
              (Value_exp (subst_pattern_singleton ~bound ~let_body exp), k)
         ) value_slots
     in
     Named (Closure_expr (slot, {function_decls; value_slots; alloc_mode}))
   | Named (Static_consts _) ->
     failwith "Unimplemented_subst_static_consts"
   | Named (Rec_info _) -> e
   | Let {let_abst; expr_body} ->
     Core_let.pattern_match {let_abst; expr_body}
       ~f:(fun ~x ~e1 ~e2 ->
          Core_let.create
            ~x
            ~e1:(subst_pattern_singleton ~bound ~let_body e1)
            ~e2:(subst_pattern_singleton ~bound ~let_body e2))
   | Let_cont (Non_recursive {handler;body}) ->
     Let_cont
       (Non_recursive
          { handler =
              Core_continuation_handler.pattern_match handler
                (fun param exp ->
                   Core_continuation_handler.create
                     param (subst_pattern_singleton ~bound ~let_body exp));
            body =
              Core_letcont_body.pattern_match body
                (fun cont exp ->
                   Core_letcont_body.create
                     cont (subst_pattern_singleton ~bound ~let_body exp))})
   | Let_cont _ ->
     failwith "Unimplemented_subst_letcont recursive case"
   | Apply {callee; continuation; exn_continuation; apply_args; call_kind} ->
     Apply
       {callee = subst_pattern_singleton ~bound ~let_body callee;
        continuation; exn_continuation;
        apply_args =
          List.map (subst_pattern_singleton ~bound ~let_body) apply_args;
        call_kind}
   | Apply_cont {k; args} ->
     Apply_cont
       { k = k;
         args = List.map (subst_pattern_singleton ~bound ~let_body) args }
   | Switch {scrutinee; arms} ->
     Switch
       { scrutinee = subst_pattern_singleton ~bound ~let_body scrutinee;
         arms = Targetint_31_63.Map.map (subst_pattern_singleton ~bound ~let_body) arms;}
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
  | Static_consts l ->
    subst_block_like_static_const_group ~bound ~let_body l
  | Closure_expr _ ->
    Named e (* NEXT *)
  | Set_of_closures _ ->
    Named e (* NEXT *)
  | Rec_info _ ->
    failwith "Unimplemented_block_like"

and subst_block_like_static_const_group
      ~(bound: Symbol.t) ~(let_body : core_exp) (e : static_const_group) : core_exp =
  Named (Static_consts
        (List.map (subst_block_like_static_const_or_code ~bound ~let_body) e))

and subst_block_like_static_const_or_code
      ~(bound: Symbol.t) ~(let_body : core_exp) (e : static_const_or_code) : static_const_or_code =
  match e with
  | Static_const const -> Static_const (subst_block_like_static_const ~bound ~let_body const)
  | (Code _ | Deleted_code) -> e

and subst_block_like_static_const
      ~(bound: Symbol.t) ~(let_body : core_exp) (e : static_const) : static_const =
  match e with
  | Block (tag, mut, args) ->
    let args =
      List.map
        (subst_pattern_static ~bound:(Bound_static.Pattern.block_like bound) ~let_body)
        args
    in
    Block (tag, mut, args)
  | _ -> e (* NEXT *)

(* [Set of closures]

   Given the code for its functions and closure variables, the set of closures
    keeps track of the mapping between them.

   i.e. it is the code generated by
    [let f = closure f_0 @f] where [@f] is the function slot and [f_0] refers
    to the code *)
and subst_bound_set_of_closures (bound : Symbol.t Function_slot.Lmap.t) ~let_body
      (e : named) =
  match e with
  | Simple v ->
    (match let_body with
     | Named (Static_consts consts) ->
       (* Assumption : there is at most one [set_of_closures] definition *)
       let set =
         List.find_opt
          (fun x ->
              match x with
              | Static_const (Static_set_of_closures _) -> true
              | _ -> false) consts
       in
       (match set with
        | Some (Static_const (Static_set_of_closures set)) ->
          (let bound = Function_slot.Lmap.bindings bound
           in
           (* try to find if any of the symbols being bound is the same as the variable v *)
           let bound_closure =
             List.find_opt (fun (_, x) ->
               Simple.same v (Simple.symbol x)) bound
           in
           (match bound_closure with
            | None -> Named e
            | Some (k, _) -> Named (Closure_expr (k, set))
           ))
        | Some _ -> failwith "Cannot be reached"
        | None -> Named e)
     | _ -> Named e
    )
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
  | Static_consts e ->
    subst_bound_set_of_closures_static_const_group ~bound ~let_body e
  | Closure_expr _ ->
    Named e (* NEXT *)
  | Set_of_closures _ ->
    failwith "Unimplemented_set_of_closures"
  | Rec_info _ ->
    failwith "Unimplemented_block_like"

and subst_bound_set_of_closures_static_const_group
      ~bound ~(let_body : core_exp) (e : static_const_group) : core_exp =
  Named (Static_consts
           (List.map (subst_bound_set_of_closures_static_const_or_code ~bound ~let_body) e))

and subst_bound_set_of_closures_static_const_or_code
      ~bound ~(let_body : core_exp) (e : static_const_or_code) : static_const_or_code =
  match e with
  | Static_const const ->
    Static_const (subst_bound_set_of_closures_static_const ~bound ~let_body const)
  | Code params_and_body ->
    Code
      (Core_function_params_and_body.pattern_match
         params_and_body
         ~f:(fun
            params body ->
            Core_function_params_and_body.create
              params
              (subst_pattern_static
                 ~bound:(Bound_static.Pattern.set_of_closures bound)
                 ~let_body body)))
  | Deleted_code -> e

and subst_bound_set_of_closures_static_const
      ~bound ~(let_body : core_exp) (e : static_const) : static_const =
  match e with
  | Block (tag, mut, args) ->
    let args =
      List.map
        (subst_pattern_static ~bound:(Bound_static.Pattern.set_of_closures bound) ~let_body)
        args
    in
    Block (tag, mut, args)
  | Static_set_of_closures {function_decls;value_slots;alloc_mode}->
    (let in_order : function_expr Function_slot.Lmap.t =
       function_decls.in_order |>
       Function_slot.Lmap.map
         (fun x ->
            match x with
            | Id code_id -> Id code_id
            | Exp e ->
              Exp (subst_pattern_static
                     ~bound:(Bound_static.Pattern.set_of_closures bound)
                     ~let_body e))
     in
     let function_decls =
       { funs = Function_slot.Map.of_list (Function_slot.Lmap.bindings in_order);
         in_order }
     in
     (Static_set_of_closures {function_decls; value_slots; alloc_mode}))
    (* let function_decls
     * failwith "Unimplemented static set of closures" *)
  | _ -> e (* NEXT *)

and subst_code_id_set_of_closures (bound : Code_id.t) ~(let_body : core_exp)
      {function_decls; value_slots; alloc_mode}
  : set_of_closures =
  let in_order : function_expr Function_slot.Lmap.t =
    function_decls.in_order |>
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
  {function_decls; value_slots; alloc_mode}

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
  | Closure_expr (slot, set) ->
    Named (Closure_expr (slot, subst_code_id_set_of_closures bound ~let_body set))
  | Set_of_closures set ->
    let set = subst_code_id_set_of_closures bound ~let_body set
    in
    Named (Set_of_closures set)
  | Static_consts [Static_const (Block (tag, immutable, exps))] ->
    let exps =
      List.map
        (subst_pattern_static ~bound:(Bound_static.Pattern.code bound) ~let_body) exps
    in
    Named (Static_consts [Static_const (Block (tag, immutable, exps))])
  | Static_consts consts ->
    (* Assumption : there is at most one [set_of_closures] definition *)
    let consts =
      List.map
        (fun x ->
           match x with
           | Static_const
               (Static_set_of_closures {function_decls; value_slots; alloc_mode})
             ->
             (let in_order : function_expr Function_slot.Lmap.t =
               function_decls.in_order |>
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
                 in_order }
             in
             Static_const (Static_set_of_closures {function_decls; value_slots; alloc_mode}))
           | x -> x)
        consts
    in
    Named (Static_consts consts)
  | Rec_info _ ->
    failwith "Unimplemented_subst_code_id"

and subst_pattern_static
      ~(bound : Bound_static.Pattern.t) ~(let_body : core_exp) (e : core_exp) : core_exp =
  match e with
  | Apply_cont {k ; args} ->
    Apply_cont
      {k = k;
       args = List.map (subst_pattern_static ~bound ~let_body) args}
  | Let {let_abst; expr_body} ->
    Core_let.pattern_match {let_abst; expr_body}
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
  | Apply {callee; continuation; exn_continuation; apply_args; call_kind} ->
    Apply
      {callee = subst_pattern_static ~bound ~let_body callee;
       continuation; exn_continuation;
       apply_args =
         List.map (subst_pattern_static ~bound ~let_body) apply_args;
       call_kind}
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
  | Named (Prim (Unary (e, arg))) ->
    let arg = subst_params params arg args
    in
    Named (Prim (Unary (e, arg)))
  | Named (Prim (Binary (e, arg1, arg2))) ->
    let arg1 = subst_params params arg1 args
    in
    let arg2 = subst_params params arg2 args
    in
    Named (Prim (Binary (e, arg1, arg2)))
  | Named (Prim (Ternary (e, arg1, arg2, arg3))) ->
    let arg1 = subst_params params arg1 args
    in
    let arg2 = subst_params params arg2 args
    in
    let arg3 = subst_params params arg3 args
    in
    Named (Prim (Ternary (e, arg1, arg2, arg3)))
  | Named (Prim (Variadic (e, args))) ->
    let args = List.map (fun x -> subst_params params x args) args
    in
    Named (Prim (Variadic (e, args)))
  | Named (Prim (Nullary _)) -> e
  | Named (Closure_expr _) ->
    failwith "Unimplemented_param_named_clo_expr"
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
  | Let_cont (Non_recursive {handler; body}) ->
    Let_cont
      (Non_recursive
         { handler =
             Core_continuation_handler.pattern_match handler
               (fun param exp ->
                  Core_continuation_handler.create
                    param (subst_params params exp args));
           body =
             Core_letcont_body.pattern_match body
               (fun cont exp ->
                  Core_letcont_body.create
                    cont (subst_params params exp args))})
  | Let_cont (Recursive _) ->
    failwith "Unimplemented_param_letcont recursive"
  | Apply {callee; continuation; exn_continuation; apply_args; call_kind} ->
    Apply
      {callee = subst_params params callee args;
       continuation; exn_continuation;
       apply_args =
         List.map (fun exp -> subst_params params exp args) apply_args;
       call_kind}
  | Switch _ ->
    failwith "Unimplemented_param_switch"
  | Invalid _ -> e

(* [LetCont-β] *)
let rec subst_cont (cont_e1: core_exp) (k: Bound_continuation.t)
    (args: Bound_parameters.t) (cont_e2: core_exp) : core_exp =
  match cont_e1 with
  | Named _ -> cont_e1
  | Let { let_abst; expr_body } ->
    let bound, e, body =
      Core_let.pattern_match {let_abst; expr_body}
        ~f:(fun ~x ~e1 ~e2 ->
          (x, subst_cont e1 k args cont_e2,
              subst_cont e2 k args cont_e2))
    in
    Core_let.create ~x:bound ~e1:e ~e2:body
  | Let_cont _ ->
    failwith "Unimplemented_letcont"
  | Apply {callee; continuation; exn_continuation; apply_args; call_kind} ->
    Apply
      {callee = subst_cont callee k args cont_e2;
       continuation; exn_continuation;
       apply_args =
         List.map (fun e1 -> subst_cont e1 k args cont_e2) apply_args;
       call_kind}
  | Apply_cont {k = cont; args = concrete_args} ->
    if Continuation.equal cont k
    then subst_params args cont_e2 concrete_args
    else
      Apply_cont
        {k = cont; args = List.map (fun x -> subst_cont x k args cont_e2) concrete_args}
  | Switch {scrutinee; arms} ->
    Switch
      {scrutinee = subst_cont scrutinee k args cont_e2;
       arms = Targetint_31_63.Map.map (fun x -> subst_cont x k args cont_e2) arms;}
  | Invalid _ -> cont_e1

let eval_prim_nullary (_v : P.nullary_primitive) : named =
  failwith "eval_prim_nullary"

let eval_prim_unary _env (v : P.unary_primitive) (_arg : core_exp) : named =
  match v with
  | Project_value_slot _ -> (Prim (Unary (v, _arg))) (* TODO *)
  | Untag_immediate ->
    (match _arg with
     | Named (Prim (Unary (Tag_immediate, Named (Prim (Unary (Is_int a, e)))))) ->
       (Prim (Unary (Is_int a, e)))
     | _ -> (Prim (Unary (v, _arg))))
  | (Get_tag | Array_length | Int_as_pointer | Boolean_not
    | Reinterpret_int64_as_float | Tag_immediate
    | Is_boxed_float | Is_flat_float_array | Begin_try_region
    | End_region | Obj_dup | Duplicate_block _ | Duplicate_array _
    | Is_int _ | Bigarray_length _ | String_length _
    | Opaque_identity _ | Int_arith (_,_) | Float_arith _
    | Num_conv _ | Unbox_number _ | Box_number (_, _)
    | Project_function_slot _ ) ->
    (Prim (Unary (v, _arg)))

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
      (v : P.binary_primitive) (arg1 : core_exp) (arg2 : core_exp) : core_exp =
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
          | Some i -> (* IY: Doublecheck loading scheme from blocks *)
            (match List.nth blocks 0 with
             | Static_const (Block (_, _, l)) ->
               List.nth l (Targetint_31_63.to_int i)
             | _ -> failwith "Unimplemented_block_load")

          | None -> Named (Prim (Binary (v, arg1, arg2))))
       else
         Named (Prim (Binary (v, arg1, arg2)))
     | Named (Prim (Variadic (Make_block (_, Immutable, _), blocks))),
       Named (Simple n) ->
       if Simple.is_const n then
         (let index = simple_tagged_immediate ~const:n in
          match index with (* TODO: Match on the tags and size? *)
          | Some i ->
            (match List.nth blocks (Targetint_31_63.to_int i) with
             | Named n -> Named n
             | _ -> failwith "Non-name load")
          | None -> Named (Prim (Binary (v, arg1, arg2))))
       else
         Named (Prim (Binary (v, arg1, arg2)))
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

let eval_prim (env : Env.t) (v : primitive) : core_exp =
  match v with
  | Nullary v -> Named (eval_prim_nullary v)
  | Unary (v, arg) -> Named (eval_prim_unary env v arg)
  | Binary (v, arg1, arg2) -> eval_prim_binary v arg1 arg2
  | Ternary (v, arg1, arg2, arg3) -> Named (eval_prim_ternary v arg1 arg2 arg3)
  | Variadic (v, args) -> Named (eval_prim_variadic v args)

let rec normalize (env : Env.t) (e:core_exp) : core_exp =
  match e with
  | Let { let_abst; expr_body } ->
    normalize_let env let_abst expr_body
    |> normalize env
  | Let_cont e ->
    normalize_let_cont env e
    |> normalize env
  | Apply {callee; continuation; exn_continuation; apply_args; call_kind} ->
    normalize_apply env callee continuation exn_continuation apply_args call_kind
  | Apply_cont {k ; args} ->
    (* The recursive call for [apply_cont] is done for the arguments *)
    normalize_apply_cont env k args
  | Switch {scrutinee; arms} -> (* TODO *)
    Switch {scrutinee = normalize env scrutinee; arms}
  | Named e -> normalize_named env e
  | Invalid _ -> e

and normalize_let env let_abst body : core_exp =
  let x, e1, e2 =
    Core_let.pattern_match {let_abst; expr_body = body}
      ~f:(fun ~x ~e1 ~e2 -> (x, e1, e2))
  in
  match body with
  | Named (Static_consts [Code _]) ->
    (* [LetCode-β] Non-recursive case
       let code f (x, ρ, res_k, exn_k) = e1 in e2 ⟶ e2 [f \ λ (x, ρ, res_k, exn_k). e1] *)
    subst_pattern ~bound:x ~let_body:e1 e2
  | Named (Static_consts (a :: l)) ->
    (* [LetCode-β] Recursive case
       Static variables may bind mutually recursive objects
       (e.g. a (mutually recursive) list of code blocks and a set of closure
       definition that indicates the closure of each code block).

       To resolve the set of closures, we do a two-stage substitution:

       First, we copy in a the content of the let-bound static code blocks
       into the set of closures definition.

       (Normalization for let-static declarations)
       [LetStatic-β]
       let code rec f1 (x) = body ... and set_of_clo K = closures ->
       let code rec f1 (x) = body ... and set_of_clo K = closures[f1\body]

       Then, we perform a pointwise [Let-β] (per usual) over the list of bound
       variables. *)

    (* [LetStatic-β] *)
    let e1 = normalize_let_static ~bound:x ~static_consts:(a :: l)
    in
    (* [Let-β] *)
    subst_pattern ~bound:x ~let_body:e1 e2
  | _ ->
      (* [LetL]
                      e1 ⟶ e1'
        -------------------------------------
         let x = e1 in e2 ⟶ let x = e1' in e2 *)
      let e1 = normalize env e1 in
      (* [Let-β]
         let x = v in e1 ⟶ e2 [x\v] *)
      subst_pattern ~bound:x ~let_body:e1 e2

(* FIXME : This is buggy *)
and normalize_let_static ~bound ~static_consts =
  List.fold_left
  (fun acc (id, const) ->
      match acc, const, id with
      | Named acc,
        Static_const (Static_set_of_closures _),
        Bound_static.Pattern.Set_of_closures set ->
        subst_bound_set_of_closures set ~let_body:(Named (Static_consts [const])) acc
      | _ -> acc)
  (Named (Static_consts static_consts))
  (List.combine (Bound_pattern.must_be_static bound |> Bound_static.to_list)
      static_consts)

and normalize_let_cont _env (e:let_cont_expr) : core_exp =
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

and normalize_apply _env callee continuation exn_continuation apply_args call_kind
  : core_exp =
  match callee with
  | Named (Static_consts [Code code]) ->
    let slot_bound, slot_body =
      Core_function_params_and_body.pattern_match
        code  ~f:(fun bff t -> bff, t)
    in
    let renaming = Renaming.empty
    in
    let renaming =
      (match continuation with
      | Apply_expr.Result_continuation.Return continuation ->
          Renaming.add_continuation renaming
            (Bound_for_function.return_continuation slot_bound)
            continuation
      | _ -> renaming)
    in
    let renaming =
      Renaming.add_continuation renaming
        (Bound_for_function.exn_continuation slot_bound)
        exn_continuation
    in
    let exp =
      apply_renaming slot_body renaming
    in
    subst_params (Bound_for_function.params slot_bound) exp
      (List.map (normalize (Env.create ())) apply_args)
  | _ ->
    Apply {callee;continuation;
           exn_continuation;apply_args;call_kind}

and normalize_apply_cont env k args : core_exp =
  (* [ApplyCont]
            args ⟶ args'
      --------------------------
          k args ⟶ k args'       *)
  Apply_cont {k = k; args = List.map (normalize env) args}

and normalize_static_const env (const : static_const) : static_const =
  match const with
  | Static_set_of_closures set ->
    Static_set_of_closures (normalize_set_of_closures env set)
  | Block (tag, mut, list) ->
    Block (tag, mut, List.map (normalize env) list)
  | (Boxed_float _ | Boxed_int32 _ | Boxed_int64 _ | Boxed_nativeint _
    | Immutable_float_block _ | Immutable_float_array _ | Immutable_value_array _
    | Empty_array | Mutable_string _ | Immutable_string _) -> const (* CHECK *)

and normalize_static_const_or_code env (const_or_code : static_const_or_code)
  : static_const_or_code =
  match const_or_code with
  | Code code ->
    let (param, body) =
      Core_function_params_and_body.pattern_match
        code  ~f:(fun x y -> x, y)
    in
    let params_and_body =
      Core_function_params_and_body.create param (normalize env body)
    in
    Code params_and_body
  | Static_const const -> Static_const (normalize_static_const env const)
  | Deleted_code -> Deleted_code

and normalize_static_const_group env (consts : static_const_group) : core_exp =
  Named (Static_consts (List.map (normalize_static_const_or_code env) consts))

(* N.B. This normalization is rather inefficient; it goes through three passes of
  the value and function expressions *)
and normalize_set_of_closures env {function_decls; value_slots; alloc_mode}
  : set_of_closures =
  let value_slots =
    Value_slot.Map.map
      (fun (val_expr, kind) -> (normalize_value_expr env val_expr, kind))
      value_slots
  in
  (* substituting in value slots for [Project_value_slots] *)
  let in_order =
    Function_slot.Lmap.map
      (fun x ->
         match x with
         | Exp (Named (Static_consts [Code code]))->
           let params_and_body =
             subst_my_closure
               code
              {function_decls;value_slots;alloc_mode}
           in
           Exp (Named (Static_consts [Code params_and_body]))
         | _ -> x)
      function_decls.in_order
  in
  (* normalize function slots
     NOTE : This might need to change when we're dealing with effectful functions*)
  let in_order =
    Function_slot.Lmap.map (normalize_function_expr env) in_order
  in
  { function_decls =
      { funs =
          Function_slot.Map.of_list (Function_slot.Lmap.bindings in_order);
        in_order}
  ; value_slots = Value_slot.Map.empty
  ; alloc_mode = alloc_mode }

(* N.B. [PROJECTION REDUCTION]
    When we substitute in a set of closures for primitives,
    (Here is where the `Projection` primitives occur),
    we eliminate the projection. *)
and subst_my_closure
    (fn_expr : function_params_and_body)
    (clo : set_of_closures) : function_params_and_body =
  let param, body =
    Core_function_params_and_body.pattern_match ~f:(fun x y -> x, y) fn_expr
  in
  let body = subst_my_closure_body clo body
  in
  Core_function_params_and_body.create param body

and subst_my_closure_body (clo: set_of_closures) (e : core_exp) : core_exp =
  match e with
  | Named e ->
    subst_my_closure_body_named clo e
  | Let {let_abst; expr_body} ->
     Core_let.pattern_match {let_abst; expr_body}
       ~f:(fun ~x ~e1 ~e2 ->
          Core_let.create
            ~x
            ~e1:(subst_my_closure_body clo e1)
            ~e2:(subst_my_closure_body clo e2))
  | Let_cont (Non_recursive {handler; body}) ->
    let handler =
      Core_continuation_handler.pattern_match handler
        (fun param exp ->
           Core_continuation_handler.create param
             (subst_my_closure_body clo exp))
    in
    let body =
      Core_letcont_body.pattern_match body
        (fun cont exp ->
           Core_letcont_body.create cont
             (subst_my_closure_body clo exp))
    in
    Let_cont (Non_recursive {handler; body})
  | Let_cont (Recursive _) ->
    failwith "Unimplemented subst_pattern_set_of_closures: Let_cont recursive case"
  | Apply {callee; continuation; exn_continuation; apply_args; call_kind} ->
    Apply
      {callee = subst_my_closure_body clo callee;
       continuation; exn_continuation;
       apply_args =
         List.map (subst_my_closure_body clo) apply_args;
       call_kind}
  | Apply_cont {k;args} ->
    Apply_cont
      { k = k;
        args = List.map (subst_my_closure_body clo) args }
  | Switch {scrutinee; arms} ->
    Switch
      { scrutinee = subst_my_closure_body clo scrutinee;
        arms = Targetint_31_63.Map.map (subst_my_closure_body clo) arms; }
  | Invalid _ -> e

and subst_my_closure_body_named
    ({function_decls=_;value_slots;alloc_mode=_}: set_of_closures) (e : named)
  : core_exp =
  match e with
  | Prim
      (Unary (Project_value_slot slot, _arg)) ->
    (match Value_slot.Map.find_opt slot.value_slot value_slots with
     | Some (Value_exp (Named (Set_of_closures clo)), _) ->
       let fun_decls = clo.function_decls.in_order
       in
       (match Function_slot.Lmap.get_singleton fun_decls with
        (* TODO: Is it necessary to rename my_closure? *)
        | Some (_, Exp e) -> e
        | _ -> Named e)
     | _ -> Named e)
  | _ -> Named e

and normalize_function_expr env (fun_expr : function_expr) : function_expr =
  match fun_expr with
  | Id _ -> fun_expr
  | Exp exp -> Exp (normalize env exp)

and normalize_value_expr env (val_expr : value_expr) : value_expr =
  match val_expr with
  | Simple_value _ -> val_expr
  | Value_exp exp -> Value_exp (normalize env exp)

(* This is a "normalization" of [named] expression, in quotations because there
  is some simple evaluation that occurs for primitive arithmetic expressions *)
and normalize_named env (body : named) : core_exp =
  match body with
  | Simple _ (* A [Simple] is a register-sized value *)
  | Rec_info _ (* Information about inlining recursive calls, an integer variable *) ->
    Named (body)
  | Closure_expr (slot, set) ->
    Named (Closure_expr (slot, normalize_set_of_closures env set))
  | Set_of_closures set -> (* Map of [Code_id]s and [Simple]s corresponding to
                         function and value slots*)
    Named (Set_of_closures (normalize_set_of_closures env set))
  | Static_consts consts -> (* [Static_consts] are statically-allocated values *)
    normalize_static_const_group env consts
  | Prim v -> eval_prim env v

let simulation_relation src tgt =
  let {Simplify.unit = tgt; _} = tgt in
  let src_core = Flambda_unit.body src |> flambda_expr_to_core in
  let tgt_core = Flambda_unit.body tgt |> flambda_expr_to_core in
  Equiv.core_eq src_core tgt_core

(** Top-level validator *)
let validate ~cmx_loader ~round src =
  let tgt = Simplify.run ~cmx_loader ~round src in
  simulation_relation src tgt
