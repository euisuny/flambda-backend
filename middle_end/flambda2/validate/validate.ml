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
let rec subst_pattern ~(bound : Bound_for_let.t) ~(let_body : core_exp) (e : core_exp)
  : core_exp =
  match bound with
  | Singleton bound ->
    (match let_body with
     | Named (Set_of_closures clo) ->
       subst_singleton_set_of_closures ~bound ~clo e
     | _ ->
        core_fmap
          (fun (bound, let_body) s ->
            let bound = Simple.var (Bound_var.var bound) in
            if (Simple.equal s bound) then let_body else Named (Simple s))
          (bound, let_body) e)
  | Static bound ->
    subst_static_list ~bound ~let_body e

and subst_singleton_set_of_closures ~(bound: Bound_var.t) ~(clo : set_of_closures)
      (e : core_exp) : core_exp =
  match e with
  | Named e -> subst_singleton_set_of_closures_named ~bound ~clo e
  | Let {let_abst; expr_body} ->
    Core_let.pattern_match {let_abst; expr_body}
      ~f:(fun ~x ~e1 ~e2 ->
        Core_let.create
          ~x
          ~e1:(subst_singleton_set_of_closures ~bound ~clo e1)
          ~e2:(subst_singleton_set_of_closures ~bound ~clo e2))
  | Let_cont (Non_recursive {handler; body}) ->
    (let handler =
      Core_continuation_handler.pattern_match handler
        (fun param exp ->
           Core_continuation_handler.create param
             (subst_singleton_set_of_closures ~bound ~clo exp))
    in
    let body =
      Core_letcont_body.pattern_match body
        (fun cont exp ->
          Core_letcont_body.create cont
            (subst_singleton_set_of_closures ~bound ~clo exp))
    in
    Let_cont (Non_recursive {handler; body}))
  | Let_cont (Recursive body) ->
    (let bound_k, continuation_map, body =
      Core_recursive.pattern_match body ~f:(fun b {continuation_map; body} ->
        b, continuation_map, body)
    in
    let bound_cm, continuation_map =
      Core_continuation_map.pattern_match continuation_map
        ~f:(fun b e -> b,e)
    in
    let continuation_map =
      Continuation.Map.map
        (fun x ->
            Core_continuation_handler.pattern_match x
                (fun param exp ->
                    Core_continuation_handler.create param
                      (subst_singleton_set_of_closures ~bound ~clo exp))) continuation_map
    in
    let body = subst_singleton_set_of_closures ~bound ~clo body
    in
    let body =
      Core_recursive.create bound_k
        {continuation_map = Core_continuation_map.create bound_cm continuation_map;
         body}
    in
    Let_cont (Recursive body))
  | Apply
      {callee; continuation; exn_continuation; apply_args; call_kind} ->
    Apply
      {callee = subst_singleton_set_of_closures ~bound ~clo callee;
       continuation; exn_continuation;
       apply_args =
         List.map (subst_singleton_set_of_closures ~bound ~clo) apply_args;
       call_kind}
  | Apply_cont {k; args} ->
    Apply_cont
      {k = k;
       args = List.map (subst_singleton_set_of_closures ~bound ~clo) args}
  | Lambda e ->
    Core_lambda.pattern_match e
      ~f:(fun b e ->
        Lambda (Core_lambda.create b (subst_singleton_set_of_closures ~bound ~clo e)))
  | Switch {scrutinee; arms} ->
    Switch
      {scrutinee = subst_singleton_set_of_closures ~bound ~clo scrutinee;
       arms = Targetint_31_63.Map.map (subst_singleton_set_of_closures ~bound ~clo) arms}
  | Invalid _ -> e

and subst_singleton_set_of_closures_named ~bound ~clo (e : named) : core_exp =
  match e with
  | Simple v ->
    if Simple.same v (Simple.var (Bound_var.var bound)) then
      Named (Set_of_closures clo)
    else
      Named e
  | Prim (Nullary _) -> Named e
  | Prim (Unary (p, e)) ->
    Named (Prim (Unary (p, subst_singleton_set_of_closures ~bound ~clo e)))
  | Prim (Binary (p, e1, e2)) ->
    Named (Prim (Binary
                   (p,
                    subst_singleton_set_of_closures ~bound ~clo e1,
                    subst_singleton_set_of_closures ~bound ~clo e2)))
  | Prim (Ternary (p, e1, e2, e3)) ->
    Named (Prim (Ternary (p,
                          subst_singleton_set_of_closures ~bound ~clo e1,
                          subst_singleton_set_of_closures ~bound ~clo e2,
                          subst_singleton_set_of_closures ~bound ~clo e3)))
  | Prim (Variadic (p, list)) ->
    Named (Prim (Variadic (p, List.map (subst_singleton_set_of_closures ~bound ~clo) list)))
  | Closure_expr (phi, slot, {function_decls; value_slots; alloc_mode}) ->
    let {function_decls; value_slots; alloc_mode} =
      (let in_order =
        Function_slot.Lmap.map (fun x ->
          match x with
          | Id _ -> x
          | Exp e -> Exp (subst_singleton_set_of_closures ~bound ~clo e))
          function_decls.in_order
      in
      let function_decls = function_decl_create in_order
      in
      let value_slots =
        Value_slot.Map.map (fun (x, kind) ->
          match x with
          | Id v -> (Exp (
            if Simple.same v (Simple.var (Bound_var.var bound)) then
              Named (Set_of_closures clo)
            else
              Named e), kind)
          | Exp e -> (Exp (subst_singleton_set_of_closures ~bound ~clo e), kind)) value_slots
      in
      {function_decls; value_slots; alloc_mode})
    in
    Named (Closure_expr (phi, slot, {function_decls; value_slots; alloc_mode}))
  | Set_of_closures {function_decls; value_slots; alloc_mode}->
    let {function_decls; value_slots; alloc_mode} =
      let in_order =
        Function_slot.Lmap.map (fun x ->
          match x with
          | Id _ -> x
          | Exp e -> Exp (subst_singleton_set_of_closures ~bound ~clo e)) function_decls.in_order
      in
      let function_decls = function_decl_create in_order
      in
      let value_slots =
        Value_slot.Map.map (fun (x, kind) ->
          match x with
          | Id v -> (Exp (
            if Simple.same v (Simple.var (Bound_var.var bound)) then
              Named (Set_of_closures clo)
            else
              Named e), kind)
          | Exp e -> (Exp (subst_singleton_set_of_closures ~bound ~clo e), kind)) value_slots
      in
      {function_decls; value_slots; alloc_mode}
    in
    Named (Set_of_closures {function_decls; value_slots; alloc_mode})
  | Static_consts group ->
    Named (Static_consts (List.map (subst_singleton_set_of_closures_static_const_or_code ~bound ~clo) group))
  | Slot (phi, Function_slot slot) ->
    (let bound = Function_slot.Lmap.bindings clo.function_decls.in_order
    in
    (* try to find if any of the symbols being bound is the same as the variable v *)
    let bound_closure =
      List.find_opt (fun (x, _) -> x = slot) bound
    in
    (match bound_closure with
      | None -> Named e
      | Some (k, _) -> Named (Closure_expr (phi, k, clo))))
  | Slot _
  | Rec_info _ -> Named e

and subst_singleton_set_of_closures_static_const_or_code ~bound ~clo
      (e : static_const_or_code) =
  match e with
  | Code params_and_body ->
    Code
      (Core_function_params_and_body.pattern_match
         params_and_body
         ~f:(fun
              params body ->
              Core_function_params_and_body.create
                params
                (Core_lambda.pattern_match body
                   ~f:(fun bound body ->
                     Core_lambda.create bound
                       (subst_singleton_set_of_closures ~bound:params ~clo body)))))
  | Deleted_code -> e
  | Static_const const ->
    Static_const (match const with
     | Static_set_of_closures {function_decls; value_slots; alloc_mode}->
      let {function_decls; value_slots; alloc_mode} =
        (
          let in_order =
            Function_slot.Lmap.map (fun x ->
              match x with
              | Id _ -> x
              | Exp e -> Exp (subst_singleton_set_of_closures ~bound ~clo e)) function_decls.in_order
          in
          let function_decls = function_decl_create in_order
          in
          let value_slots =
            Value_slot.Map.map (fun (x, kind) ->
              match x with
              | Id v -> (Exp (
                if Simple.same v (Simple.var (Bound_var.var bound)) then
                  Named (Set_of_closures clo)
                else
                  Named (Static_consts [e])), kind)
              | Exp e -> (Exp (subst_singleton_set_of_closures ~bound ~clo e), kind)) value_slots
          in
          {function_decls; value_slots; alloc_mode}
        )
      in
      Static_set_of_closures {function_decls; value_slots; alloc_mode}
    | Block (tag, mut, list) ->
      let list = List.map (subst_singleton_set_of_closures ~bound ~clo) list
      in
      Block (tag, mut, list)
    | _ -> const)

and subst_static_list ~(bound : Bound_codelike.t) ~let_body e : core_exp =
  let rec subst_static_list_ bound body e =
    (match bound, body with
     | [], [] -> e
     | hd :: tl, let_body :: body ->
       subst_static_list_ tl body
         (subst_pattern_static ~bound:hd ~let_body e)
     | _, _ ->
      failwith "Mismatched static binder and let body length")
  in
  match let_body with
  | Named (Static_consts consts_list) ->
    let (body : core_exp list) =
      List.map (fun x -> Named (Static_consts [x])) consts_list
    in
    subst_static_list_ (Bound_codelike.to_list bound) body e
  | _ -> failwith "Expected name static constants in let body"

and subst_pattern_static
      ~(bound : Bound_codelike.Pattern.t) ~(let_body : core_exp) (e : core_exp) : core_exp =
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
  | Lambda e ->
    Core_lambda.pattern_match e
      ~f:(fun b e ->
        Lambda (Core_lambda.create
          b
          (subst_pattern_static ~bound ~let_body e)))
  | Invalid _ -> e

(* [Set of closures]
   Given the code for its functions and closure variables, the set of closures
    keeps track of the mapping between them.
   i.e. it is the code generated by
    [let f = closure f_0 @f] where [@f] is the function slot and [f_0] refers
    to the code *)
and subst_bound_set_of_closures (bound : Bound_var.t) ~let_body
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
          if Simple.same v (Simple.var (Bound_var.var bound)) then
            Named (Static_consts [Static_const (Static_set_of_closures set)])
          else Named e
        | Some _ -> failwith "Cannot be reached"
        | None -> Named e)
     | _ -> Named e
    )
  | Prim (Nullary e) -> Named (Prim (Nullary e))
  | Prim (Unary (e, arg1)) ->
    let arg1 =
      subst_pattern_static
        ~bound:(Bound_codelike.Pattern.set_of_closures bound) ~let_body arg1
    in
    Named (Prim (Unary (e, arg1)))
  | Prim (Binary (e, arg1, arg2)) ->
    let arg1 =
      subst_pattern_static
        ~bound:(Bound_codelike.Pattern.set_of_closures bound) ~let_body arg1
    in
    let arg2 =
      subst_pattern_static
        ~bound:(Bound_codelike.Pattern.set_of_closures bound) ~let_body arg2
    in
    Named (Prim (Binary (e, arg1, arg2)))
  | Prim (Ternary (e, arg1, arg2, arg3)) ->
    let arg1 =
      subst_pattern_static
        ~bound:(Bound_codelike.Pattern.set_of_closures bound) ~let_body arg1
    in
    let arg2 =
      subst_pattern_static
        ~bound:(Bound_codelike.Pattern.set_of_closures bound) ~let_body arg2
    in
    let arg3 =
      subst_pattern_static ~bound:(Bound_codelike.Pattern.set_of_closures bound) ~let_body arg3
    in
    Named (Prim (Ternary (e, arg1, arg2, arg3)))
  | Prim (Variadic (e, args)) ->
    let args =
      List.map
        (subst_pattern_static ~bound:(Bound_codelike.Pattern.set_of_closures bound) ~let_body) args
    in
    Named (Prim (Variadic (e, args)))
  | Static_consts e ->
    subst_bound_set_of_closures_static_const_group ~bound ~let_body e
  | Slot (phi, Function_slot slot) ->
    (match let_body with
     | Named (Static_consts consts) ->
        let set =
          List.find_opt
            (fun x ->
                match x with
                | Static_const (Static_set_of_closures _) -> true
                | _ -> false) consts
        in
        (match set with
          | Some (Static_const (Static_set_of_closures set)) ->
            let bound = Function_slot.Lmap.bindings set.function_decls.in_order
            in
            (* try to find if any of the symbols being bound is the same as the variable v *)
            let bound_closure =
              List.find_opt (fun (x, _) -> x = slot) bound
            in
            (match bound_closure with
             | None -> Named e
             | Some (k, _) -> Named (Closure_expr (phi, k, set)))
          | Some _ -> failwith "Cannot be reached"
          | None -> Named e)
     | _ -> Named e
    )
  | Slot _ |  Closure_expr _ ->
    Named e (* NEXT : Substitute in the value slots *)
  | Set_of_closures _ ->
    failwith "Unimplemented_set_of_closures"
  | Rec_info _ ->
    failwith "Unimplemented_block_like"

and subst_bound_set_of_closures_static_const_group
      ~bound ~(let_body : core_exp) (e : static_const_group) : core_exp =
  Named (Static_consts
           (List.map (subst_bound_set_of_closures_static_const_or_code ~bound ~let_body) e))

and subst_bound_set_of_closures_static_const_or_code
      ~(bound : Bound_var.t)
      ~(let_body : core_exp) (e : static_const_or_code) : static_const_or_code =
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
                (Core_lambda.pattern_match body
                   ~f:(fun bound body ->
                     Core_lambda.create bound
                       (subst_pattern_static
                          ~bound:(Bound_codelike.Pattern.set_of_closures params)
                          ~let_body body
                       )))))
  | Deleted_code -> e

and subst_bound_set_of_closures_static_const
      ~(bound : Bound_var.t) ~(let_body : core_exp) (e : static_const) : static_const =
  match e with
  | Block (tag, mut, args) ->
    let args =
      List.map
        (subst_pattern_static ~bound:(Bound_codelike.Pattern.set_of_closures bound) ~let_body)
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
                     ~bound:(Bound_codelike.Pattern.set_of_closures bound)
                     ~let_body e))
     in
     let function_decls =
       { funs = Function_slot.Map.of_list (Function_slot.Lmap.bindings in_order);
         in_order }
     in
     (Static_set_of_closures {function_decls; value_slots; alloc_mode}))
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
              Exp (subst_pattern_static ~bound:(Bound_codelike.Pattern.code bound)
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
        ~bound:(Bound_codelike.Pattern.code bound) ~let_body arg1
    in
    Named (Prim (Unary (e, arg1)))
  | Prim (Binary (e, arg1, arg2)) ->
    let arg1 =
      subst_pattern_static
        ~bound:(Bound_codelike.Pattern.code bound) ~let_body arg1
    in
    let arg2 =
      subst_pattern_static
        ~bound:(Bound_codelike.Pattern.code bound) ~let_body arg2
    in
    Named (Prim (Binary (e, arg1, arg2)))
  | Prim (Ternary (e, arg1, arg2, arg3)) ->
    let arg1 =
      subst_pattern_static
        ~bound:(Bound_codelike.Pattern.code bound) ~let_body arg1
    in
    let arg2 =
      subst_pattern_static
        ~bound:(Bound_codelike.Pattern.code bound) ~let_body arg2
    in
    let arg3 =
      subst_pattern_static ~bound:(Bound_codelike.Pattern.code bound) ~let_body arg3
    in
    Named (Prim (Ternary (e, arg1, arg2, arg3)))
  | Prim (Variadic (e, args)) ->
    let args =
      List.map
        (subst_pattern_static ~bound:(Bound_codelike.Pattern.code bound) ~let_body) args
    in
    Named (Prim (Variadic (e, args)))
  | Slot _ -> Named e (* NEXT *)
  | Closure_expr (phi, slot, set) ->
    Named (Closure_expr (phi, slot, subst_code_id_set_of_closures bound ~let_body set))
  | Set_of_closures set ->
    let set = subst_code_id_set_of_closures bound ~let_body set
    in
    Named (Set_of_closures set)
  | Static_consts [Static_const (Block (tag, immutable, exps))] ->
    let exps =
      List.map
        (subst_pattern_static ~bound:(Bound_codelike.Pattern.code bound) ~let_body) exps
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
                      Exp (subst_pattern_static ~bound:(Bound_codelike.Pattern.code bound)
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

and subst_block_like
      ~(bound : Symbol.t) ~(let_body : core_exp) (e : named) : core_exp =
  match e with
  | Simple v ->
    if Simple.equal v (Simple.symbol bound) then let_body else Named e
  | Prim (Nullary e) -> Named (Prim (Nullary e))
  | Prim (Unary (e, arg1)) ->
    let arg1 =
      subst_pattern_static ~bound:(Bound_codelike.Pattern.block_like bound) ~let_body arg1
    in
    Named (Prim (Unary (e, arg1)))
  | Prim (Binary (e, arg1, arg2)) ->
    let arg1 =
      subst_pattern_static ~bound:(Bound_codelike.Pattern.block_like bound) ~let_body arg1
    in
    let arg2 =
      subst_pattern_static ~bound:(Bound_codelike.Pattern.block_like bound) ~let_body arg2
    in
    Named (Prim (Binary (e, arg1, arg2)))
  | Prim (Ternary (e, arg1, arg2, arg3)) ->
    let arg1 =
      subst_pattern_static ~bound:(Bound_codelike.Pattern.block_like bound) ~let_body arg1
    in
    let arg2 =
      subst_pattern_static ~bound:(Bound_codelike.Pattern.block_like bound) ~let_body arg2
    in
    let arg3 =
      subst_pattern_static ~bound:(Bound_codelike.Pattern.block_like bound) ~let_body arg3
    in
    Named (Prim (Ternary (e, arg1, arg2, arg3)))
  | Prim (Variadic (e, args)) ->
    let args =
      List.map (subst_pattern_static ~bound:(Bound_codelike.Pattern.block_like bound) ~let_body) args
    in
    Named (Prim (Variadic (e, args)))
  | Static_consts l ->
    subst_block_like_static_const_group ~bound ~let_body l
  | Slot _ | Closure_expr _ ->
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
        (subst_pattern_static ~bound:(Bound_codelike.Pattern.block_like bound) ~let_body)
        args
    in
    Block (tag, mut, args)
  | _ -> e (* NEXT *)

(* ∀ p i, p ∈ params -> params[i] = p -> e [p \ args[i]] *)
(* [Bound_parameters] are [Variable]s *)
let subst_params
  (params : Bound_parameters.t) (e : core_exp) (args : core_exp list) =
  let param_list =
    Bound_parameters.to_list params |> List.map Bound_parameter.simple
  in
  let param_args = List.combine param_list args in
  core_fmap
    (fun () s ->
      match List.assoc_opt s param_args with
      | Some arg_v -> arg_v
      | None -> Named (Simple s)) () e

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
  | Let_cont (Non_recursive {handler; body})->
    let handler =
      Core_continuation_handler.pattern_match handler
        (fun param exp ->
           Core_continuation_handler.create param
             (subst_cont exp k args cont_e2))
    in
    let body =
      Core_letcont_body.pattern_match body
        (fun cont exp ->
           Core_letcont_body.create cont
             (subst_cont exp k args cont_e2))
    in
    Let_cont (Non_recursive {handler; body})
  | Let_cont (Recursive _) ->
    failwith "Unimplemented subst cont recursive case"
  | Apply {callee; continuation; exn_continuation; apply_args; call_kind} ->
    let continuation =
      (match continuation with
      | Cont_id (Return cont) ->
        if Continuation.equal cont k
        then Handler (Core_continuation_handler.create args cont_e2)
        else continuation
      | _ -> continuation)
    in
    let exn_continuation =
      (match exn_continuation with
       | Cont_id cont ->
         if Continuation.equal cont k
         then Handler (Core_continuation_handler.create args cont_e2)
         else exn_continuation
       | _ -> exn_continuation)
    in
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
  | Lambda _ ->
    failwith "Unimplemented subst_cont: Lambda"
  | Switch {scrutinee; arms} ->
    Switch
      {scrutinee = subst_cont scrutinee k args cont_e2;
       arms = Targetint_31_63.Map.map (fun x -> subst_cont x k args cont_e2) arms;}
  | Invalid _ -> cont_e1

let eval_prim_nullary (_v : P.nullary_primitive) : named =
  failwith "eval_prim_nullary"

let eval_prim_unary (v : P.unary_primitive) (_arg : core_exp) : named =
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
     | _, _ -> Named (Prim (Binary (v, arg1, arg2))))
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
  | Float_comp _ -> Named (Prim (Binary (v, arg1, arg2)))

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

let eval_prim (v : primitive) : core_exp =
  match v with
  | Nullary v -> Named (eval_prim_nullary v)
  | Unary (v, arg) -> Named (eval_prim_unary v arg)
  | Binary (v, arg1, arg2) -> eval_prim_binary v arg1 arg2
  | Ternary (v, arg1, arg2, arg3) -> Named (eval_prim_ternary v arg1 arg2 arg3)
  | Variadic (v, args) -> Named (eval_prim_variadic v args)

let rec normalize (e:core_exp) : core_exp =
  match e with
  | Let { let_abst; expr_body } ->
    normalize_let let_abst expr_body
    |> normalize
  | Let_cont e ->
    normalize_let_cont e
    |> normalize
  | Apply {callee; continuation; exn_continuation; apply_args; call_kind} ->
    normalize_apply callee continuation exn_continuation apply_args call_kind
  | Apply_cont {k ; args} ->
    (* The recursive call for [apply_cont] is done for the arguments *)
    normalize_apply_cont k args
  | Lambda e ->
    Core_lambda.pattern_match e
      ~f:(fun x e ->
        Lambda (Core_lambda.create x (normalize e)))
  | Switch {scrutinee; arms} -> (* TODO *)
    Switch {scrutinee = normalize scrutinee; arms}
  | Named (Closure_expr (phi, slot, clo)) ->
    let var = Bound_for_let.Singleton (Bound_var.create phi Name_mode.normal)
    in
    Named (Closure_expr (phi, slot, normalize_set_of_closures var clo))
  | Named _
  | Invalid _ -> e

and normalize_let let_abst body : core_exp =
  let x, e1, e2 =
    Core_let.pattern_match {let_abst; expr_body = body}
      ~f:(fun ~x ~e1 ~e2 -> (x, e1, e2))
  in
  match body with
  | Named (Static_consts [Code _]) ->
    (* [LetCode-β] Non-recursive case
       let code f (x, ρ, res_k, exn_k) = e1 in e2 ⟶ e2 [f \ λ (x, ρ, res_k, exn_k). e1] *)
    subst_pattern ~bound:x ~let_body:e1 e2
  | _ ->
      (* [LetL]
                      e1 ⟶ e1'
        -------------------------------------
         let x = e1 in e2 ⟶ let x = e1' in e2 *)
      let x, e1 =
        (match e1 with
        | Named e -> normalize_named x e
        | _ -> x, normalize e1)
      in
      (* [Let-β]
         let x = v in e1 ⟶ e2 [x\v] *)
      subst_pattern ~bound:x ~let_body:e1 e2

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
    (match e1 with
    | Apply _ -> Let_cont (Non_recursive {handler; body})
    | _ -> subst_cont e1 k args e2)
  | Recursive _handlers -> failwith "Unimplemented_recursive"

(* TODO: substitute in continuation and exn_continuations (if it has in-lined
          handlers) *)
and normalize_apply callee continuation exn_continuation apply_args call_kind
  : core_exp =
  match callee with
  | Named (Static_consts [Code code]) ->
    let _, lambda_expr =
      Core_function_params_and_body.pattern_match
        code  ~f:(fun phi t -> phi, t)
    in
    let bound, body =
      Core_lambda.pattern_match lambda_expr
        ~f:(fun b body -> b, body)
    in
    let return_continuation2 = bound.return_continuation
    in
    let exn_continuation2 = bound.exn_continuation
    in
    let params = bound.params
    in
    let renaming = Renaming.empty
    in
    let renaming =
      (match continuation with
      | Cont_id (Apply_expr.Result_continuation.Return continuation) ->
          Renaming.add_continuation renaming
            return_continuation2
            continuation
      | _ -> renaming)
    in
    let renaming =
      (match exn_continuation with
       | Cont_id continuation ->
         Renaming.add_continuation renaming
           exn_continuation2
           continuation
       | _ -> renaming)
    in
    let exp =
      apply_renaming body renaming
    in
    subst_params params exp
      (List.map normalize apply_args)
  | Lambda exp ->
    let bound, exp =
      Core_lambda.pattern_match exp ~f:(fun x y -> x,y)
    in
    let renaming = Renaming.empty
    in
    let renaming =
      (match continuation with
       | Cont_id (Apply_expr.Result_continuation.Return continuation) ->
         Renaming.add_continuation renaming
           (bound.return_continuation)
           continuation
       | _ -> renaming)
    in
    let renaming =
      (match exn_continuation with
       | Cont_id exn_continuation ->
         Renaming.add_continuation renaming
           (bound.exn_continuation)
           exn_continuation
       | _ -> renaming)
    in
    let exp =
      apply_renaming exp renaming
    in
    subst_params (bound.params) exp
      (List.map normalize apply_args)
  | _ ->
    Apply {callee;continuation;
           exn_continuation;apply_args;call_kind}

and normalize_apply_cont k args : core_exp =
  (* [ApplyCont]
            args ⟶ args'
      --------------------------
          k args ⟶ k args'       *)
  Apply_cont {k = k; args = List.map normalize args}

and normalize_static_const (phi : Bound_for_let.t) (const : static_const) : static_const =
  match const with
  | Static_set_of_closures set ->
    Static_set_of_closures (normalize_set_of_closures phi set)
  | Block (tag, mut, list) ->
    Block (tag, mut, List.map normalize list)
  | (Boxed_float _ | Boxed_int32 _ | Boxed_int64 _ | Boxed_nativeint _
    | Immutable_float_block _ | Immutable_float_array _ | Immutable_value_array _
    | Empty_array | Mutable_string _ | Immutable_string _) -> const (* CHECK *)

and normalize_static_const_or_code (phi : Bound_for_let.t) (const_or_code : static_const_or_code)
  : static_const_or_code =
  match const_or_code with
  | Code code ->
    let (param, (bound, body)) =
      Core_function_params_and_body.pattern_match
        code  ~f:(fun x y -> x,
                             Core_lambda.pattern_match y ~f:(fun b body -> b, body))
    in
    let params_and_body =
      Core_function_params_and_body.create param
        (Core_lambda.create bound (normalize body))
    in
    Code params_and_body
  | Static_const const -> Static_const (normalize_static_const phi const)
  | Deleted_code -> Deleted_code

and normalize_static_const_group (phi : Bound_codelike.Pattern.t list) (consts : static_const_group) :
  Bound_codelike.Pattern.t list * core_exp =
  let is_static_set_of_closures =
    (fun e ->
     match e with
     | Static_const (Static_set_of_closures _) -> true
     | _ -> false)
  in
  let is_code =
    (fun e ->
       match e with
       | Code _ -> true
       | _ -> false)
  in
  let phi_consts = List.combine phi consts
  in
  let set_of_closures, static_consts =
    List.partition (fun (_, x) -> is_static_set_of_closures x) phi_consts
  in
  match set_of_closures with
  | [] -> (phi, Named (Static_consts consts))
  | _ ->
    (let code, static_consts =
      List.partition (fun (_, x) -> is_code x) static_consts
    in
    let process_set_of_closures (set : set_of_closures) =
      List.fold_left
        (fun acc (id, x) ->
          match x with
          | Code x ->
            let code_id : Code_id.t =
              (match id with
                | Bound_codelike.Pattern.Code id -> id
                | _ -> failwith "Expected code id")
            in
            let code =
              subst_code_id_set_of_closures code_id
                ~let_body:(Named (Static_consts [Code x])) acc
            in
            code
          | _ -> failwith "Expected code bound") set code
    in
    let set_of_closures =
      List.map
        (fun (phi, x) ->
          match x with
          | Static_const (Static_set_of_closures x) ->
            let phi = Bound_for_let.Static (Bound_codelike.create [phi])
            in
            Static_const (Static_set_of_closures (process_set_of_closures x |>
                                                  normalize_set_of_closures phi))
          | _ -> failwith "Expected set of closures") set_of_closures
    in
    let static_consts =
      List.map (fun (_, x) -> normalize_static_const_or_code
                                (Bound_for_let.Static (Bound_codelike.create phi)) x) static_consts
    in
    let consts = set_of_closures @ static_consts
    in
    let phi =
      List.filter
        (fun x -> match x with
           | Bound_codelike.Pattern.Code _ -> false | _ -> true) phi
    in
    (phi, Named (Static_consts consts)))

(* N.B. This normalization is rather inefficient;
   Right now (for the sake of clarity) it goes through three passes of the
   value and function expressions *)
and normalize_set_of_closures (phi : Bound_for_let.t) {function_decls; value_slots; alloc_mode}
  : set_of_closures =
  let value_slots =
    Value_slot.Map.map
      (fun (val_expr, kind) -> (normalize_value_expr val_expr, kind))
      value_slots
  in
  (* [ClosureVal] and [ClosureFn]
     substituting in value slots for [Project_value_slots] and
     substituting in function slots for [Project_function_slots] *)
  let in_order =
    Function_slot.Lmap.mapi
      (fun slot x ->
         match x with
         | Exp (Named (Static_consts [Code code]))->
           let params_and_body =
             subst_my_closure phi slot
               code
              {function_decls;value_slots;alloc_mode}
           in
           Exp params_and_body (* FIXME: Might want to put [Lambda] as a [Static_const] *)
         | _ -> x)
      function_decls.in_order
  in
  (* normalize function slots
     NOTE (for later):
     This might need to change when we're dealing with effectful functions *)
  let in_order =
    Function_slot.Lmap.map normalize_function_expr in_order
  in
  { function_decls =
      { funs =
          Function_slot.Map.of_list (Function_slot.Lmap.bindings in_order);
        in_order}
  ; value_slots = Value_slot.Map.empty
  ; alloc_mode = alloc_mode }

and subst_my_closure (phi : Bound_for_let.t) (slot : Function_slot.t)
      (fn_expr : function_params_and_body)
      (clo : set_of_closures) : core_exp =
  match phi with
  | Singleton var
  | Static [Set_of_closures var] ->
    (let phi = Bound_var.var var
     in
      Core_function_params_and_body.pattern_match fn_expr
        ~f:(fun bff e ->
          Lambda
            (Core_lambda.pattern_match e
               ~f:(fun bound body ->
                 (* Note: Can't use [Renaming] because it is bidirectional:
                    we only want to substitute in one direction here, namely
                    if we see any occurrence of a [my_closure], substitute in
                    the closure [phi] variable. *)
                 let body =
                   core_fmap
                     (fun _ simple  ->
                        if (Simple.same (Simple.var (Bound_var.var bff)) simple)
                        then Named (Slot (phi, Function_slot slot))
                        else (Named (Simple simple))) () body
                 in
                Core_lambda.create bound
                  (subst_my_closure_body clo body)))))
  | _ -> Named (Static_consts [Code fn_expr])

(* N.B. [PROJECTION REDUCTION]
    When we substitute in a set of closures for primitives,
    (Here is where the `Projection` primitives occur),
    we eliminate the projection. *)
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
  | Lambda _ ->
    failwith "Unimplemented_subst_my_closure_body: Lambda"
  | Switch {scrutinee; arms} ->
    Switch
      { scrutinee = subst_my_closure_body clo scrutinee;
        arms = Targetint_31_63.Map.map (subst_my_closure_body clo) arms; }
  | Invalid _ -> e

(* [ClosureVal] and [ClosureFn] normalization *)
and subst_my_closure_body_named
    ({function_decls=_;value_slots;alloc_mode=_}: set_of_closures) (e : named)
  : core_exp =
  match e with
  | Prim (Unary (Project_value_slot slot, _arg)) ->
    (match Value_slot.Map.find_opt slot.value_slot value_slots with
     | Some (Exp (Named (Closure_expr (_, _, clo))), _) ->
       let fun_decls = clo.function_decls.in_order
       in
       (match Function_slot.Lmap.get_singleton fun_decls with
        | Some (_, Exp e) -> e
        | _ -> Named e)
     | Some (Exp (Named (Set_of_closures clo)), _) ->
       let fun_decls = clo.function_decls.in_order
       in
       (match Function_slot.Lmap.get_singleton fun_decls with
        | Some (_, Exp e) -> e
        | _ -> Named e)
     | _ -> Named e)
  | Prim (Unary (Project_function_slot {move_from ; move_to},
                 Named (Slot (phi, Function_slot slot)))) ->
    if (move_from = slot) then
      Named (Slot (phi, Function_slot move_to))
    else
      Named e
  | _ -> Named e

and normalize_function_expr (fun_expr : function_expr) : function_expr =
  match fun_expr with
  | Id _ -> fun_expr
  | Exp exp -> Exp (normalize exp)

and normalize_value_expr (val_expr : value_expr) : value_expr =
  match val_expr with
  | Id _ -> val_expr
  | Exp exp -> Exp (normalize exp)

(* This is a "normalization" of [named] expression, in quotations because there
  is some simple evaluation that occurs for primitive arithmetic expressions *)
and normalize_named (var: Bound_for_let.t) (body : named) : Bound_for_let.t * core_exp =
  match body with
  | Simple _ (* A [Simple] is a register-sized value *)
  | Slot _
  | Rec_info _ (* Information about inlining recursive calls, an integer variable *) ->
    (var, Named (body))
  | Closure_expr (phi, slot, set) ->
    (var, Named (Closure_expr (phi, slot, normalize_set_of_closures var set)))
  | Set_of_closures set -> (* Map of [Code_id]s and [Simple]s corresponding to
                         function and value slots*)
    (var, Named (Set_of_closures (normalize_set_of_closures var set)))
  | Static_consts consts -> (* [Static_consts] are statically-allocated values *)
    (match var with
     | Static var ->
       let bound_vars = Bound_codelike.to_list var
       in
       let phi, exp = normalize_static_const_group bound_vars consts
       in
       (Static (Bound_codelike.create phi), exp)
     | _ -> failwith "Expected bound static variables")
  | Prim v -> (var, eval_prim v)

let simulation_relation src tgt =
  let {Simplify.unit = tgt; _} = tgt in
  let src_core = Flambda_unit.body src |> flambda_expr_to_core in
  let tgt_core = Flambda_unit.body tgt |> flambda_expr_to_core in
  Equiv.core_eq src_core tgt_core

(** Top-level validator *)
let validate ~cmx_loader ~round src =
  let tgt = Simplify.run ~cmx_loader ~round src in
  simulation_relation src tgt
