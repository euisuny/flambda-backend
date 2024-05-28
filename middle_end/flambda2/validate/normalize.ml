open! Flambda
open! Flambda2_core
open! Translate
open! Equiv

(** Normalization

    - CBV-style reduction for [let] and [letcont] expressions
    - Assumes that the [typeopt/value_kind] flag is [false] *)

(* Hash-consing environment that keeps track of code *)
type code = (Code_id.t, function_params_and_body) Hashtbl.t
let env : code = Hashtbl.create 10

(* The current compilation unit; initialized to dummy unit *)
let comp_unit : Compilation_unit.t ref =
  ref (Compilation_unit.create Compilation_unit.Prefix.empty
         Compilation_unit.Name.dummy)

let rec does_not_occur (v : literal list) acc (exp : core_exp) =
  match descr exp with
  | Invalid _ -> acc
  | Named (Literal l) ->
    ((List.for_all (fun x -> not (literal_contained x l)) v) && acc)
  | Named (Prim _| Closure_expr _ | Set_of_closures _ | Static_consts _
          | Rec_info _) -> acc (* FIXME : do a deep pattern match here *)
  | Let {let_abst; expr_body} ->
    Core_let.pattern_match {let_abst; expr_body}
      ~f:(fun ~x:_ ~e1 ~e2 ->
        does_not_occur v acc e1 && does_not_occur v acc e2)
  | Let_cont {handler; body} ->
    let handler =
      Core_continuation_handler.pattern_match handler
        (fun _ exp -> does_not_occur v acc exp)
    in
    let body =
      Core_letcont_body.pattern_match body
        (fun _ exp -> does_not_occur v acc exp)
    in
    handler && body
  | Apply {callee; continuation; exn_continuation; region; apply_args}->
    does_not_occur v acc callee &&
    does_not_occur v acc continuation &&
    does_not_occur v acc exn_continuation &&
    does_not_occur v acc region &&
    List.fold_left
      (fun acc e -> acc && does_not_occur v acc e) true apply_args
  | Apply_cont {k; args} ->
    does_not_occur v acc k &&
    List.fold_left
      (fun acc e -> acc && does_not_occur v acc e) true args
  | Lambda e ->
    Core_lambda.pattern_match e
      ~f:(fun _ e -> does_not_occur v acc e)
  | Handler handler ->
    Core_continuation_handler.pattern_match handler
         (fun _ exp -> does_not_occur v acc exp)
  | Switch {scrutinee; arms} ->
    does_not_occur v acc scrutinee &&
    Targetint_31_63.Map.fold
      (fun _ x acc -> acc && does_not_occur v acc x) arms true

let literal_var_eq l v =
  (match l with
    | Simple s ->
      let var = Simple.var v in
      Simple.equal s var
    | (Cont _ | Res_cont _ | Slot _ | Code_id _) -> false)

(* Check whether a parameter occurs in an expression other than in argument position *)
let rec parameter_occurs_only_as_call_arg (p : Bound_parameter.t) (e : core_exp) =
  match descr e with
  | Named n -> parameter_occurs_only_as_call_arg_named p n
  | Let e ->
    Core_let.pattern_match e
      ~f:(fun ~x:_ ~e1 ~e2 ->
        parameter_occurs_only_as_call_arg p e1 &&
        parameter_occurs_only_as_call_arg p e2)
  | Let_cont {handler;body} ->
    Core_continuation_handler.pattern_match handler
      (fun _ e ->
        parameter_occurs_only_as_call_arg p e) &&
    Core_letcont_body.pattern_match body
      (fun _ e ->
        parameter_occurs_only_as_call_arg p e)
  | Apply_cont {k ; args} ->
      parameter_occurs_only_as_call_arg p k &&
      List.for_all (fun x ->
          match must_be_literal x with
          | Some _ -> true
          | None -> parameter_occurs_only_as_call_arg p x) args
  | Lambda e ->
      Core_lambda.pattern_match e
        ~f:(fun _ e -> parameter_occurs_only_as_call_arg p e)
  | Handler e ->
      Core_continuation_handler.pattern_match e
       (fun _ e -> parameter_occurs_only_as_call_arg p e)
  | Switch {scrutinee; arms} ->
       parameter_occurs_only_as_call_arg p scrutinee &&
       Targetint_31_63.Map.for_all (fun _ e -> parameter_occurs_only_as_call_arg p e) arms
  | Invalid _ -> false
  | Apply {callee;
      continuation;
      exn_continuation;
      region;
      apply_args} ->
      parameter_occurs_only_as_call_arg p callee &&
      parameter_occurs_only_as_call_arg p continuation &&
      parameter_occurs_only_as_call_arg p exn_continuation &&
      parameter_occurs_only_as_call_arg p region &&
      List.for_all (fun x ->
          match must_be_literal x with
          | Some _ -> true
          | None -> parameter_occurs_only_as_call_arg p x) apply_args

and parameter_occurs_only_as_call_arg_prim p (e : primitive) =
  (match e with
  | Nullary _ -> true
  | Unary (_, e) ->
    parameter_occurs_only_as_call_arg p e
  | Binary (_, e1, e2) ->
    parameter_occurs_only_as_call_arg p e1 &&
    parameter_occurs_only_as_call_arg p e2
  | Ternary (_, e1, e2, e3) ->
    parameter_occurs_only_as_call_arg p e1 &&
    parameter_occurs_only_as_call_arg p e2 &&
    parameter_occurs_only_as_call_arg p e3
  | Variadic (_, list) ->
    List.for_all (parameter_occurs_only_as_call_arg p) list)

and parameter_occurs_only_as_call_arg_named p (e : named) =
  match e with
  | Literal _ -> true
    (* not (literal_var_eq l (Bound_parameter.var p)) *)
  | Prim e -> parameter_occurs_only_as_call_arg_prim p e
  | Closure_expr (_, _, {function_decls; value_slots}) ->
    SlotMap.for_all (fun _ a -> parameter_occurs_only_as_call_arg p a) function_decls &&
    Value_slot.Map.for_all (fun _ a -> parameter_occurs_only_as_call_arg p a) value_slots
  | Set_of_closures {function_decls; value_slots} ->
    SlotMap.for_all (fun _ a -> parameter_occurs_only_as_call_arg p a) function_decls &&
    Value_slot.Map.for_all (fun _ a -> parameter_occurs_only_as_call_arg p a) value_slots
  | Static_consts e ->
    List.for_all
    (fun e ->
      match e with
        | Code {expr; anon=_}->
              Core_function_params_and_body.pattern_match expr
              ~f:(fun
                    _ body ->
                      (Core_lambda.pattern_match body
                        ~f:(fun _ body ->
                             parameter_occurs_only_as_call_arg p body)));
        | Deleted_code -> true
        | Static_const const ->
          (match const with
          | Static_set_of_closures {function_decls; value_slots }->
            SlotMap.for_all (fun _ a -> parameter_occurs_only_as_call_arg p a) function_decls &&
            Value_slot.Map.for_all (fun _ a -> parameter_occurs_only_as_call_arg p a) value_slots
          | Block (_, _, list) ->
              (List.for_all (parameter_occurs_only_as_call_arg p) list)
          | ( Boxed_float _ | Boxed_int32 _ | Boxed_int64 _ | Boxed_nativeint _
            | Immutable_float_block _ | Immutable_float_array _ | Immutable_value_array _
            | Empty_array | Mutable_string _ | Immutable_string _ ) -> true)) e
  | Rec_info _ -> true

let rec eliminate (p : Bound_parameter.t) v (e : core_exp) =
  match Expr.descr e with
  | Named e ->
    named_fix (eliminate p v)
      (fun () x ->
         (* If there is a literal equivalent to the invariant parameter
            in a subexpression, substitute in the concrete value of the
            parameter. *)
         if literal_var_eq x (Bound_parameter.var p) then v
         else Expr.create_named (Literal x)) () e
  | Let e ->
    let_fix (eliminate p v) e
  | Let_cont e ->
    let_cont_fix (eliminate p v) e
  | Apply e ->
    eliminate_apply p v e
  | Apply_cont e ->
    eliminate_apply_cont p v e
  | Lambda e -> lambda_fix (eliminate p v) e
  | Handler e ->
    handler_fix (eliminate p v) e
  | Switch e -> switch_fix (eliminate p v) e
  | Invalid _ -> e

and eliminate_apply (p : Bound_parameter.t) v {callee; continuation; exn_continuation; region; apply_args} =
  (* On the application arguments, remove any exact literal equivalent
    to the invariant parameter. *)
  let apply_args =
    List.filter
      (fun x ->
         match must_be_literal x with
         | Some l -> not (literal_var_eq l (Bound_parameter.var p))
         | None -> true
      ) apply_args
  in
  (* Instantiate any subexpression that contains argument to the concrete value. *)
  let apply_args =
    List.map
      (fun x -> eliminate p v x)
      apply_args
  in
  Expr.create_apply
    {callee = eliminate p v callee ;
     continuation = eliminate p v continuation;
     exn_continuation = eliminate p v exn_continuation;
     region = eliminate p v region;
     apply_args}

and eliminate_apply_cont (p : Bound_parameter.t) v {k; args} =
  let args' =
    List.filter
      (fun x ->
         match must_be_literal x with
         | Some l ->
            not (literal_var_eq l (Bound_parameter.var p))
         | None -> true
      ) args
  in
  let args' =
    List.map
      (fun x -> eliminate p v x)
      args'
  in
  Expr.create_apply_cont
    {k = eliminate p v k; args = args'}

let eliminate_arguments_rec_call (p : Bound_parameter.t) v (e : core_exp) =
  if parameter_occurs_only_as_call_arg p e then
    (true, eliminate p v e)
  else
    (false, e)

(* Substitution funtions for β-reduction *)
(* [Let-β]
      e[bound\let_body] *)
let rec subst_pattern ~(bound : Bound_for_let.t) ~(let_body : core_exp)
          (e : core_exp) : core_exp =
  match bound with
  | Singleton bound ->
    let e = (match must_be_set_of_closures let_body with
     | Some clo ->
       subst_singleton_set_of_closures ~bound:(Bound_var.var bound) ~clo e
     | None ->
        let e =
          core_fmap
          (fun (bound, let_body) s ->
             match s with
             | Simple s ->
                let bound = Simple.var (Bound_var.var bound) in
                if (Simple.equal s bound) then
                  let_body
                else Expr.create_named (Literal (Simple s))
             | (Cont _ | Res_cont _ | Slot _ | Code_id _) ->
               Expr.create_named (Literal s))
          (bound, let_body) e in
          e
    ) in
    e
  | Static bound ->
    subst_static_list ~bound ~let_body e

and subst_singleton_set_of_closures ~(bound: Variable.t)
      ~(clo : set_of_closures) (e : core_exp) : core_exp =
  match descr e with
  | Named e -> subst_singleton_set_of_closures_named ~bound ~clo e
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

and subst_singleton_set_of_closures_named ~bound ~clo (e : named) : core_exp =
  let f bound (v : literal) =
    (match v with
    | Simple v ->
      (if Simple.same v (Simple.var bound) then
         (let {function_decls; value_slots=_} = clo in
          match SlotMap.bindings function_decls with
          | [(slot, _)] ->
              Expr.create_named (Closure_expr (bound, slot, clo))
          | ([]|_::_)->
            Expr.create_named (Set_of_closures clo))
      else
        Expr.create_named (Literal (Simple v)))
    | Slot (phi, Function_slot slot) ->
      (let decls = SlotMap.bindings clo.function_decls in
       let bound_closure = List.find_opt (fun (x, _) -> x = slot) decls in
       (match bound_closure with
        | None -> Expr.create_named e
        | Some (k, _) -> Expr.create_named (Closure_expr (phi, k, clo))
       ))
    | (Cont _ | Res_cont _ | Slot (_, Value_slot _) | Code_id _) ->
      Expr.create_named (Literal v))
  in
  match e with
  | Literal v -> f bound v
  | Prim e -> prim_fix (subst_singleton_set_of_closures ~bound ~clo) e
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
  | Rec_info _ -> Expr.create_named e

and subst_static_list ~(bound : Bound_codelike.t) ~let_body e : core_exp =
  let rec subst_static_list_ bound body e =
    (match bound, body with
     | [], [] -> e
     | hd :: tl, let_body :: body ->
       subst_static_list_ tl body
         (subst_pattern_static ~bound:hd ~let_body e)
     | _, _ ->
      Misc.fatal_error "Mismatched static binder and let body length")
  in
  match must_be_static_consts let_body with
  | Some body ->
    subst_static_list_ (Bound_codelike.to_list bound) body e
  | None -> Misc.fatal_error "Expected name static constants in let body"

and subst_pattern_static
      ~(bound : Bound_codelike.Pattern.t) ~(let_body : static_const_or_code) (e : core_exp)
  : core_exp =
  match Expr.descr e with
  | Let e ->
    let_fix (subst_pattern_static ~bound ~let_body) e
  | Let_cont e ->
    let_cont_fix (subst_pattern_static ~bound ~let_body) e
  | Apply e ->
    apply_fix (subst_pattern_static ~bound ~let_body) e
  | Apply_cont e ->
    apply_cont_fix (subst_pattern_static ~bound ~let_body) e
  | Lambda e ->
    lambda_fix (subst_pattern_static ~bound ~let_body) e
  | Handler e ->
    handler_fix (subst_pattern_static ~bound ~let_body) e
  | Switch e ->
    switch_fix (subst_pattern_static ~bound ~let_body) e
  | Named named ->
    (match bound with
     | Block_like bound ->
       subst_block_like ~bound ~let_body named
     | Set_of_closures set ->
       subst_bound_set_of_closures set ~let_body named
     | Code id ->
       subst_code_id id ~let_body named)
  | Invalid _ -> e

(* [Set of closures]
   Given the code for its functions and closure variables, the set of closures
    keeps track of the mapping between them.
   i.e. it is the code generated by
    [let f = closure f_0 @f] where [@f] is the function slot and [f_0] refers
    to the code *)
and subst_bound_set_of_closures (bound : Bound_var.t) ~(let_body : static_const_or_code)
      (e : named) =
  (match let_body with
   | Static_const const ->
     (match must_be_static_set_of_closures const with
      | Some set -> subst_singleton_set_of_closures_named ~bound:(Bound_var.var bound) ~clo:set e
      | None -> Expr.create_named e)
   | (Deleted_code | Code _) ->
  match e with
  | Literal (Simple v) ->
    (match let_body with
     | Static_const const ->
      (match must_be_static_set_of_closures const with
        | Some set ->
          if Simple.same v (Simple.var (Bound_var.var bound)) then
            Expr.create_named
              (Static_consts [Static_const (Static_set_of_closures set)])
          else Expr.create_named e
        | None -> Expr.create_named e)
     | (Deleted_code | Code _) -> Misc.fatal_error "Cannot be reached")
  | Prim e ->
    prim_fix (subst_pattern_static
                ~bound:(Bound_codelike.Pattern.set_of_closures bound)
                ~let_body) e
  | Static_consts e ->
    static_const_group_fix
      (subst_pattern_static
      ~bound:(Bound_codelike.Pattern.set_of_closures bound)
      ~let_body) e
  | Literal (Slot (phi, Function_slot slot)) ->
    (match let_body with
     | Static_const const ->
        (match must_be_static_set_of_closures const with
        | Some set ->
          let bound = SlotMap.bindings set.function_decls in
          (* try to find if any of the symbols being bound is the same as the
            variable v *)
          let bound_closure =
            List.find_opt (fun (x, _) -> x = slot) bound
          in
          (match bound_closure with
          | None -> subst_singleton_set_of_closures_named ~bound:phi ~clo:set e
                      (* Expr.create_named e *)
          | Some (k, _) -> Expr.create_named (Closure_expr (phi, k, set)))
        | None -> Misc.fatal_error "Cannot be reached")
      | (Deleted_code | Code _) -> Misc.fatal_error "Cannot be reached")
  | Literal (Res_cont _ | Code_id _ | Cont _ | Slot (_, Value_slot _))
  | Closure_expr _ | Set_of_closures _ | Rec_info _ ->
    Expr.create_named e)

and subst_code_id_set_of_closures (bound : Code_id.t) ~let_body
      {function_decls; value_slots}
  : set_of_closures =
  let function_decls : core_exp SlotMap.t =
    function_decls |>
      SlotMap.map
        (fun x ->
           subst_pattern_static
             ~bound:(Bound_codelike.Pattern.code bound) ~let_body x)
  in
  {function_decls; value_slots}

and subst_code_id (bound : Code_id.t) ~(let_body : static_const_or_code) (e : named) : core_exp =
  match e with
  | Literal e ->
    (match e with
     | Code_id code_id ->
       if (Code_id.compare code_id bound = 0)
       then Expr.create_named (Static_consts [let_body])
       else (Expr.create_named (Literal e))
     | (Simple _ | Cont _ | Res_cont _ | Slot _) -> Expr.create_named (Literal e))
  | Prim e ->
    prim_fix
      (subst_pattern_static
         ~bound:(Bound_codelike.Pattern.code bound) ~let_body) e
  | Closure_expr (phi, slot, set) ->
    Expr.create_named (Closure_expr (phi, slot, subst_code_id_set_of_closures bound ~let_body set))
  | Set_of_closures set ->
    let set = subst_code_id_set_of_closures bound ~let_body set
    in
    Expr.create_named (Set_of_closures set)
  | Static_consts consts ->
    static_const_group_fix
      (subst_pattern_static ~bound:(Bound_codelike.Pattern.code bound) ~let_body)
       consts
  | Rec_info _ -> Expr.create_named e

and subst_block_like
      ~(bound : Symbol.t) ~(let_body : static_const_or_code) (e : named) : core_exp =
  core_fmap
    (fun _ v ->
       match v with
       | Simple v ->
         if Simple.equal v (Simple.symbol bound)
         then Expr.create_named (Static_consts [let_body])
         else Expr.create_named (Literal (Simple v))
       | (Cont _ | Res_cont _ | Slot _ | Code_id _) ->
         Expr.create_named (Literal v))
    () (Expr.create_named e)

let partial_combine l1 l2 =
  let rec partial_combine (l1 : 'a list) (l2 : 'b list) acc
  : ('a * 'b) list * 'a list =
    (match l1, l2 with
     | _, [] -> acc, l1
     | x1 :: l1, x2 :: l2 ->
       let (acc, b) = partial_combine l1 l2 acc
       in
       (x1, x2) :: acc, b
     | [], _ -> Misc.fatal_error "Partial combine: Length mismatch")
  in
  partial_combine l1 l2 []

(* ∀ p i, p ∈ params -> params[i] = p -> e [p \ args[i]] *)
(* There can be partial applications: don't try to do [List.combine] to avoid
   fatal errors *)
(* [Bound_parameters] are [Variable]s *)
let subst_params
  (params : Bound_parameters.t) (e : core_exp) (args : core_exp list) =
  let param_list = Bound_parameters.to_list params in
  let param_args, remainder = partial_combine param_list args in
  let e =
    if remainder == []
    then e
    else
      Expr.create_handler
        (Core_continuation_handler.create (Bound_parameters.create remainder) e)
  in
  let param_args =
    List.map (fun (x, y) -> (Bound_parameter.simple x, y)) param_args in
  core_fmap
    (fun () s ->
      match s with
      | Simple s ->
          (match List.assoc_opt s param_args with
          | Some arg_v -> arg_v
          | None -> Expr.create_named (Literal (Simple s)))
      | (Cont _ | Res_cont _ | Slot _ | Code_id _) ->
        Expr.create_named (Literal s))
    () e

(* We want to remove [begin_region]/[end_region] pairs of the region is not used
   for anything.  This is accomplished in two steps:

   1) When simplifying [let x = e1 in e2], if [x] is unused in [e2], we can drop
   the whole let and just keep [e2].  And we don't count [end_region] as using
   its region argument, so we will drop [begin_region] (which is [e1] here) this
   way.  That happens in [step_let]

   2) But that leaves behind an [end_region] for a now undefined region in [e2].
   This function checks for that and cleans it up.  This is horribly inefficient
   - flambda2 actually does a much smarter thing so it doesn't have to
   re-traverse the term.  *)
let remove_corresponding_end_region region_var e1 e2 =
  let[@warning "-4"] is_let_end_region_of region_var e =
    Core_let.pattern_match e ~f:(fun ~x:_ ~e1 ~e2 ->
      match Expr.descr e1 with
      | Named (Prim (Unary (End_region, region))) ->
        begin match Expr.descr region with
        | Named (Literal (Simple region)) ->
          begin match Simple.must_be_var region with
          | Some (region_var', _) when Variable.equal region_var region_var' ->
            Some e2
          | _ -> None
          end
        | _ -> None
        end
      | _ -> None)
  in

  let rec remove_end region_var e2 =
    match Expr.descr e2 with
    | Invalid _-> e2
    | Named e ->
      named_fix (remove_end region_var)
        (fun () x -> Expr.create_named (Literal x)) () e
    | Let e ->
      begin match is_let_end_region_of region_var e with
      | Some e -> e
      | None -> let_fix (remove_end region_var) e
      end
    | Let_cont e -> let_cont_fix (remove_end region_var) e
    | Apply e -> apply_fix (remove_end region_var) e
    | Apply_cont e -> apply_cont_fix (remove_end region_var) e
    | Lambda e -> lambda_fix (remove_end region_var) e
    | Handler e -> handler_fix (remove_end region_var) e
    | Switch e -> switch_fix (remove_end region_var) e
  in
  match[@warning "-4"] Expr.descr e1, region_var with
  | Named (Prim (Nullary Begin_region)), Bound_for_let.Singleton v ->
    remove_end (Bound_var.var v) e2
  | _ -> e2

(* [LetCont-β]
  e1 where k args = e2 ⟶ e1 [k \ λ args. e2] *)
let rec subst_cont (cont_e1: core_exp) (k: Bound_continuation.t)
          (args: Bound_parameters.t) (cont_e2: core_exp) : core_exp =
  match Expr.descr cont_e1 with
  | Named (Literal (Cont cont | Res_cont (Return cont)))  ->
    if Continuation.equal cont k
    then
      Expr.create_handler
        (Core_continuation_handler.create args cont_e2)
    else cont_e1
  | Named (Set_of_closures e) ->
    let e = set_of_closures_fix (fun e -> subst_cont e k args cont_e2) e in
     Set_of_closures e |> Expr.create_named
  | Named (Static_consts e) ->
    static_const_group_fix (fun e -> subst_cont e k args cont_e2) e
  | Named (Prim e) ->
    prim_fix (fun e -> subst_cont e k args cont_e2) e
  | Named (Closure_expr (v, slot, e)) ->
    let e = set_of_closures_fix (fun e -> subst_cont e k args cont_e2) e in
     Closure_expr (v, slot, e) |> Expr.create_named
  | Named (Literal (Simple _ | Slot _ | Res_cont Never_returns | Code_id _)
          | Rec_info _) -> cont_e1
  | Let e ->
    let_fix (fun e -> subst_cont e k args cont_e2) e
  | Let_cont e ->
    let_cont_fix (fun e -> subst_cont e k args cont_e2) e
  | Apply e ->
    apply_fix (fun e -> subst_cont e k args cont_e2) e
  | Apply_cont {k = e; args = concrete_args} ->
    Expr.create_apply_cont
      {k = subst_cont e k args cont_e2;
        args = List.map (fun x -> subst_cont x k args cont_e2) concrete_args}
  | Lambda e ->
    lambda_fix (fun e -> subst_cont e k args cont_e2) e
  | Handler e ->
    handler_fix (fun e -> subst_cont e k args cont_e2) e
  | Switch e ->
    switch_fix (fun e -> subst_cont e k args cont_e2) e
  | Invalid _ -> cont_e1

let rec step (e: core_exp) : core_exp =
  match Expr.descr e with
  | Let { let_abst; expr_body } ->
    step_let let_abst expr_body
  | Let_cont e ->
    step_let_cont e
  | Apply {callee; continuation; exn_continuation; region; apply_args} ->
    step_apply callee continuation exn_continuation region apply_args
  | Apply_cont {k ; args} ->
    (* The recursive call for [apply_cont] is done for the arguments *)
    step_apply_cont k args
  | Lambda e -> step_lambda e
  | Handler e -> step_handler e
  | Switch {scrutinee; arms} ->
    let scrutinee = step scrutinee in
    let arms =
      Targetint_31_63.Map.map (fun x -> let e = step x in e) arms
    in
    step_switch scrutinee arms
  | Named e -> step_named e
  | Invalid _ -> e

and _simplify_speculative_application (e : core_exp) : core_exp =
  (match Expr.descr e with
   | Apply {callee; continuation; exn_continuation; region; apply_args} ->
     (match must_be_handler continuation with
     | Some cont ->
        let continuation_arg =
          Core_continuation_handler.pattern_match cont
         (fun x _ -> x)
      in
      let continuation' =
        step_apply_cont continuation [e]
          |> Core_continuation_handler.create continuation_arg
          |> Expr.create_handler
      in
        {callee=callee;
        continuation= continuation';
        exn_continuation=exn_continuation;
        region=region;
        apply_args=apply_args} |>
        Expr.create_apply
     | None -> e)
   | _ -> e)[@ocaml.warning "-4"] (* FIXME *)

and step_lambda (e : lambda_expr) =
  Core_lambda.pattern_match e
    ~f:(fun {return_continuation; exn_continuation; params; my_region} e ->
      let e = step e in
      Expr.create_lambda
        (Core_lambda.create
           {return_continuation;exn_continuation;params;my_region}
            e))

and step_handler (e : continuation_handler) =
  Core_continuation_handler.pattern_match e
    (fun param e ->
       let e = step e in
       Expr.create_handler
         (Core_continuation_handler.create param e))

(* NOTE: [List.for_all] could be inefficient *)
and step_switch scrutinee arms : core_exp =
  let default =
    (* if the arms are all the same, collapse them to a single arm *)
      (* Expr.create_switch {scrutinee; arms} *)
    let bindings = Targetint_31_63.Map.bindings arms in
    let (_, hd) = List.hd bindings in
    if (List.for_all (fun (_, x) -> Equiv.core_eq hd x) bindings)
    then hd
    else Expr.create_switch {scrutinee; arms}
  in
  (* if the scrutinee is exactly one of the arms, simplify *)
  match must_be_simple_or_immediate scrutinee with
  | Some s ->
    (match Simple.must_be_constant s with
      | Some constant ->
        (match Int_ids.Const.descr constant with
          | Naked_immediate i | Tagged_immediate i ->
            (Targetint_31_63.Map.find i arms)
          | Naked_float _ | Naked_int32 _ | Naked_int64 _ | Naked_nativeint _ ->
            default)
      | None -> default)
  | None -> default

(* FIXME: normalize apply tailcall if other expressions are not inlined yet
          (should happen for non-tailcalls as well) *)
and step_let let_abst body : core_exp =
  Core_let.pattern_match {let_abst; expr_body = body} ~f:(fun ~x ~e1 ~e2 ->
    (* If the let-bound value is a closure, store the normalized value into the
       environment. *)
    (* [LetL]
                    e1 ⟶ e1'
        -------------------------------------
       let x = e1 in e2 ⟶ let x = e1' in e2 *)
    (* If it's not a named expression, reduce [e1]. *)
    let x, e1 =
      match must_be_named e1 with
      | Some e ->
        step_named_for_let x e
      | None -> x, step e1
    in
    match Effects.can_substitute e1 with
    | Can_duplicate ->
      (* [e1] can be substituted freely; i.e. it has only generative effects and
         does not observe effects. *)
      (* [Let-β]
        let x = v in e1 ⟶ e2 [x\v] *)
      subst_pattern ~bound:x ~let_body:e1 e2 |> step
    | No_substitutions ->
      (* Cannot be substituted; however, if it returns unit, then value can be
         replaced with unit. *)
      let e2 =
        if returns_unit e1 then
        (* Substitute in unit value in place for [e2]. *)
          subst_pattern ~bound:x
            ~let_body:(Expr.create_named (Literal (Simple
            (Simple.const Int_ids.Const.const_zero)))) e2
        else e2
      in
      Core_let.create ~x ~e1 ~e2:(step e2)
    | Can_delete_if_unused ->
      (* Can be deleted if its result is unused.  We also apply the unit
         optimization from above. *)
      let e2 =
        if returns_unit e1 then
        (* Substitute in unit value in place for [e2]. *)
          subst_pattern ~bound:x
            ~let_body:(Expr.create_named (Literal (Simple
            (Simple.const Int_ids.Const.const_zero)))) e2
        else e2
      in
      let e2 = step e2 in
      let is_used = Core_let.let_var_free_in x e2 in
      if is_used then
        Core_let.create ~x ~e1 ~e2
      else
        (* A very special case for when we've removed a begin_region *)
        remove_corresponding_end_region x e1 e2
  )

and step_let_cont ({handler; body}:let_cont_expr) : core_exp =
  Core_continuation_handler.pattern_match handler
    (fun args e2 ->
        Core_letcont_body.pattern_match body
          (fun k e1 ->
            (* [LetCont-β]
              e1 where k args = e2 ⟶ e1 [k \ λ args. e2] *)
            let result = subst_cont e1 k args e2 in
            result
          )
    ) |> step

(* Reduce a direct loop apply to an [apply_cont]. *)
and reduce_rec_call_apply
    ({return_continuation; exn_continuation; my_region = _; params=_} as t : Bound_for_lambda.t) key phi
    (e : core_exp) =
  let _red_call = reduce_rec_call_apply t key phi in
  (match descr e with
  | Named e -> named_fix (_red_call) (fun () x -> Expr.create_named (Literal x)) () e
  | Let e -> let_fix (_red_call) e
  | Let_cont e -> let_cont_fix (_red_call) e
  | Apply_cont e -> apply_cont_fix (_red_call) e
  | Lambda e -> lambda_fix (_red_call) e
  | Handler e -> handler_fix (_red_call) e
  | Switch e -> switch_fix (_red_call) e
  | Invalid _ -> e
  | Apply {callee;
      continuation = continuation';
      exn_continuation = exn_continuation';
      region = _;
      apply_args} ->
      (* callee is to itself *)
      (match must_be_slot callee,
             must_be_cont continuation',
             must_be_cont exn_continuation'
        with
        | Some (_, Function_slot slot), Some continuation', Some exn_continuation' ->
          if (Function_slot.name slot =
              Function_slot.name key &&
            Continuation.equal return_continuation continuation' &&
            Continuation.equal exn_continuation exn_continuation')
          then
            (Expr.create_apply_cont {k = callee; args = apply_args})
          else e
        | (Some (_, (Value_slot _ | Function_slot _)) | None),
          (Some _ | None), (Some _ | None) -> e
        )
    )

and step_fun_decls (decls : function_declarations) phi =
  SlotMap.mapi
    (fun key slot ->
       match must_be_lambda slot with
       | Some x ->
         (* Check if this is a direct loop *)
         Core_lambda.pattern_match x
           ~f:(fun x e ->
               let e' = reduce_rec_call_apply x key phi e in
               (* If the return and exception continuation occurs in the
                  subexpression or the transformation didn't take place *)
               if not (does_not_occur [Cont x.return_continuation; Cont x.exn_continuation] true e')
                  || core_eq e e'
               then
                 slot
               else
                 Expr.create_handler
                    (Core_continuation_handler.create
                   x.params
                    (* (Bound_parameters.create params) *)
                    e'))
       | None -> slot
    ) decls

and step_apply_no_beta_redex callee continuation exn_continuation region apply_args :
  core_exp =
  let default =
    Expr.create_apply {callee;continuation;exn_continuation;region;apply_args}
  in
  match Expr.descr callee with
  | Named (Closure_expr (phi, slot, {function_decls; value_slots})) ->
    (* If it is a closure expression that contains a recursive call to itself,
       reduce the expression down to an [apply_cont] if possible. *)
    let function_decls' =
      step_fun_decls function_decls phi
    in
    (match (SlotMap.find_opt slot function_decls),
           (SlotMap.find_opt slot function_decls') with
     | Some decl, Some decl' ->
       if core_eq decl decl' then default
       else Expr.create_apply_cont
            { k = Expr.create_named (Closure_expr
                                    (phi, slot, {function_decls = function_decls'; value_slots}));
              args = apply_args }
     | _, _ -> default)
  | (Named (Static_consts ((Code _ | Deleted_code | Static_const _)::_ | [])
           | Literal _ | Prim _ | Set_of_closures _
           | Rec_info _)
    | Lambda _
    | Handler _ | Let _ | Let_cont _ | Apply _ | Apply_cont _ | Switch _ | Invalid _) ->
    default

and step_apply_lambda lambda_expr continuation exn_continuation region apply_args :
  core_exp =
  let e = Core_lambda.pattern_match lambda_expr
    ~f:(fun bound exp ->
        let params = bound.params in
        let exp =
          core_fmap
            (fun _ l ->
               match l with
               | (Cont k | Res_cont (Return k)) ->
                 if Continuation.equal k bound.return_continuation
                 then continuation
                 else if Continuation.equal k bound.exn_continuation
                 then exn_continuation
                 else (Expr.create_named (Literal l))
               | Simple s ->
                 if (Simple.same (Simple.var bound.my_region) s)
                 then region
                 else (Expr.create_named (Literal l))
               | (Res_cont Never_returns | Slot _ | Code_id _) ->
                 Expr.create_named (Literal l)
            ) () exp
        in
        subst_params params exp apply_args)
  in
  (* simplify_speculative_application e *) e

and step_apply callee continuation exn_continuation region apply_args : core_exp =
  (let callee = step callee in
  let continuation = step continuation in
  let exn_continuation = step exn_continuation in
  let region = step region in
  let apply_args = List.map step apply_args in
  match Expr.descr callee with
  | Lambda expr ->
    step_apply_lambda expr continuation exn_continuation region apply_args
  | (Named _ | Handler _ | Let _ | Let_cont _ | Apply _ | Apply_cont _
    | Switch _ | Invalid _) ->
    step_apply_no_beta_redex callee continuation exn_continuation region apply_args
  )[@ocaml.warning "-4"]

(* Note that the beta-reduction for [apply_cont] is implemented in
   [step_let_cont] (LATER: Refactor) *)
and step_apply_cont k args : core_exp =
  let k = step k in
  (* [ApplyCont]
            args ⟶ args'
      --------------------------
     k args ⟶ k args'       *)
  let args = List.map step args in
  match must_be_handler k with
  | Some handler ->
    Core_continuation_handler.pattern_match handler
      (fun params e -> subst_params params e args) |> step
  | None ->
    (match must_be_named k with
    | Some (Closure_expr (phi, slot, {function_decls; value_slots})) ->
      let x = SlotMap.find slot function_decls in
      let (e, args) =
        (match must_be_handler x with
          | Some x ->
            Core_continuation_handler.pattern_match x
              (fun params e' ->
                 let concrete_args =
                   List.combine (Bound_parameters.to_list params) args
                 in
                (* Loop invariant argument reduction :
                  for each parameter, remove the argument if
                  it only occurs in argument position of the recursive call
                  and nowhere else. *)
                let (params, e', args) =
                  List.fold_left (fun (l, e, args) (x, arg) ->
                    let (b, e) = eliminate_arguments_rec_call x arg e in
                    if b then (l, e, args) else (x :: l, e, arg :: args)
                  ) ([], e', []) concrete_args
                in
                let e =
                  Expr.create_handler
                      (Core_continuation_handler.create
                          (Bound_parameters.create params) e') in
                (e, args))
          | None -> (x, args))
        in
        let function_decls = SlotMap.add slot e function_decls in
        let k = Expr.create_named (Closure_expr (phi, slot, {function_decls; value_slots})) in
        Expr.create_apply_cont {k; args}
    | _ -> Expr.create_apply_cont {k; args})[@ocaml.warning "-4"]

(* N.B. [Projection reduction]
    When we substitute in a set of closures for primitives,
    (Here is where the `Projection` primitives occur),
    we eliminate the projection. *)
and subst_my_closure_body phi (clo: set_of_closures) (e : core_exp) : core_exp =
  match Expr.descr e with
  | Named e -> subst_my_closure_body_named phi clo e
  | Let e ->
    let_fix (subst_my_closure_body phi clo) e
  | Let_cont e ->
    let_cont_fix (subst_my_closure_body phi clo) e
  | Apply e ->
    apply_fix (subst_my_closure_body phi clo) e
  | Apply_cont e ->
    apply_cont_fix (subst_my_closure_body phi clo) e
  | Lambda e ->
    lambda_fix (subst_my_closure_body phi clo) e
  | Handler e ->
    handler_fix (subst_my_closure_body phi clo) e
  | Switch e ->
    switch_fix (subst_my_closure_body phi clo) e
  | Invalid _ -> e

and subst_my_closure_body_named _phi
    ({function_decls;value_slots}: set_of_closures) (e : named)
  : core_exp =
  (match e with
   | Prim (Unary (Project_value_slot slot, arg)) ->
     (match must_be_named arg with
      | Some (Closure_expr (_, _, {function_decls = _ ; value_slots})) ->
          (match Value_slot.Map.find_opt slot.value_slot value_slots with
            | Some exp -> exp
            | None -> Expr.create_named e)
      | _ ->
        (match Value_slot.Map.find_opt slot.value_slot value_slots with
         | Some exp ->
           (match must_have_closure exp with
            | Some _ -> exp
            | None ->
              (match must_be_function_slot_expr exp with
               | Some (phi, slot) ->
                 (match SlotMap.find_opt slot function_decls with
                  | Some e -> e
                  | None -> (Expr.create_named (Literal (Slot (phi, Function_slot slot)))))
               | None -> exp))
         | None -> Expr.create_named e))
  | Prim (Unary (Project_function_slot {move_from ; move_to}, arg)) ->
    (match must_be_function_slot_expr arg with
     | Some (phi, slot) ->
       (if (move_from = slot) then
        Expr.create_named (Literal (Slot (phi, Function_slot move_to)))
        else
          Expr.create_named e)
     | None -> Expr.create_named e)
  | (Prim (Unary
             ((Reinterpret_int64_as_float | Tag_immediate | Untag_immediate
              | Duplicate_block _ | Duplicate_array _
              | Is_int _ | Get_tag | Array_length | Bigarray_length _ | String_length _
              | Int_as_pointer | Opaque_identity _ | Int_arith _ | Float_arith _
              | Num_conv _ | Boolean_not | Unbox_number _ | Box_number _
              | Is_boxed_float | Is_flat_float_array | Begin_try_region | End_region
              | Obj_dup), _) | Nullary _ | Binary _ | Ternary _ | Variadic _)
    | Literal _ | Closure_expr _ | Set_of_closures _
    | Static_consts _ | Rec_info _) -> Expr.create_named e)[@ocaml.warning "-4"]

(* This is a "normalization" of [named] expression, in quotations because there
  is some simple evaluation that occurs for primitive arithmetic expressions *)
and step_named (body : named) : core_exp =
  match body with
  | Literal _ (* A [Simple] is a register-sized value *)
  | Rec_info _ (* Information about inlining recursive calls, an integer variable *) ->
    Expr.create_named (body)
  | Closure_expr (phi, slot, {function_decls; value_slots}) ->
    let function_decls = SlotMap.map step function_decls in
    let value_slots = Value_slot.Map.map step value_slots in
    (* If this slot has no reference to phi, just project it. *)
    begin match SlotMap.find_opt slot function_decls with
    | Some f ->
      if does_not_occur [Simple (Simple.var phi)] true f then
        f
      else
        Expr.create_named (Closure_expr (phi, slot, {function_decls; value_slots}))
    | None ->
      (* This seems like it should never happen? *)
      Misc.fatal_error "Missing slot"
    end
  | Set_of_closures {function_decls; value_slots} ->
    let function_decls = SlotMap.map step function_decls in
    let value_slots = Value_slot.Map.map step value_slots in
    Expr.create_named (Set_of_closures {function_decls; value_slots})
  | Static_consts e -> static_const_group_fix step e
  | Prim v ->
    let v = match v with
      | Nullary _ -> v
      | Unary (p, e) -> Unary (p, step e)
      | Binary (p, e1, e2) -> Binary (p, step e1, step e2)
      | Ternary (p, e1, e2, e3) -> Ternary (p, step e1, step e2, step e3)
      | Variadic (p, es) -> Variadic (p, List.map step es)
    in
    Eval_prim.eval v

(* This is a "normalization" of [named] expression, in quotations because there
  is some simple evaluation that occurs for primitive arithmetic expressions *)
and step_named_for_let (var: Bound_for_let.t) (body: named)
  : Bound_for_let.t * core_exp =
  match body with
  | Literal _ (* A [Simple] is a register-sized value *)
  | Rec_info _ (* Information about inlining recursive calls, an integer variable *) ->
    (var, Expr.create_named body)
  | Closure_expr (phi, slot, set) ->
    (var, Expr.create_named (Closure_expr (phi, slot, set)))
  | Set_of_closures set -> (* Map of [Code_id]s and [Simple]s corresponding to
                              function and value slots*)
    let set =
      (match var with
      | Singleton var | Static [Set_of_closures var] ->
        let phi = Bound_var.var var in step_set_of_closures phi set
      | _ -> set)[@ocaml.warning "-4"]
    in
    (var, Expr.create_named (Set_of_closures set))
  | Static_consts consts -> (* [Static_consts] are statically-allocated values *)
    let _ =
      (match var with
      | Static binding ->
        let l = List.combine binding consts in
        (* Add all code bindings to the environment **)
        let _ =
          List.map (fun (var, x) ->
            match var, x with
            | Bound_codelike.Pattern.Code var, Code x -> Hashtbl.add env var x
            | _, _ -> ()) l
        in ()
      | _ -> ())[@ocaml.warning "-4"] in
    (match var with
    | Static binding ->
      let l = List.combine binding consts in
      let var, consts =
        List.filter (fun (_, x) -> match x with Code _ -> false | _ -> true) l |>
        List.split
      in
      (let consts =
          List.map2 (
            fun var x ->
              match (var : Bound_codelike.Pattern.t), x with
              | Bound_codelike.Pattern.Set_of_closures var,
                Static_const (Static_set_of_closures soc) ->
                let phi = Bound_var.var var in
                let soc = step_set_of_closures phi soc in
                Static_const (Static_set_of_closures soc)
              | Bound_codelike.Pattern.Set_of_closures _, _ ->
                Misc.fatal_error "Binder mismatch for static exprs"
              | _, _ -> x
          ) var consts
        in
        (Static (Bound_codelike.create var),
        Expr.create_named (Static_consts consts)))
    | _ -> (var, Expr.create_named (Static_consts consts))
    )[@ocaml.warning "-4"]
  | Prim v -> (var, Eval_prim.eval v)

and concretize_my_closure phi (slot : Function_slot.t)
      ({expr=fn_expr;anon=_} : function_params_and_body)
      (clo : set_of_closures) : core_exp =
  Core_function_params_and_body.pattern_match fn_expr
    ~f:(fun bff e ->
      (* bff is the "my_closure" variable *)
      Expr.create_lambda
        (Core_lambda.pattern_match e
            ~f:(fun bound body ->
              (* Note: Can't use [Renaming] because it is bidirectional:
                we only want to substitute in one direction here, namely
                if we see any occurrence of a [my_closure], substitute in
                the closure [phi] variable. *)
              let body =
                core_fmap
                  (fun _ s ->
                    match s with
                    | Simple simple ->
                        if (Simple.same (Simple.var (Bound_var.var bff)) simple)
                        then
                          Expr.create_named (Literal (Slot (phi, Function_slot slot)))
                        else (Expr.create_named (Literal s))
                    | (Cont _ | Res_cont _ | Slot _ | Code_id _) ->
                      Expr.create_named (Literal s))
                  () body
              in
            Core_lambda.create bound (subst_my_closure_body phi clo body))))

and step_set_of_closures var
      {function_decls; value_slots} : set_of_closures =
  (* [ClosureVal] and [ClosureFn]
     substituting in value slots for [Project_value_slots] and
     substituting in function slots for [Project_function_slots] *)
  let function_decls' =
    (SlotMap.mapi
      (fun slot x ->
         (match must_be_literal x with
          | Some (Code_id id) ->
            (* Look up the code id in the environment *)
            let code =
              try Hashtbl.find env id with
              | Not_found ->
                (Format.printf "Fatal error: failed to find code_id %a" Code_id.print id;
                 exit 1)
            in
            (* Instantiate uses of [my_closure] and project out appropriate function
              and value slots *)
            let params_and_body =
              concretize_my_closure var slot code {function_decls;value_slots}
            in
            (* Step the body *)
            let params_and_body' = step params_and_body in
            params_and_body'
          | _ -> x))
      function_decls)[@ocaml.warning "-4"]
  in
  { function_decls = function_decls' ; value_slots }

(* Inline non-recursive continuation handlers first *)
let rec inline_handlers (e : core_exp) =
  match Expr.descr e with
  | Named e ->
    named_fix inline_handlers (fun () x -> Expr.create_named (Literal x)) () e
  | Let e ->
    let_fix inline_handlers e
  | Let_cont e -> inline_let_cont e
  | Apply e ->
    apply_fix inline_handlers e
  | Apply_cont e ->
    apply_cont_fix inline_handlers e
  | Lambda e -> lambda_fix inline_handlers e
  | Handler e ->
    handler_fix inline_handlers e
  | Switch e -> switch_fix inline_handlers e
  | Invalid _ -> e

and inline_let_cont ({handler; body}:let_cont_expr) : core_exp =
  Core_continuation_handler.pattern_match handler
    (fun args e2 ->
        Core_letcont_body.pattern_match body
          (fun k e1 ->
            (* [LetCont-β]
              e1 where k args = e2 ⟶ e1 [k \ λ args. e2] *)
            let result = subst_cont e1 k args e2 in
            result
          )
    ) |> inline_handlers

let normalize e =
  let e = inline_handlers e in
  step e

