open! Flambda
open! Flambda2_core
open! Translate

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

let rec does_not_occur (v : literal) acc (exp : core_exp) =
  match descr exp with
  | Invalid _ -> acc
  | Named (Literal l) ->
    (not (literal_contained v l) && acc)
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

(* [LetCont-β] *)
let rec subst_cont (cont_e1: core_exp) (k: Bound_continuation.t)
          (args: Bound_parameters.t) (cont_e2: core_exp) : core_exp =
  match Expr.descr cont_e1 with
  | Named (Literal (Cont cont | Res_cont (Return cont)))  ->
    if Continuation.equal cont k
    then
      Expr.create_handler
        (Core_continuation_handler.create args cont_e2)
    else cont_e1
  | Named (Literal (Simple _ | Slot _ | Res_cont Never_returns | Code_id _)
          | Prim _ | Closure_expr _ | Set_of_closures _ | Static_consts _
          | Rec_info _) -> cont_e1
  | Let e ->
    let_fix (fun e -> subst_cont e k args cont_e2) e
  | Let_cont e ->
    let_cont_fix (fun e -> subst_cont e k args cont_e2) e
  | Apply e ->
    apply_fix (fun e -> subst_cont e k args cont_e2) e
  | Apply_cont {k = e; args = concrete_args} ->
    (* if Continuation.equal cont k
     * then subst_params args cont_e2 concrete_args
     * else *)
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

and simplify_speculative_application (e : core_exp) : core_exp =
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
  Core_let.pattern_match {let_abst; expr_body = body}
    ~f:(fun ~x ~e1 ~e2 ->
    (* [LetL]
                    e1 ⟶ e1'
        -------------------------------------
       let x = e1 in e2 ⟶ let x = e1' in e2 *)
    (* If the let-bound value is a closure, store the normalized value into the
       environment. *)
    let x, e1 =
      (match must_be_named e1 with
       | Some e -> step_named_for_let x e
      | None -> let e1 = step e1 in x, e1)
    in
    (* [Let-β]
       let x = v in e1 ⟶ e2 [x\v] *)
    (* if can_inline e1 *)
    (* then *)
    (subst_pattern ~bound:x ~let_body:e1 e2 |> step))
(*     else *)
(*       ( *)
(* (\* let c, e2 = step c e2 in *\) *)
(*        let c, e2 = *)
(*          (if returns_unit e1 then *)
(*             let e2 = *)
(*               subst_pattern ~bound:x *)
(*                 ~let_body:(create_named (Literal (Simple *)
(*                 (Simple.const Int_ids.Const.const_zero)))) e2 *)
(*             in *)
(*             e2 *)
(*           else e2) |> step c *)
(*        in *)
(*        c, Core_let.create ~x ~e1 ~e2)) *)

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

and step_fun_decls (decls : function_declarations) =
  SlotMap.mapi
    (fun key x ->
       match must_be_lambda x with
       | Some x ->
         (* Check if this is a direct loop *)
         Core_lambda.pattern_match x
           ~f:(fun
                {return_continuation;
                 exn_continuation;
                 params;
                 my_region}
                e ->
                let default =
                  Expr.create_lambda
                    (Core_lambda.create
                       {return_continuation;exn_continuation;params;my_region}
                    e)
                in
                match must_be_apply e with
                | Some
                    {callee;
                      continuation = continuation';
                      exn_continuation = exn_continuation';
                      region = _;
                      apply_args} ->
                  (* callee is to itself *)
                  (match must_be_slot callee,
                          must_be_cont continuation',
                          must_be_cont exn_continuation'
                    with
                    | Some (_, Function_slot slot), Some cont, Some exn_cont ->
                      if Function_slot.name slot =
                         Function_slot.name key &&
                        Continuation.equal cont return_continuation &&
                        Continuation.equal exn_cont exn_continuation
                      then
                        Expr.create_handler
                          (Core_continuation_handler.create
                             params
                              (Expr.create_apply_cont
                                {k = callee;
                                args = apply_args}))
                      else default
                    | (Some (_, (Value_slot _ | Function_slot _)) | None),
                      (Some _ | None), (Some _ | None) ->
                      default
                   )
                  | None -> default
           )
       | None -> x
    ) decls

and step_apply_no_beta_redex callee continuation exn_continuation region apply_args :
  core_exp =
  let default =
    Expr.create_apply {callee;continuation;exn_continuation;region;apply_args}
  in
  match Expr.descr callee with
  | Named (Closure_expr (phi, slot, {function_decls; value_slots})) ->
    let function_decls =
      step_fun_decls function_decls
    in
    (match SlotMap.find_opt slot function_decls |>
            Option.map Expr.descr with
     | Some (Handler _) ->
       Expr.create_apply_cont
         { k = Expr.create_named (Closure_expr (phi, slot, {function_decls; value_slots}));
           args = apply_args }
     | (Some (Named _ | Let _ | Let_cont _ | Apply _ | Apply_cont _ | Switch _
              | Lambda _ | Invalid _) | None) -> default)
  | (Named (Static_consts ((Code _ | Deleted_code | Static_const _)::_ | [])
           | Literal _ | Prim _ | Set_of_closures _
           | Rec_info _)
    | Lambda _
    | Handler _ | Let _ | Let_cont _ | Apply _ | Apply_cont _ | Switch _ | Invalid _) ->
    default

and step_apply_function_decls phi slot function_decls
      callee continuation exn_continuation region apply_args : core_exp =
  match SlotMap.find_opt slot function_decls |>
        Option.map Expr.descr with
  | Some (Lambda exp) ->
    if does_not_occur (Simple (Simple.var phi)) true (Expr.create_lambda exp) then
      step_apply_lambda exp continuation exn_continuation region apply_args
    else
      step_apply_no_beta_redex callee continuation exn_continuation region apply_args
  | (Some (
    (Named _ | Let _ | Let_cont _ | Apply _ | Apply_cont _ | Switch _
    | Handler _ | Invalid _)) | None) ->
    step_apply_no_beta_redex callee continuation exn_continuation region apply_args

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
  simplify_speculative_application e

and step_apply callee continuation exn_continuation region apply_args : core_exp =
  (let callee = step callee in
  let continuation = step continuation in
  let exn_continuation = step exn_continuation in
  let region = step region in
  let apply_args = List.map step apply_args in
  match Expr.descr callee with
  | Named (Closure_expr (phi, slot,
                         {function_decls; value_slots = _})) ->
    step_apply_function_decls phi slot function_decls
      callee continuation exn_continuation region apply_args
  | Lambda expr ->
    step_apply_lambda expr continuation exn_continuation region apply_args
  | (Named (Static_consts ((Code _ | Deleted_code | Static_const _)::_ | [])
           | Literal _ | Prim _ | Set_of_closures _
           | Rec_info _)
     | Handler _ | Let _ | Let_cont _ | Apply _ | Apply_cont _ | Switch _ | Invalid _) ->
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
  | None -> Expr.create_apply_cont {k; args}

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
    Expr.create_named (Closure_expr (phi, slot, {function_decls; value_slots}))
  | Set_of_closures {function_decls; value_slots} ->
    let function_decls = SlotMap.map step function_decls in
    let value_slots = Value_slot.Map.map step value_slots in
    Expr.create_named (Set_of_closures {function_decls; value_slots})
  | Static_consts e -> static_const_group_fix step e
  | Prim v -> Eval_prim.eval v

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
      (* let _ = *) (*   Format.printf "Bound var %a\n\n%! Body is %a \n\n\n%!" *)
      (*     Bound_for_let.print var Flambda2_core.print (Expr.create_named body) *)
      (* in *)
      (* Misc.fatal_error "Unexpected binders for static exprs" *)
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
  let function_decls =
    (SlotMap.mapi
      (fun slot x ->
         (match must_be_literal x with
          | Some (Code_id id) ->
            let code = Hashtbl.find env id in
            let params_and_body =
              concretize_my_closure var slot code {function_decls;value_slots}
            in
            params_and_body
          | _ -> x))
      function_decls)[@ocaml.warning "-4"]
  in
  { function_decls ; value_slots }

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
