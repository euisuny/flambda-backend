open! Flambda
open! Flambda2_core
open! Translate

module P = Flambda_primitive

let fuel = ref 0

let fuel_limit = 30

(* Semantic values of Flambda2 terms

   Each term gets translated into an open singleton term with names and closures
   in place of abstraction *)
type value =
  | VFun of Variable.t
  | VNamed of named_value
  | VApply of apply_value
  | VApplyCont of apply_cont_value
  | VLambda of closure
  | VHandler of closure
  | VSwitch of switch_value
  | VInvalid of { message : string }

and literal_value =
  | VSimple of Simple.t
  | VCont of Continuation.t
  | VRes_cont of Apply_expr.Result_continuation.t
  | VSlot of (Variable.t * slot)
  | VCode_id of Code_id.t

and named_value =
  | VLiteral of literal_value
  | VPrim of primitive_value
  | VStatic_consts of static_const_group_value
  | VRec_info of Rec_info_expr.t

and primitive_value =
  | Nullary of P.nullary_primitive
  | Unary of P.unary_primitive * value
  | Binary of P.binary_primitive * value * value
  | Ternary of P.ternary_primitive * value * value * value
  | Variadic of P.variadic_primitive * value list

and static_const_or_code_value =
  | VCode of closure
  | VDeleted_code
  | VStatic_const of static_const_value

and static_const_value =
  | Block of Tag.Scannable.t * Mutability.t * value list
  | Boxed_float of Numeric_types.Float_by_bit_pattern.t Or_variable.t
  | Boxed_int32 of Int32.t Or_variable.t
  | Boxed_int64 of Int64.t Or_variable.t
  | Boxed_nativeint of Targetint_32_64.t Or_variable.t
  | Immutable_float_block of
      Numeric_types.Float_by_bit_pattern.t Or_variable.t list
  | Immutable_float_array of
      Numeric_types.Float_by_bit_pattern.t Or_variable.t list
  | Immutable_value_array of Field_of_static_block.t list
  | Empty_array
  | Mutable_string of { initial_value : string }
  | Immutable_string of string
and static_const_group_value = static_const_or_code_value list

and apply_value =
  { callee: value;
    continuation: value;
    exn_continuation: value;
    region: value;
    apply_args: value list; }

and apply_cont_value =
  { k : value;
    args : value list }

and switch_value =
  { scrutinee : value;
    arms : value Targetint_31_63.Map.t }

and value_env = (name * value) list

and function_env = (fun_name * (SlotMap.key * value) list) list

(* A closure is a list of names, function and value environment, and a core
   expression *)
and closure =
  { names : name list;
    fun_env : function_env;
    val_env : value_env;
    exp: core_exp }

and name =
  | NCont of Continuation.t
  | NVar of Variable.t
  | NSlot of slot
  | NCode of Code_id.t
  | NSymbol of Symbol.t

and fun_name =
    | NFun of Variable.t

(* Analogous to [reflect] *)
let rec eval fenv (venv : (name * value) list) (e : core_exp) : value =
  match Expr.descr e with
  | Let e ->
    let x, e1, e2 =
      Core_let.pattern_match e
        ~f:(fun ~x ~e1 ~e2 -> x, e1, e2)
    in
    let env' = let_bound_to_name fenv venv x e1 in
    eval fenv (env' @ venv) e2

  | Let_cont {handler; body} ->
    let e2 = With_delayed_renaming.create (Handler handler) in
    let k, e1 =
      Core_letcont_body.pattern_match body
        (fun k e1 -> k, e1)
    in
    eval fenv ((NCont k, eval fenv venv e2)::venv) e1

  | Apply
      {callee; continuation; exn_continuation;
       region; apply_args} ->
    let apply_args' = List.map (eval fenv venv) apply_args in
    let t = eval fenv venv callee in
    (if !fuel < fuel_limit then
       (fuel := !fuel + 1;
        match eval fenv venv callee with
        | VLambda {names =
            NVar _ :: NCont ret :: NCont ex :: NVar reg :: params ;
            fun_env ; val_env ; exp } ->
          let l = [(NCont ret, eval fenv venv continuation);
                  (NCont ex, eval fenv venv exn_continuation);
                  (NVar reg, eval fenv venv region);
                  (NVar reg, eval fenv venv region)] in
          let args = List.combine params apply_args' in
          eval (fun_env @ fenv) (l @ args @ val_env @ venv) exp
        | t ->
          VApply
          {callee = t;
          continuation = eval fenv venv continuation;
          exn_continuation = eval fenv venv exn_continuation;
          region = eval fenv venv region;
          apply_args = apply_args'})[@ocaml.warning "-4"]
    else
      VApply
        {callee = t;
         continuation = eval fenv venv continuation;
         exn_continuation = eval fenv venv exn_continuation;
         region = eval fenv venv region;
         apply_args = apply_args'})

  | Apply_cont {k ; args} ->
    let args = List.map (eval fenv venv) args in
    let t = eval fenv venv k in
    (if !fuel < fuel_limit then
     (fuel := !fuel + 1;
      match eval fenv venv k with
     | VHandler {names; fun_env; val_env; exp} ->
       let args = List.combine names args in
       eval (fun_env @ fenv) (args @ val_env) exp
     | t ->
       VApplyCont {k = t; args})[@ocaml.warning "-4"]
     else
       VApplyCont {k = t; args})
  | Lambda t ->
    let x, e =
      Core_lambda.pattern_match t ~f:(fun b e -> b, e)
    in
    let params = x.params |> Bound_parameters.to_list |>
                 List.map (fun x -> NVar (Bound_parameter.var x)) in
    VLambda
      { names =
        [NCont x.return_continuation;
          NCont x.exn_continuation;
          NVar x.my_region] @ params;
        fun_env = fenv;
        val_env = venv;
        exp = e }
  | Handler t ->
    let x, e =
      Core_continuation_handler.pattern_match t
        (fun b e -> b, e)
    in
    let x = Bound_parameters.to_list x |>
            List.map (fun x -> (NVar (Bound_parameter.var x))) in
    VHandler
      { names = x; fun_env = fenv; val_env = venv; exp = e }
  | Switch {scrutinee; arms} ->
    VSwitch {
      scrutinee = eval fenv venv scrutinee;
      arms = Targetint_31_63.Map.map (eval fenv venv) arms
    }
  | Named e -> eval_named fenv venv e
  | Invalid { message } -> VInvalid { message }

and let_bound_to_name (fenv : function_env) (venv : value_env)
    (t : Bound_for_let.t) (e : core_exp)
  : (name * value) list =
  match t with
  | Singleton v ->
    let nvar = NVar (Bound_var.var v) in
    (match must_be_named e with
     | Some e ->
       (match e with
        | Literal l ->
          [(nvar, eval_literal fenv venv l)]
        | Prim p ->
          [(nvar, eval fenv venv (Eval_prim.eval p))]
        | Closure_expr (var, fn, clos) ->
          let slot =
            Named (Literal (Slot (var, Function_slot fn)))
            |> With_delayed_renaming.create
          in
          let env =
            closure_expr_to_closure fenv var venv clos
          in
          let x = eval fenv (env @ venv) slot in
          [(nvar, x)]
        | Set_of_closures clos ->
            closure_expr_to_closure
              fenv (Bound_var.var v)
              venv clos
        | Static_consts _ ->
          Misc.fatal_error
            "Expected static variable to be bound for static constants"
        | Rec_info v -> [(nvar, VNamed (VRec_info v))])
     | None ->
        [(NVar (Bound_var.var v), eval fenv venv e)]
    )
  | Static c ->
    (match must_be_static_consts e with
     | Some group ->
       let binding = List.combine c group in
       let group ((c, e) : Bound_codelike.Pattern.t * static_const_or_code) =
         (match c with
          | Bound_codelike.Pattern.Code c ->
            let e = Expr.create_named (Static_consts [e]) in
            [(NCode c, eval fenv venv e)]
          | Bound_codelike.Pattern.Set_of_closures v ->
            (match e with
             | Static_const (Static_set_of_closures clos) ->
                closure_expr_to_closure fenv (Bound_var.var v) venv clos
             | _ -> Misc.fatal_error "Expected static closure body")
          | Bound_codelike.Pattern.Block_like s  ->
            let e = Expr.create_named (Static_consts [e]) in
            [(NSymbol s, eval fenv venv e)]) in
       List.map group binding |> List.flatten
     | None -> Misc.fatal_error "Expected static consts body")

and closure_expr_to_closure
    (fenv : function_env)
    (phi : Variable.t)
    (venv: (name * value) list)
    ({function_decls; value_slots} : set_of_closures) =
  let value_slots_list =
    Value_slot.Map.map (eval fenv venv) value_slots |>
    Value_slot.Map.to_seq |> List.of_seq in
  let value_slots =
    List.map (fun (k, v) -> (NSlot (Value_slot k), v))
      value_slots_list
  in
  let env = value_slots @ venv in
  let phi_value =
    SlotMap.to_seq function_decls |>
    List.of_seq |>
    List.map (fun (i, x) -> (i, eval fenv venv x))
  in
  let function_decls_list : (name * _) list =
    SlotMap.to_seq function_decls |>
    List.of_seq |>
    List.map
      (fun (i, x) ->
        (NSlot (Function_slot i),
         match must_be_code_id x with
         | Some id ->
           (match (List.assoc_opt (NCode id) env) with
            | Some (VNamed (VStatic_consts
                  [VCode { names; fun_env; val_env; exp }])) ->
              (* Value slot extends the environment captured for a function *)
              VLambda
                { names = names;
                  fun_env = (NFun phi, phi_value) :: fenv @ fun_env;
                  val_env = (NVar phi, VFun phi) ::
                      value_slots @ val_env @ venv;
                  exp = exp}
            | _ ->
              eval ((NFun phi, phi_value) :: fenv)
                    ((NVar phi, VFun phi):: venv) x)
        | None -> eval ((NFun phi, phi_value) :: fenv)
                        ((NVar phi, VFun phi):: venv) x))
  in
  function_decls_list

and eval_named
    (fenv : function_env) (venv : value_env) (e : named) =
  match e with
  | Literal l -> eval_literal fenv venv l
  | Prim p -> eval_prim fenv venv p
  | Closure_expr (var, fn, clos) ->
    let slot =
      Named (Literal (Slot (var, Function_slot fn)))
        |> With_delayed_renaming.create
    in
    let env =
      closure_expr_to_closure fenv var venv clos
    in
    eval fenv (env @ venv) slot
  | Set_of_closures _ ->
    Misc.fatal_error "[eval_named] Unreachable: set of closures"
  | Static_consts consts ->
    VNamed
      (VStatic_consts
         (List.map (eval_static_const_or_code fenv venv) consts))
  | Rec_info v -> VNamed (VRec_info v)

and eval_static_const_or_code
    (fenv : function_env) (venv : value_env)
    (c : static_const_or_code) : static_const_or_code_value =
  match c with
  | Code f -> eval_function_params_and_body fenv venv f
  | Deleted_code -> VDeleted_code
  | Static_const s -> VStatic_const (eval_static_const fenv venv s)

and eval_function_params_and_body
    (fenv : function_env) (venv : value_env)
    ({expr; _} : Flambda2_core.function_params_and_body) =
  let v, args, e =
    Core_function_params_and_body.pattern_match
      expr ~f:(fun v t ->
        let args, e =
          Core_lambda.pattern_match t
            ~f:(fun b e -> b, e)
        in (v, args, e))
  in
  let params = args.params |> Bound_parameters.to_list |>
               List.map (fun x -> NVar (Bound_parameter.var x)) in
  VCode
    {names = [NVar (Bound_var.var v);
              NCont args.return_continuation;
              NCont args.exn_continuation;
              NVar args.my_region] @ params;
     fun_env = fenv;
     val_env = venv;
     exp = e}

and eval_static_const
    (fenv : function_env) (venv : value_env) (s : static_const) =
  match s with
  | Static_set_of_closures _ ->
    Misc.fatal_error "Unreachable: eval_static_const [static_set_of_closures]"
  | Block (tag, mut, l) ->
    let l = List.map (eval fenv venv) l in
    Block (tag, mut, l)
  | Boxed_float t -> Boxed_float t
  | Boxed_int32 t -> Boxed_int32 t
  | Boxed_int64 t -> Boxed_int64 t
  | Boxed_nativeint t -> Boxed_nativeint t
  | Immutable_float_block t -> Immutable_float_block t
  | Immutable_float_array t -> Immutable_float_array t
  | Immutable_value_array t -> Immutable_value_array t
  | Empty_array -> Empty_array
  | Mutable_string { initial_value } -> Mutable_string { initial_value }
  | Immutable_string s -> Immutable_string s

and _print_name fmt (n : name) =
  match n with
  | NVar s ->
    Format.fprintf fmt "var %a @."
      Variable.print s
  | NSymbol s ->
    Format.fprintf fmt "symbol %a @."
      Symbol.print s
  | NSlot (Function_slot s) ->
    Format.fprintf fmt "fn slot %a @."
      Function_slot.print s
  | NSlot (Value_slot s) ->
    Format.fprintf fmt "val slot %a @."
     Value_slot.print s
  | NCode i ->
    Format.fprintf fmt "code id %a @."
      Code_id.print i
  | NCont i ->
    Format.fprintf fmt "cont %a @." Continuation.print i

and _print_env (env : (name * value) list) =
  Format.fprintf Format.std_formatter "------- val_env -------@.";
  List.iter (fun (n, _) -> _print_name Format.std_formatter n) env;
  Format.fprintf Format.std_formatter "-------------------@.@."

and _print_fenv (fenv : function_env) =
  Format.fprintf Format.std_formatter "------- fun_env -------@.";
  List.iter (fun (NFun n, env) ->
      Format.fprintf
      Format.std_formatter "Var %a@." Variable.print n;
      List.iter (fun (k, _) ->
          Format.fprintf
          Format.std_formatter "Slot %a@."
          Function_slot.print k) env)
    fenv;
  Format.fprintf Format.std_formatter "-------------------@.@."

and eval_literal fenv (env : (name * value) list) (e : literal) =
  match e with
  | Simple s ->
    let x =
      Simple.pattern_match' s
        ~var:(fun t ~coercion:_ ->
            List.assoc_opt (NVar t) env)
        ~symbol:(fun t ~coercion:_ ->
            List.assoc_opt (NSymbol t) env)
        ~const:(fun _ -> Some (VNamed (VLiteral (VSimple s))))
    in
    (match x with
      | Some (VNamed (VLiteral (VCode_id i))) ->
          (match (List.assoc_opt (NCode i) env) with
            | Some x -> x
            | None -> Misc.fatal_error "Literal not found")
      | Some s -> s
      | _ -> (VNamed (VLiteral (VSimple s))))
  | Cont k ->
    (match List.assoc_opt (NCont k) env with
     | Some s -> s
     | None -> VNamed (VLiteral (VCont k)))
  | Res_cont (Return k) -> List.assoc (NCont k) env
  | Res_cont _ -> Misc.fatal_error "Res_cont : Never returns"
  | Code_id id ->
    (match List.assoc_opt (NCode id) env with
     | Some x -> x
     | None -> VNamed (VLiteral (VCode_id id)))
  | Slot (var, Function_slot slot) ->
    (* Debug print.. *)
    (* _print_fenv _fenv; *)
    (* _print_env env; *)
    (* Format.fprintf Format.std_formatter "%a" Function_slot.print slot; *)

    (* VNamed (VLiteral (VSlot (var, Function_slot slot))) *)

    (* TODO: Add fuel so it doesn't diverge *)
    (* TODO: Change value environment to only store value slots *)
    (* TODO: Clean up [List.assoc_opt] use cases *)
    (match (List.assoc_opt (NFun var) fenv) with
    | Some x ->
      (let x = List.assoc_opt slot x in
      (match x with
      | Some (VNamed (VLiteral (VCode_id i))) ->
         (match (List.assoc_opt (NCode i) env) with
           | Some x' -> x'
           | None -> (VNamed (VLiteral (VCode_id i))))
      | Some x -> x
      | None ->
        Misc.fatal_error "Not found: function_slot"))
    | None ->
      let x  = List.assoc_opt (NSlot (Function_slot slot)) env in
      (match x with
       | Some (VNamed (VLiteral (VCode_id i))) ->
         (match (List.assoc_opt (NCode i) env) with
          | Some x' -> x'
          | None -> (VNamed (VLiteral (VCode_id i))))
         (* (match (List.assoc_opt (NCode i) env) with *)
         (*  | Some x' -> x' *)
         (*  | None -> (VNamed (VLiteral (VCode_id i)))) *)
       | Some x -> x
       | None ->
         (VNamed (VLiteral (VSlot (var, (Function_slot slot)))))))

  | Slot (_, Value_slot slot) ->
    let x  = List.assoc_opt (NSlot (Value_slot slot)) env in
    (match x with
     | Some (VNamed (VLiteral (VCode_id i))) ->
       (match (List.assoc_opt (NCode i) env) with
        | Some x' -> x'
        | None -> (VNamed (VLiteral (VCode_id i))))
     | Some x -> x
     | None -> Misc.fatal_error "Not found: value_slot")

and eval_prim (fenv : function_env) (venv : value_env)
    (e : primitive) =
  (match e with
    | Nullary e ->
      VNamed (VPrim (Nullary e))
    | Unary (Project_value_slot
        { project_from ; value_slot = slot; kind }, arg) ->
      let x = List.assoc_opt (NSlot (Value_slot slot)) venv in
      (match x with
      | Some x -> x
      | _ ->
        VNamed
        (VPrim
          (Unary
            (Project_value_slot
                      { project_from ; value_slot = slot; kind } ,
            eval fenv venv arg))))
    | Unary (Project_function_slot {move_from ; move_to}, arg) ->
      let x = List.assoc_opt (NSlot (Function_slot move_to)) venv in
      (match x with
        | Some x -> x
        | _ ->
          Format.fprintf Format.std_formatter "%s" (Function_slot.to_string move_to);
          VNamed
                (VPrim
                    (Unary
                      (Project_function_slot
                          { move_from ; move_to} ,
                        eval fenv venv arg))))
    | Unary (p, e) ->
      VNamed (VPrim (Unary (p, eval fenv venv e)))
    | Binary (p, e1, e2) ->
      VNamed (VPrim (Binary (p, eval fenv venv e1, eval fenv venv e2)))
    | Ternary (p, e1, e2, e3) ->
      VNamed (VPrim (Ternary
        (p, eval fenv venv e1, eval fenv venv e2, eval fenv venv e3)))
    | Variadic (p, list) ->
      VNamed (VPrim (Variadic (p, List.map (eval fenv venv) list))))

let appCl ({names = _; fun_env; val_env; exp} : closure) : value =
  eval fun_env val_env exp

let rec quote (ns : name list) (t : value) : core_exp =
  match t with
  | VNamed e -> quote_named ns e
  | VApply {callee ; continuation ; exn_continuation ; region ; apply_args} ->
    let e =
      Apply
        { callee = quote ns callee;
          continuation = quote ns continuation;
          exn_continuation = quote ns exn_continuation;
          region = quote ns region;
          apply_args = List.map (quote ns) apply_args }
    in
    With_delayed_renaming.create e
  | VApplyCont { k ; args } ->
    let e =
      Apply_cont
        { k = quote ns k;
          args = List.map (quote ns) args}
    in
    With_delayed_renaming.create e
  | VLambda
      { names =
          NVar clo ::
                NCont ret ::
                NCont exn ::
                NVar region :: params;
        fun_env; val_env; exp } ->
    let params' =
      List.map
        (fun x ->
          match x with
            | NVar v ->
              Bound_parameter.create v
                Flambda_kind.With_subkind.any_value
            | _ -> Misc.fatal_error "Expected variable") params
      |> Bound_parameters.create
    in
    let x = Bound_for_lambda.create
              ~return_continuation:ret
              ~exn_continuation:exn
              ~params:params'
              ~my_region:region
    in
    let l =
      NVar clo ::
            NCont ret :: NCont exn :: NVar region :: params in
    let e = Lambda
      (Core_lambda.create
        x
        (quote (l @ ns)
            (appCl { names = l; fun_env; val_env; exp})))
    in
    With_delayed_renaming.create e
  | VLambda
      { names =
          NCont ret ::
          NCont exn ::
          NVar region :: params;
        fun_env; val_env; exp } ->
    let params' =
      List.map
        (fun x ->
           match x with
           | NVar v ->
             Bound_parameter.create v
               Flambda_kind.With_subkind.any_value
           | _ -> Misc.fatal_error "Expected variable") params
      |> Bound_parameters.create
    in
    let x = Bound_for_lambda.create
        ~return_continuation:ret
        ~exn_continuation:exn
        ~params:params'
        ~my_region:region
    in
    let l =
      NCont ret :: NCont exn :: NVar region :: params in
    let e = Lambda
        (Core_lambda.create
           x
           (quote (l @ ns)
              (appCl { names = l; fun_env; val_env; exp})))
    in
    With_delayed_renaming.create e
  | VHandler { names; fun_env; val_env; exp } ->
    let params =
      List.map
        (fun x ->
           match x with
           | NVar i ->
             Bound_parameter.create i
               (Flambda_kind.With_subkind.any_value)
           | _ -> Misc.fatal_error
                    "Expected variable parameters for handler ")
        names
      |> Bound_parameters.create
    in
    let e =
      Handler
        (Core_continuation_handler.create
           params
           (quote (names @ ns)
              (appCl
                 { names; fun_env; val_env; exp })))
    in
    With_delayed_renaming.create e
  | VSwitch { scrutinee ; arms } ->
    let scrutinee = quote ns scrutinee in
    let arms = Targetint_31_63.Map.map (quote ns) arms in
    With_delayed_renaming.create
      (Switch {scrutinee = scrutinee; arms = arms})
  | VInvalid { message } ->
    With_delayed_renaming.create (Invalid { message })
  | VLambda { names; fun_env = _; val_env = _; exp = _} ->
    List.iter (_print_name Format.std_formatter) names;
    Misc.fatal_error "Mismatched lambda arguments on quoting"
  | VFun var ->
      (Named (Literal (Simple (Simple.var var)))
            |> With_delayed_renaming.create)

and quote_named ns (e : named_value) : core_exp =
  match e with
  | VLiteral s ->
    Named (Literal
      (match s with
       | VSimple s -> Simple s
       | VCont k -> Cont k
       | VRes_cont k -> Res_cont k
       | VSlot s -> Slot s
       | VCode_id id -> Code_id id))
    |> With_delayed_renaming.create
  | VPrim p -> quote_prim ns p
  | VStatic_consts const ->
    Named (quote_static_consts ns const)
    |> With_delayed_renaming.create
  | VRec_info rec_info ->
    Named (Rec_info rec_info)
    |> With_delayed_renaming.create

and quote_static_consts ns group : named =
  Static_consts (List.map (quote_static_const_or_code ns) group)

and quote_static_const_or_code ns const : static_const_or_code =
  match const with
  | VCode clo -> Code {expr = quote_code ns clo ; anon = false}
  | VDeleted_code -> Deleted_code
  | VStatic_const s -> Static_const (quote_static_const ns s)

and quote_code ns (clo : closure) =
  (match clo with
    | { names =
        NVar clo :: NCont ret :: NCont exn :: NVar region :: params;
        fun_env ; val_env ; exp } ->
    let params' =
      List.map
        (fun x ->
           match x with
           | NVar v ->
             Bound_parameter.create v
               Flambda_kind.With_subkind.any_value
           | _ -> Misc.fatal_error "Expected variable") params
      |> Bound_parameters.create
    in
    let x = Bound_for_lambda.create
        ~return_continuation:ret
        ~exn_continuation:exn
        ~params:params'
        ~my_region:region
    in
    let l = NVar clo :: NCont ret :: NCont exn :: NVar region :: params in
    Core_function_params_and_body.create
      (Bound_var.create clo Name_mode.normal)
      (Core_lambda.create
          x
          (quote (l @ ns)
            (appCl { names = l; fun_env; val_env; exp})))
    | _ -> Misc.fatal_error "Mismatched [quote_code]")[@ocaml.warning "-8"]

and quote_static_const ns s : static_const =
  match s with
  | Block (tag, mut, l) ->
    let l = List.map (quote ns) l in
    Block (tag, mut, l)
  | Boxed_float t -> Boxed_float t
  | Boxed_int32 t -> Boxed_int32 t
  | Boxed_int64 t -> Boxed_int64 t
  | Boxed_nativeint t -> Boxed_nativeint t
  | Immutable_float_block t -> Immutable_float_block t
  | Immutable_float_array t -> Immutable_float_array t
  | Immutable_value_array t -> Immutable_value_array t
  | Empty_array -> Empty_array
  | Mutable_string { initial_value } -> Mutable_string { initial_value }
  | Immutable_string s -> Immutable_string s

and quote_prim ns (e : primitive_value) : core_exp =
  (match e with
  | Nullary e -> Nullary e
  | Unary (p, e) -> Unary (p, quote ns e)
  | Binary (p, e1, e2) ->
    Binary (p, quote ns e1, quote ns e2)
  | Ternary (p, e1, e2, e3) ->
   Ternary (p, quote ns e1, quote ns e2, quote ns e3)
  | Variadic (p, l) ->
    Variadic (p, List.map (quote ns) l))
  |> Eval_prim.eval

let nf (env : (name * value) list) (t : core_exp) =
  quote (List.map fst env) (eval [] env t)

let normalize = nf []
