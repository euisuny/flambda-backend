open! Flambda
open! Flambda2_core
open! Translate

module P = Flambda_primitive

let fuel = ref 0
let fuel_limit = 10

type name =
  | NCont of Continuation.t
  | NVar of Variable.t
  | NSlot of Value_slot.t
  | NCode of Code_id.t
  | NSymbol of Symbol.t

type fun_name = Variable.t

(* Semantic values of Flambda2 terms

   Each term gets translated into an open singleton term with names and closures
   in place of abstraction *)
type value =
  | VFun of Variable.t
  | VNamed of named_value
  | VApply of apply_value
  | VLambda of closure
  | VSwitch of switch_value
  | VConst of const_value
  | VRec of value list
  | VInvalid of { message : string }

and apply_value =
  { callee: value;
    apply_args: value list; }

and switch_value =
  { scrutinee : value;
    arms : value Targetint_31_63.Map.t }

and literal_value =
  | VSimple of Simple.t
  | VCont of Continuation.t
  | VRes_cont of Apply_expr.Result_continuation.t
  | VSlot of (Variable.t * slot)
  | VCode_id of Code_id.t

and named_value =
  | VLiteral of literal_value
  | VPrim of primitive_value
  | VRec_info of Rec_info_expr.t

and primitive_value =
  | Nullary of P.nullary_primitive
  | Unary of P.unary_primitive * value
  | Binary of P.binary_primitive * value * value
  | Ternary of P.ternary_primitive * value * value * value
  | Variadic of P.variadic_primitive * value list

and const_value =
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

and value_env = (name * value) list
and function_env = ((fun_name * Function_slot.t) * closure) list

(* A closure is a list of names, function and value environment, and a core
   expression *)
and closure =
  { names : name list;
    fun_env : function_env;
    val_env : value_env;
    exp: core_exp }

(* Analogous to [reflect] *)
let rec eval fenv (venv : (name * value) list) (e : core_exp) : value =
  match Expr.descr e with
  | Let e ->
    let x, e1, e2 =
      Core_let.pattern_match e
        ~f:(fun ~x ~e1 ~e2 -> x, e1, e2)
    in
    let (fenv', env') = let_bound_to_name fenv venv x e1 in
    eval fenv' (env' @ venv) e2

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
    (match eval fenv venv callee with
    | VLambda {names =
        NCont ret :: NCont ex :: NVar reg :: params ;
        fun_env ; val_env ; exp } ->

      let l = [(NCont ret, eval fenv venv continuation);
              (NCont ex, eval fenv venv exn_continuation);
              (NVar reg, eval fenv venv region);
              (NVar reg, eval fenv venv region)] in
      let args = List.combine params apply_args' in
      eval (fun_env @ fenv) (l @ args @ val_env @ venv) exp
    | t ->
      let continuation = eval fenv venv continuation in
      let exn_continuation = eval fenv venv exn_continuation in
      let region = eval fenv venv region in
      VApply
      {callee = t;
        apply_args =
          continuation :: exn_continuation :: region :: apply_args'}
    )[@ocaml.warning "-4"]

  | Apply_cont {k ; args} ->
    let args = List.map (eval fenv venv) args in
    (match eval fenv venv k with
     | VLambda {names; fun_env; val_env; exp} ->
       let args = List.combine names args in
       eval (fun_env @ fenv) (args @ val_env) exp
     | t ->
       VApply {callee = t; apply_args = args})[@ocaml.warning "-4"]

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
    VLambda
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
  : function_env * value_env =
  match t with
  | Singleton v ->
    let nvar = NVar (Bound_var.var v) in
    (match must_be_named e with
     | Some e ->
       (match e with
        | Literal l ->
          (fenv, [(nvar, eval_literal fenv venv l)])
        | Prim p ->
          (fenv, [(nvar, eval fenv venv (Eval_prim.eval p))])
        | Closure_expr (var, fn, clos) ->
          let slot =
            Named (Literal (Slot (var, Function_slot fn)))
            |> With_delayed_renaming.create
          in
          let fenv =
            closure_expr_to_closure fenv var venv clos
          in
          let x = eval fenv venv slot in
          (fenv, [(nvar, x)])
        | Set_of_closures clos ->
            (closure_expr_to_closure
              fenv (Bound_var.var v)
              venv clos, venv)
        | Static_consts _ ->
          Misc.fatal_error
            "Expected static variable to be bound for static constants"
        | Rec_info v -> (fenv, [(nvar, VNamed (VRec_info v))]))
     | None ->
        (fenv, [(NVar (Bound_var.var v), eval fenv venv e)])
    )
  | Static c ->
    (match must_be_static_consts e with
     | Some group ->
       let binding = List.combine c group in
       let (code, remain) = List.partition (fun (_, x) -> is_code x) binding in
       let group fenv venv ((c, e) : Bound_codelike.Pattern.t * static_const_or_code) :
         function_env * value_env =
         (match c with
          | Bound_codelike.Pattern.Code c ->
            let e = Expr.create_named (Static_consts [e]) in
            (fenv, [(NCode c, eval fenv venv e)])
          | Bound_codelike.Pattern.Set_of_closures v ->
            (match e with
             | Static_const (Static_set_of_closures clos) ->
                (closure_expr_to_closure fenv (Bound_var.var v) venv clos, venv)
             | _ -> Misc.fatal_error "Expected static closure body")
          | Bound_codelike.Pattern.Block_like s  ->
            let e = Expr.create_named (Static_consts [e]) in
            (fenv, [(NSymbol s, eval fenv venv e)])) in
       let code_x : (function_env * value_env) list = List.map (group fenv venv) code in
       let (fenv', venv') =
         List.fold_right
          (fun (fenv, venv) (facc, vacc) -> (fenv @ facc, venv @ vacc)) code_x ([], []) in
       let remain_x : (function_env * value_env) list = List.map (group (fenv' @ fenv) (venv' @ venv)) remain in
       let (fenv'', venv'') =
         List.fold_right
           (fun (fenv, venv) (facc, vacc) -> (fenv @ facc, venv @ vacc)) remain_x ([], []) in
       (fenv'' @ fenv', venv'' @ venv')

     | None -> Misc.fatal_error "Expected static consts body")

and closure_expr_to_closure
    (fenv : function_env)
    (phi : Variable.t)
    (venv: (name * value) list)
    ({function_decls; value_slots} : set_of_closures) :
  function_env =
  let value_slots_list =
    Value_slot.Map.map (eval fenv venv) value_slots |>
    Value_slot.Map.to_seq |> List.of_seq in
  let value_slots =
    List.map (fun (k, v) -> (NSlot k, v))
      value_slots_list
  in
  let env = value_slots @ venv in
  let phi_value : function_env =
    SlotMap.to_seq function_decls |>
    List.of_seq |>
    List.map (fun (i, x) -> ((phi, i),
       match eval fenv venv x with
       | VLambda clo -> clo
       | _ ->
         _print_env env;
         Format.fprintf Format.std_formatter
           "%a" Flambda2_core.print x;
         Misc.fatal_error
                "[cetc] expected closure"
     ))
  in
  let function_decls_list =
    let x = SlotMap.to_seq function_decls |> List.of_seq in
    List.fold_right
      (fun (x, v) acc ->
         match x with
         | Function_slot s -> (s, v) :: acc
         | _ -> acc) [] x in

  let function_decls_list : function_env =
    function_decls_list |>
    List.map
      (fun (i, x) ->
        ((phi, i),
         match must_be_code_id x with
         | Some id ->
           (match (List.assoc_opt (NCode id) env) with
            | Some (VLambda { names = NVar v :: NCont c :: names ;
                              fun_env; val_env; exp }) ->
              (* Value slot extends the environment captured for a function *)
              { names = NCont c :: names;
                fun_env = phi_value @ fenv @ fun_env;
                val_env = (NVar v, VNamed (VLiteral
                            (VSlot (phi, Function_slot i))))
                          :: (NVar phi, VFun phi)
                          :: value_slots @ val_env @ venv;
                exp = exp }
            | Some (VLambda { names; fun_env; val_env; exp }) ->
              (* Value slot extends the environment captured for a function *)
                { names = names;
                  fun_env = phi_value @ fenv @ fun_env;
                  val_env = (NVar phi, VFun phi) ::
                      value_slots @ val_env @ venv;
                  exp = exp }
            | _->
              Misc.fatal_error "Expected closure")
          | None ->
             let x = eval (phi_value @ fenv)
                        ((NVar phi, VFun phi):: venv) x in
              (match x with
              | VLambda e -> e;
              | _ -> Misc.fatal_error "Expected closure")))
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
    let fenv =
      closure_expr_to_closure fenv var venv clos
    in
    eval fenv venv slot
  | Set_of_closures _ ->
    Misc.fatal_error "[eval_named] Unreachable: set of closures"
  | Static_consts consts ->
    let x =
      (List.fold_right
         (fun x acc ->
            match eval_static_const_or_code fenv venv x with
            | Some x -> x :: acc
            | None -> acc) consts [])
    in
    if List.length x > 1
    then (VRec x)
    else if List.length x > 0
    then List.hd x else VInvalid {message = "Empty const"}
  | Rec_info v -> VNamed (VRec_info v)

and eval_static_const_or_code
    (fenv : function_env) (venv : value_env)
    (c : static_const_or_code) : value option =
  match c with
  | Code f -> Some (eval_function_params_and_body fenv venv f)
  | Deleted_code -> None
  | Static_const s -> Some (VConst (eval_static_const fenv venv s))

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
  VLambda
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
  | NSlot s ->
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

and _print_fenv (env : function_env) =
  Format.fprintf Format.std_formatter "------- fun_env -------@.";
  List.iter (fun ((v, slot), _) ->
      Format.fprintf Format.std_formatter "(%a, %a)@."
        Variable.print v
        Function_slot.print slot) env;
  Format.fprintf Format.std_formatter "-------------------@.@."

and _print_value (x : value) =
  match x with
  | VFun v -> Format.fprintf Format.std_formatter "%a" Variable.print v
  | VNamed _ ->
    Format.fprintf Format.std_formatter "named"
  | VApply _ ->
    Format.fprintf Format.std_formatter "apply"
  | VLambda _ ->
    Format.fprintf Format.std_formatter "lambda"
  | VSwitch _ ->
    Format.fprintf Format.std_formatter "switch"
  | VConst _ ->
    Format.fprintf Format.std_formatter "const"
  | VRec _ ->
    Format.fprintf Format.std_formatter "rec"
  | VInvalid { message } ->
    Format.fprintf Format.std_formatter "%s" message

and _fenv_to_soc name (fenv: function_env) : set_of_closures =
  let seq =
    List.map
      (fun ((_, slot) , clo) ->
         (slot, quote name (VLambda clo))) fenv
    |> List.to_seq
  in
  {function_decls = SlotMap.of_seq seq;
   value_slots = Value_slot.Map.empty }

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
  | Slot (var, Function_slot slot) -> (* TODO : Add fuel *)
    (if (!fuel < fuel_limit) then
    (fuel := !fuel + 1;
    (match (List.assoc_opt (var, slot) fenv) with
      | Some {names; fun_env; val_env; exp} ->
        ((* TODO more fine-grained fuel checking *)
          (* let (_, fun_env) = List.partition (fun (k, _) -> k == (var, slot)) fun_env in *)
          (* let (_, val_env) = List.partition (fun (k, _) -> k == NVar var) val_env in *)
          VLambda {names; fun_env = fenv @ fun_env ;
                   val_env = env @ val_env ; exp})
      | None ->
        VNamed (VLiteral (VSlot (var, (Function_slot slot))))))
    else
      (VNamed (VLiteral (VSlot (var, (Function_slot slot))))))

  | Slot (_, Value_slot slot) ->
    let x  = List.assoc_opt (NSlot slot) env in
    (_print_env env;
    (match x with
     | Some (VNamed (VLiteral (VCode_id i))) ->
       (match List.assoc_opt (NCode i) env with
        | Some x -> x
        | None -> (VNamed (VLiteral (VCode_id i))))
     | Some x -> x
     | None -> Misc.fatal_error "Not found: value_slot"))

and eval_prim (fenv : function_env) (venv : value_env)
    (e : primitive) =
  (match e with
    | Nullary e ->
      VNamed (VPrim (Nullary e))
    | Unary (Project_value_slot
        { project_from ; value_slot = slot; kind }, arg) ->
      let x = List.assoc_opt (NSlot slot) venv in
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
      (let x : function_env = List.filter (fun ((_, x), _) -> x == move_to) fenv in
      (match x with
        | [(_, x)] -> VLambda x
        | _ ->
          VNamed
            (VPrim (Unary (Project_function_slot { move_from ; move_to },
                eval fenv venv arg)))))
    | Unary (p, e) ->
      VNamed (VPrim (Unary (p, eval fenv venv e)))
    | Binary (p, e1, e2) ->
      VNamed (VPrim (Binary (p, eval fenv venv e1, eval fenv venv e2)))
    | Ternary (p, e1, e2, e3) ->
      VNamed (VPrim (Ternary
        (p, eval fenv venv e1, eval fenv venv e2, eval fenv venv e3)))
    | Variadic (p, list) ->
      VNamed (VPrim (Variadic (p, List.map (eval fenv venv) list))))

and appCl ({names = _; fun_env; val_env; exp} : closure) : value =
  eval fun_env val_env exp

and quote (ns : name list) (t : value) : core_exp =
  match t with
  | VNamed e -> quote_named ns e
  | VApply {callee ; apply_args} ->
    let e =
      Apply_cont
        { k = quote ns callee;
          args = List.map (quote ns) apply_args }
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
  | VLambda { names; fun_env; val_env; exp } ->
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
  | VFun var ->
      (Named (Literal (Simple (Simple.var var)))
            |> With_delayed_renaming.create)
  | VConst c ->
      Named (Static_consts [Static_const (quote_const ns c)])
        |> With_delayed_renaming.create
  | _ -> failwith "Unimplemented"

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
  | VRec_info rec_info ->
    Named (Rec_info rec_info)
    |> With_delayed_renaming.create

and quote_const ns s : static_const =
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

let normalize f =
  fuel := f;
  nf []
