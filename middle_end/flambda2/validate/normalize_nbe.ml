open! Flambda
open! Flambda2_core
open! Translate

module P = Flambda_primitive

type name =
  | NCont of Continuation.t
  | NResCont of Apply_expr.Result_continuation.t
  | NVar of Variable.t
  (* | NSimple of Simple.t *)
  | NSlot of Variable.t * slot
  | NCode of Code_id.t
  | NSymbol of Symbol.t
  | NLambda of Bound_for_lambda.t
  | NParams of Bound_parameters.t
  | NList of name list

(* Semantic values of Flambda2 terms

   Each term gets translated into an open singleton term with names and closures
   in place of abstraction *)
type value =
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
  | VClosure_expr of
      (Variable.t * Function_slot.t * closure)
  | VSet_of_closures of set_of_closures
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
  | Static_set_of_closures of set_of_closures
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

and env = (name * value) list

(* A closure is a list of names, environment, and a core expression *)
and closure = Close of name list * env * core_exp

let let_bound_to_name (t : Bound_for_let.t) : name =
  match t with
  | Singleton v ->
    NVar (Bound_var.var v)
  | Static c ->
    let l = Bound_codelike.to_list c in
    let to_name c =
    (match c with
     | Bound_codelike.Pattern.Code c -> NCode c
     | Bound_codelike.Pattern.Set_of_closures v ->
       NVar (Bound_var.var v)
     | Bound_codelike.Pattern.Block_like s ->
       NSymbol s)
    in
    NList (List.map to_name l)

(* Analogous to [reflect] *)
let rec eval (env : (name * value) list) (e : core_exp) =
  match Expr.descr e with
  | Let e ->
    let x, e1, e2 =
      Core_let.pattern_match e
        ~f:(fun ~x ~e1 ~e2 -> x, e1, e2)
    in
    Format.fprintf Format.std_formatter "let %a @." print e1;
    let x = let_bound_to_name x in
    eval ((x, eval env e1)::env) e2
  | Let_cont {handler; body} ->
    Format.fprintf Format.std_formatter "LetCont@.";
    let e2 = With_delayed_renaming.create (Handler handler) in
    let k, e1 =
      Core_letcont_body.pattern_match body
        (fun k e1 -> k, e1)
    in
    eval ((NCont k, eval env e2)::env) e1
  | Apply
      {callee; continuation; exn_continuation;
       region; apply_args} ->
    Format.fprintf Format.std_formatter "Apply@.";
    let apply_args = List.map (eval env) apply_args in
    (match eval env callee with
    | VLambda (Close (xs, env', t)) ->
      let args = List.combine xs apply_args in
      eval (args @ env') t
    | t ->
      VApply
      {callee = t;
       continuation = eval env continuation;
       exn_continuation = eval env exn_continuation;
       region = eval env region;
       apply_args})[@ocaml.warning "-4"]
  | Apply_cont {k ; args} ->
    let args = List.map (eval env) args in
    (match eval env k with
     | VHandler (Close (xs, env', t)) ->
       let args = List.combine xs args in
       eval (args @ env') t
     | t ->
       VApplyCont {k = t; args}
    )[@ocaml.warning "-4"]
  | Lambda t ->
    let x, e =
      Core_lambda.pattern_match t ~f:(fun b e -> b, e)
    in
    VLambda (Close ([NLambda x], env, e))
  | Handler t ->
    let x, e =
      Core_continuation_handler.pattern_match t
        (fun b e -> b, e)
    in
    VHandler (Close ([NParams x], env, e))
  | Switch {scrutinee; arms} ->
    VSwitch {
      scrutinee = eval env scrutinee;
      arms = Targetint_31_63.Map.map (eval env) arms
    }
  | Named e ->
    Format.fprintf Format.std_formatter "Named@.";
    eval_named env e
  | Invalid { message } -> VInvalid { message }

and closure_expr_to_closure
    (phi : Variable.t)
    (env: (name * value) list)
    ({function_decls; value_slots} : set_of_closures)
  : (name * value) list =
  (* Substitute in the value slots first *)
  let value_slots_list =
    Value_slot.Map.map (eval env) value_slots |>
    Value_slot.Map.to_seq |> List.of_seq in
  let value_slots =
    List.map (fun (k, v) ->
        (NSlot (phi, Value_slot k), v))
      value_slots_list
  in
  let env = value_slots @ env in
  let function_decls_list =
    SlotMap.map (eval env) function_decls |>
    SlotMap.to_seq |> List.of_seq
  in
  let function_decls =
    List.map (fun (k, v) -> (NSlot (phi, Function_slot k), v))
      function_decls_list
  in
  function_decls @ env

and eval_named (env : (name * value) list) (e : named) =
  match e with
  | Literal l -> eval_literal env l
  | Prim p -> eval_prim env p
  | Closure_expr (var, fn, clos) ->
    let env =
      closure_expr_to_closure var env clos
    in
    List.assoc (NSlot (var, Function_slot fn)) env
  | Set_of_closures clos ->
    VNamed (VSet_of_closures clos)
  | Static_consts consts ->
    VNamed
      (VStatic_consts
         (List.map (eval_static_const_or_code env) consts))
  | Rec_info v -> VNamed (VRec_info v)

and eval_static_const_or_code (env : (name * value) list)
    (c : static_const_or_code) :
  static_const_or_code_value =
  match c with
  | Code f -> eval_function_params_and_body env f
  | Deleted_code -> VDeleted_code
  | Static_const s -> VStatic_const (eval_static_const env s)

and eval_function_params_and_body (env : (name * value) list) ({expr; _} : Flambda2_core.function_params_and_body) =
  let v, args, e =
    Core_function_params_and_body.pattern_match
      expr ~f:(fun v t ->
          let args, e =
            Core_lambda.pattern_match t ~f:(fun b e -> b, e)
          in (v, args, e))
  in
  VCode (Close ([NVar (Bound_var.var v); NLambda args],
                  env, e))

and eval_static_const
    (env : (name * value) list) (s : static_const) =
  match s with
  | Static_set_of_closures s -> Static_set_of_closures s
  | Block (tag, mut, l) ->
    let l = List.map (eval env) l in
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

and print_name (n : name) =
  match n with
  | NVar s ->
    Format.fprintf Format.std_formatter "var %a @."
      Variable.print s
  | _ ->
    Format.fprintf Format.std_formatter "something @."

and print_env (env : (name * value) list) =
    List.iter (fun (n, _) -> print_name n) env

and eval_literal (env : (name * value) list) (e : literal) =
  Format.fprintf Format.std_formatter "Literal %a @." Flambda2_core.print_literal e;
  print_env env;
  match e with
  | Simple s ->
    (match Simple.must_be_var s with
    | Some (s, _) -> List.assoc (NVar s) env
    | None -> VNamed (VLiteral (VSimple s)))
  | Cont k ->
    (match List.assoc_opt (NCont k) env with
     | Some s -> s
     | None -> VNamed (VLiteral (VCont k)))
  | Res_cont k -> List.assoc (NResCont k) env
  | Code_id id -> List.assoc (NCode id) env
  | Slot (var, slot) -> List.assoc (NSlot (var, slot)) env

and eval_prim (env : (name * value) list) (e : primitive) =
  (match e with
    | Nullary e ->
      VNamed (VPrim (Nullary e))
    | Unary (p, e) ->
      VNamed (VPrim (Unary (p, eval env e)))
    | Binary (p, e1, e2) ->
      VNamed (VPrim (Binary (p, eval env e1, eval env e2)))
    | Ternary (p, e1, e2, e3) ->
      VNamed (VPrim (Ternary
        (p, eval env e1, eval env e2, eval env e3)))
    | Variadic (p, list) ->
      VNamed (VPrim (Variadic (p, List.map (eval env) list))))

let appCl (Close (x, env, t) : closure) (v : value list) : value =
  let env' = List.combine x v in
  eval (env' @ env) t

let closure_to_soc _clo : set_of_closures =
  failwith "Unimplemented closure to soc"

let rec quote (ns : name list) (t : value) : core_exp =
  match t with
  | VNamed e ->
    With_delayed_renaming.create (Named (quote_named ns e))
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
        { k = quote ns k; args = List.map (quote ns) args }
    in
    With_delayed_renaming.create e
  | VLambda (Close ([NLambda x], env, t)) ->
    let e =
      Lambda
        (Core_lambda.create
          x
          (quote (NLambda x :: ns)
              (appCl (Close ([NLambda x], env, t))
                              (List.map snd env))))
    in
    With_delayed_renaming.create e
  | VHandler (Close ([NParams l], env, t)) ->
    let e =
      Handler
        (Core_continuation_handler.create
           l
           (quote (NParams l :: ns)
              (appCl (Close ([NParams l], env, t))
                 (List.map snd env))))
    in
    With_delayed_renaming.create e
  | VSwitch { scrutinee ; arms } ->
    let scrutinee = quote ns scrutinee in
    let arms = Targetint_31_63.Map.map (quote ns) arms in
    With_delayed_renaming.create
      (Switch {scrutinee = scrutinee; arms = arms})
  | VInvalid { message } ->
    With_delayed_renaming.create (Invalid { message })
  | VLambda _ | VHandler _ ->
    failwith "[VLambda/VHandler-quote] Unexpected closure length"

and quote_named ns (e : named_value) : named =
  match e with
  | VLiteral s ->
    Literal
      (match s with
       | VSimple s -> Simple s
       | VCont k -> Cont k
       | VRes_cont k -> Res_cont k
       | VSlot s -> Slot s
       | VCode_id id -> Code_id id)
  | VPrim p -> quote_prim ns p
  | VClosure_expr (var, slot, clo) ->
    Closure_expr (var, slot, closure_to_soc clo)
  | VSet_of_closures soc ->
    Set_of_closures soc (* TODO *)
  | VStatic_consts _group ->
    failwith "Unimplemented static_consts"
  | VRec_info rec_info -> Rec_info rec_info

and quote_prim ns (e : primitive_value) : named =
  match e with
  | Nullary e ->
    (Prim (Nullary e))
  | Unary (p, e) ->
    (Prim (Unary (p, quote ns e)))
  | Binary (p, e1, e2) ->
    (Prim (Binary (p, quote ns e1, quote ns e2)))
  | Ternary (p, e1, e2, e3) ->
    (Prim (Ternary (p, quote ns e1, quote ns e2, quote ns e3)))
  | Variadic (p, l) ->
    (Prim (Variadic (p, List.map (quote ns) l)))

let nf (env : (name * value) list) (t : core_exp) =
  quote (List.map fst env) (eval env t)

let normalize = nf []
