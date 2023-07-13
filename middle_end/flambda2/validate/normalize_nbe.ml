open! Flambda
open! Flambda2_core
open! Translate

module P = Flambda_primitive

type name =
  | NCont of Continuation.t
  | NResCont of Apply_expr.Result_continuation.t
  | NVar of Variable.t
  | NSimple of Simple.t
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

and named_value =
  | VPrim of primitive_value
  | VClosure_expr of
      (Variable.t * Function_slot.t * set_of_closures_value)
  | VSet_of_closures of set_of_closures_value
  | Static_consts of static_const_group_value
  | Rec_info

and primitive_value =
  | Nullary of P.nullary_primitive
  | Unary of P.unary_primitive * value
  | Binary of P.binary_primitive * value * value
  | Ternary of P.ternary_primitive * value * value * value
  | Variadic of P.variadic_primitive * value list

and set_of_closures_value =
  { function_decls : function_declarations;
    value_slots : value Value_slot.Map.t}

(* functions that are in-order *)
and function_declarations = value SlotMap.t

and function_params_and_body_value =
  { expr: (Bound_var.t, closure) Name_abstraction.t;
    anon: bool }

and static_const_or_code_value =
  | Code of function_params_and_body_value
  | Deleted_code
  | Static_const of static_const_value

and static_const_value =
  | Static_set_of_closures of set_of_closures_value
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
    let x = let_bound_to_name x in
    eval ((x, eval env e1)::env) e2
  | Let_cont {handler; body} ->
    let e2 = With_delayed_renaming.create (Handler handler) in
    let k, e1 =
      Core_letcont_body.pattern_match body
        (fun k e1 -> k, e1)
    in
    eval ((NCont k, eval env e2)::env) e1
  | Apply
      {callee; continuation; exn_continuation;
       region; apply_args} ->
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
  | Named e -> eval_named env e
  | Invalid { message } -> VInvalid { message }

and eval_named (env : (name * value) list) (e : named) =
  match e with
  | Literal l -> eval_literal env l
  | Prim p -> eval_prim env p
  | Closure_expr (var, fn, {function_decls; value_slots}) ->
    let _var =
      List.assoc (NSlot (var, Function_slot fn)) env
    in
    let _clos =
      VSet_of_closures
        {function_decls =
          SlotMap.map (eval env) function_decls;
        value_slots =
          Value_slot.Map.map (eval env) value_slots}
    in
    failwith "Unimplemented"
  | Set_of_closures {function_decls; value_slots} ->
      VSet_of_closures
        {function_decls =
           SlotMap.map (eval env) function_decls;
         value_slots =
           Value_slot.Map.map (eval env) value_slots}
  | Static_consts _consts ->
    failwith "Unimplemented"
  | Rec_info _ ->
    failwith "Unimplemented"

and eval_literal (env : (name * value) list) (e : literal) =
  match e with
  | Simple s -> List.assoc (NSimple s) env
  | Cont k -> List.assoc (NCont k) env
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

let quote_named (_e : named_value) : named =
  failwith "Unimplemented"

let rec quote (ns : name list) (t : value) : core_exp =
  match t with
  | VNamed e ->
    With_delayed_renaming.create (Named (quote_named e))
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

let nf (env : (name * value) list) (t : core_exp) =
  quote (List.map fst env) (eval env t)

let normalize = nf []
