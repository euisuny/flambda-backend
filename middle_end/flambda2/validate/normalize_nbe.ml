open! Flambda
open! Flambda2_core
open! Translate

type name =
  | NCont of Continuation.t
  | NVar of Variable.t
  | NCode of Code_id.t
  | NSymbol of Symbol.t
  | NLambda of Bound_for_lambda.t
  | NParams of Bound_parameters.t
  | NList of name list

type value =
  | VNamed of named
  | VApply of apply_value
  | VApplyCont of apply_cont_value
  | VLambda of closure
  | VHandler of closure
  | VSwitch of switch_value
  | VInvalid of { message : string }

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
  | Named _ -> failwith "Unimplemented"
  | Invalid { message } -> VInvalid { message }

let normalize = failwith "Unimplemented"
