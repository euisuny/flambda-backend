open! Flambda

module P = Flambda_primitive
let fprintf = Format.fprintf

(** Simplified core of [flambda2] terms **)
(* (1) Simple.t -> core_exp for [Apply*] expressions
   (2) Ignore [Num_occurrences] (which is used for making inlining decisions)
   (3) Ignored traps for now *)

type core_exp =
  | Named of named
  | Let of let_expr
  | Let_cont of let_cont_expr
  | Apply of apply_expr
  | Apply_cont of apply_cont_expr
  | Switch of switch_expr
  | Invalid of { message : string }

(** Let expressions [let x = e1 in e2]

   [fun x -> e2] = let_abst
   [e1] = body **)
and let_expr =
  { let_abst : (Bound_pattern.t, core_exp) Name_abstraction.t;
    body : core_exp; }

and named =
  | Simple of Simple.t
  | Prim of primitive
  | Set_of_closures of Set_of_closures.t
  | Static_consts of static_const_group
  | Rec_info of Rec_info_expr.t

and primitive =
  | Nullary of P.nullary_primitive
  | Unary of P.unary_primitive * core_exp
  | Binary of P.binary_primitive * core_exp * core_exp
  | Ternary of P.ternary_primitive * core_exp * core_exp * core_exp
  | Variadic of P.variadic_primitive * core_exp list

and function_params_and_body =
  (Bound_for_function.t, core_exp) Name_abstraction.t

and static_const_or_code =
  | Code of function_params_and_body Code0.t
  | Deleted_code
  | Static_const of Static_const.t

and static_const_group = static_const_or_code list

and let_cont_expr =
  (* Non-recursive case [e1 where k x = e2]

     [fun x -> e2] = handler
     bound variable [k] = Bound_continuation.t
     [e1] = body (has bound variable [k] in scope) *)
  | Non_recursive of
    { handler : continuation_handler;
      body : (Bound_continuation.t, core_exp) Name_abstraction.t;}

  (* Recursive case, we have a set of (mutually recursive) continuations
     [let rec K x in e] where [K] is a map of continuations
     [x] is the set of invariant parameters
     bound variable [K] is in the scope of [e]

     [x] = invariant_params (Bound_parameters.t)
     [K] = continuation_map
     [e] = body *)
  | Recursive of
      (Bound_continuations.t, recursive_let_expr) Name_abstraction.t

and recursive_let_expr =
  { continuation_map :
      (Bound_parameters.t, continuation_handler_map) Name_abstraction.t;
    body : core_exp; }

and continuation_handler_map =
  continuation_handler Continuation.Map.t

and continuation_handler =
  (Bound_parameters.t, core_exp) Name_abstraction.t

and apply_expr =
  { callee: core_exp;
    continuation: Apply_expr.Result_continuation.t;
    exn_continuation: Continuation.t;
    args: core_exp list;
    call_kind: Call_kind.t; }

and apply_cont_expr =
  { k : Continuation.t;
    args : core_exp list }

and switch_expr =
  { scrutinee : core_exp;
    arms : core_exp Targetint_31_63.Map.t }

(** Nominal renaming for [core_exp] **)
let rec apply_renaming t renaming : core_exp =
  match t with
  | Named t -> Named (apply_renaming_named t renaming)
  | Let t -> Let (apply_renaming_let t renaming)
  | Let_cont t -> Let_cont (apply_renaming_let_cont t renaming)
  | Apply t -> Apply (apply_renaming_apply t renaming)
  | Apply_cont t -> Apply_cont (apply_renaming_apply_cont t renaming)
  | Switch t -> Switch (apply_renaming_switch t renaming)
  | Invalid t -> Invalid t

(* renaming for [Let] *)
and apply_renaming_let { let_abst; body } renaming : let_expr =
  let let_abst' =
    Name_abstraction.apply_renaming
      (module Bound_pattern)
      let_abst renaming
      ~apply_renaming_to_term:apply_renaming
  in
  let defining_expr' = apply_renaming body renaming in
  { let_abst = let_abst'; body = defining_expr' }

and apply_renaming_named t renaming : named =
  match t with
  | Simple simple ->
    Simple (Simple.apply_renaming simple renaming)
  | Prim prim ->
    Prim (apply_renaming_prim prim renaming)
  | Set_of_closures set ->
    Set_of_closures (Set_of_closures.apply_renaming set renaming)
  | Static_consts consts ->
    Static_consts (apply_renaming_static_const_group consts renaming)
  | Rec_info info ->
    Rec_info (Rec_info_expr.apply_renaming info renaming)

and apply_renaming_prim t renaming : primitive =
  match t with
  | Nullary (Invalid _ | Optimised_out _ | Probe_is_enabled _ | Begin_region) ->
    t
  | Unary (prim, arg) ->
    let prim = P.apply_renaming_unary_primitive prim renaming in
    let arg = apply_renaming arg renaming in
    Unary (prim, arg)
  | Binary (prim, arg1, arg2) ->
    let prim = P.apply_renaming_binary_primitive prim renaming in
    let arg1 = apply_renaming arg1 renaming in
    let arg2 = apply_renaming arg2 renaming in
    Binary (prim, arg1, arg2)
  | Ternary (prim, arg1, arg2, arg3) ->
    let prim = P.apply_renaming_ternary_primitive prim renaming in
    let arg1 = apply_renaming arg1 renaming in
    let arg2 = apply_renaming arg2 renaming in
    let arg3 = apply_renaming arg3 renaming in
    Ternary (prim, arg1, arg2, arg3)
  | Variadic (prim, args) ->
    let prim = P.apply_renaming_variadic_primitive prim renaming in
    let args = List.map (fun x -> apply_renaming x renaming) args in
    Variadic (prim, args)

and apply_renaming_static_const_group t renaming : static_const_group =
  List.map (fun static_const ->
    apply_renaming_static_const_or_code static_const renaming) t

and apply_renaming_static_const_or_code t renaming : static_const_or_code =
  match t with
  | Code code ->
    Code (Code0.apply_renaming
            ~apply_renaming_function_params_and_body code renaming)
  | Deleted_code -> Deleted_code
  | Static_const const ->
    Static_const (Static_const.apply_renaming const renaming)

and apply_renaming_function_params_and_body t renaming =
  Name_abstraction.apply_renaming
    (module Bound_for_function) t renaming ~apply_renaming_to_term:apply_renaming

(* renaming for [Let_cont] *)
and apply_renaming_let_cont t renaming : let_cont_expr =
  match t with
  | Non_recursive { handler; body } ->
    let handler =
      apply_renaming_cont_handler handler renaming
    in
    let body =
      Name_abstraction.apply_renaming
        (module Bound_continuation)
        body renaming ~apply_renaming_to_term:apply_renaming
    in
    Non_recursive { handler = handler ; body = body }
  | Recursive t ->
    Recursive (Name_abstraction.apply_renaming
        (module Bound_continuations)
        t renaming ~apply_renaming_to_term:apply_renaming_recursive_let_expr)

and apply_renaming_recursive_let_expr {continuation_map; body} renaming
  : recursive_let_expr =
  let continuation_map =
    Name_abstraction.apply_renaming
      (module Bound_parameters)
      continuation_map renaming ~apply_renaming_to_term:apply_renaming_cont_map
  in
  { continuation_map = continuation_map ;
    body = apply_renaming body renaming }

and apply_renaming_cont_handler t renaming : continuation_handler =
  Name_abstraction.apply_renaming
    (module Bound_parameters)
    t renaming ~apply_renaming_to_term:apply_renaming

and apply_renaming_cont_map t renaming : continuation_handler_map =
  Continuation.Map.fold
    (fun k handler result ->
       let k = Renaming.apply_continuation renaming k in
       let handler = apply_renaming_cont_handler handler renaming in
       Continuation.Map.add k handler result) t Continuation.Map.empty

(* renaming for [Apply] *)
and apply_renaming_apply
      { callee; continuation; exn_continuation; args; call_kind} renaming:
  apply_expr =
  let continuation =
    Apply_expr.Result_continuation.apply_renaming continuation renaming in
  let exn_continuation =
    Renaming.apply_continuation renaming exn_continuation in
  let callee = apply_renaming callee renaming in
  let args = List.map (fun x -> apply_renaming x renaming) args in
  let call_kind = Call_kind.apply_renaming call_kind renaming in
  { callee = callee; continuation = continuation;
    exn_continuation = exn_continuation; args = args; call_kind = call_kind }

(* renaming for [Apply_cont] *)
and apply_renaming_apply_cont {k; args} renaming : apply_cont_expr =
  let k = Renaming.apply_continuation renaming k in
  let args = List.map (fun x -> apply_renaming x renaming) args in
  { k = k; args = args }

(* renaming for [Switch] *)
and apply_renaming_switch {scrutinee; arms} renaming : switch_expr =
  let scrutinee = apply_renaming scrutinee renaming in
  let arms = Targetint_31_63.Map.map (fun x -> apply_renaming x renaming) arms in
  { scrutinee = scrutinee; arms = arms }

(** Sexp-ish simple pretty-printer for [core_exp]s.
  Ignores name_stamp, compilation_unit, and debug_info for simplicity. **)
let rec print ppf e =
  fprintf ppf "(@[<hov 1>";
  (match e with
   | Named t ->
     fprintf ppf "named@ ";
     print_named ppf t;
   | Let t ->
     fprintf ppf "let@ ";
     print_let ppf t;
   | Let_cont t ->
     fprintf ppf "let_cont@ ";
     print_let_cont ppf t;
   | Apply t ->
     fprintf ppf "apply@ ";
     print_apply ppf t;
   | Apply_cont t ->
     fprintf ppf "apply_cont@ ";
     print_apply_cont ppf t;
   | Switch t ->
     fprintf ppf "switch@ ";
     print_switch ppf t;
   | Invalid { message } ->
     fprintf ppf "invalid %s" message);
  fprintf ppf "@])";

and print_let ppf ({let_abst; body} : let_expr) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_pattern)
    let_abst ~apply_renaming_to_term:apply_renaming
    ~f:(fun bound let_body ->
        fprintf ppf "(bound@ (%a),@ body@ (%a))@ in=%a"
        print_bound_pattern bound
        print body
        print let_body)

and print_bound_pattern ppf (t : Bound_pattern.t) =
  match t with
  | Singleton v ->
    fprintf ppf "singleton@ %a"
      Bound_var.print v
  | Set_of_closures v ->
    fprintf ppf "set_of_closures@ %a"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space
         Bound_var.print) v
  | Static v ->
    fprintf ppf "static@ %a"
      print_bound_static v

and print_bound_static ppf (t : Bound_static.t) =
  Format.fprintf ppf "@[<hov 0>%a@]"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space print_static_pattern)
    (t |> Bound_static.to_list)

and print_static_pattern ppf (t : Bound_static.Pattern.t) =
  match t with
  | Code v ->
    fprintf ppf "code@ %a" Code_id.print v
  | Set_of_closures v ->
    Format.fprintf ppf "set_of_closures@ %a"
      (Function_slot.Lmap.print Symbol.print) v
  | Block_like v ->
    Format.fprintf ppf "(block_like@ %a)" Symbol.print v

and print_named ppf (t : named) =
  match t with
  | Simple simple ->
    fprintf ppf "simple@ %a"
    Simple.print simple;
  | Prim prim ->
    fprintf ppf "prim@ %a"
    print_prim prim;
  | Set_of_closures clo ->
    fprintf ppf "set_of_closures@ %a"
    Set_of_closures.print clo
  | Static_consts consts ->
    fprintf ppf "static_consts@ %a"
    print_static_const_group consts
  | Rec_info info ->
    fprintf ppf "rec_info@ %a"
    Rec_info_expr.print info

and print_prim ppf (t : primitive) =
  match t with
  | Nullary prim ->
    print_nullary_prim ppf prim
  | Unary (prim, arg) ->
    fprintf ppf "(%a, %a)"
     P.print_unary_primitive prim
     print arg
  | Binary (prim, arg1, arg2) ->
    fprintf ppf "(%a, %a, %a)"
    P.print_binary_primitive prim
    print arg1
    print arg2
  | Ternary (prim, arg1, arg2, arg3) ->
    fprintf ppf "(%a, %a, %a, %a)"
    P.print_ternary_primitive prim
    print arg1
    print arg2
    print arg3
  | Variadic (prim, args) ->
    fprintf ppf "(%a, %a)"
    P.print_variadic_primitive prim
    (Format.pp_print_list ~pp_sep: Format.pp_print_space print) args



and print_nullary_prim ppf (t : P.nullary_primitive) =
  match t with
  | Invalid _ ->
    fprintf ppf "Invalid"
  | Optimised_out _ ->
    fprintf ppf "Optimised_out"
  | Probe_is_enabled { name } ->
    fprintf ppf "(Probe_is_enabled@ %s)" name
  | Begin_region ->
    fprintf ppf "Begin_region"

and print_static_const_group ppf t =
  Format.pp_print_list ~pp_sep:Format.pp_print_space print_static_const_or_code ppf t

and print_static_const_or_code ppf t =
  match t with
  | Code code -> Code0.print ~print_function_params_and_body ppf code
  | Deleted_code -> fprintf ppf "deleted_code"
  | Static_const const -> Static_const.print ppf const

and print_function_params_and_body ppf (t:function_params_and_body) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_for_function) t
    ~apply_renaming_to_term:apply_renaming
    ~f:(fun bff expr ->
      fprintf ppf "ret: %a; exn: %a; %a"
        Continuation.print (Bound_for_function.return_continuation bff)
        Continuation.print (Bound_for_function.exn_continuation bff)
        print expr)

and print_let_cont ppf (t : let_cont_expr) =
  match t with
  | Non_recursive {handler; body} ->
    Name_abstraction.pattern_match_for_printing
      (module Bound_continuation) body
      ~apply_renaming_to_term:apply_renaming
      ~f:(fun cont body ->
        Name_abstraction.pattern_match_for_printing
          (module Bound_parameters) handler
          ~apply_renaming_to_term:apply_renaming
          ~f:(fun k let_body ->
            fprintf ppf "(cont@ %a,@ param@ %a,@ body@ %a)@ in=%a"
            print_cont cont
            print_params k
            print let_body
            print body))
  | Recursive t ->
    fprintf ppf "rec@ ";
    Name_abstraction.pattern_match_for_printing
      (module Bound_continuations) t
      ~apply_renaming_to_term:apply_renaming_recursive_let_expr
      ~f:(fun k body -> print_recursive_let_cont ppf k body)

and print_params ppf (k : Bound_parameters.t) =
  Format.fprintf ppf "@[<hov 0>%a@]"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space print_param)
    (k |> Bound_parameters.to_list)

and print_param ppf (k : Bound_parameter.t) =
  fprintf ppf "%s" (Bound_parameter.var k |> Variable.name)

and print_cont ppf (k : Bound_continuation.t) =
  fprintf ppf "%s" (Continuation.name k)

and print_recursive_let_cont ppf (k : Bound_continuations.t)
      ({continuation_map; body} : recursive_let_expr) =
  fprintf ppf "[@ %a@ ] " Bound_continuations.print k;
  Name_abstraction.pattern_match_for_printing
    (module Bound_parameters) continuation_map
    ~apply_renaming_to_term:apply_renaming_cont_map
    ~f:(fun k body ->
      fprintf ppf "(%a)\n" Bound_parameters.print k;
      Continuation.Map.iter (print_continuation_handler ppf) body;
    );
  fprintf ppf "@ in\n %a" print body

and print_continuation_handler ppf key (t : continuation_handler) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_parameters) t
    ~apply_renaming_to_term:apply_renaming
    ~f:(fun k body ->
      fprintf ppf "%s: fun %a -> %a"
        (Continuation.name key)
        Bound_parameters.print k print body)

and print_apply ppf
      ({callee; continuation; exn_continuation; args; _} : apply_expr) =
  fprintf ppf "%a %a %a "
    print callee
    Apply_expr.Result_continuation.print continuation
    Continuation.print exn_continuation;
  Format.pp_print_list ~pp_sep:Format.pp_print_space print ppf args

and print_apply_cont ppf ({k ; args} : apply_cont_expr) =
  fprintf ppf "%a@ " print_cont k;
  Format.pp_print_list ~pp_sep:Format.pp_print_space print ppf args

and print_switch ppf ({scrutinee; arms} : switch_expr) =
  fprintf ppf "switch %a :" print scrutinee;
  Targetint_31_63.Map.iter (print_arm ppf) arms

and print_arm ppf key arm =
  fprintf ppf "| %a -> %a\n"
    Targetint_31_63.print key
    print arm

(** [ids_for_export] is the set of bound variables for a given expression **)
let rec ids_for_export (t : core_exp) =
  match t with
  | Named t -> ids_for_export_named t
  | Let t -> ids_for_export_let t
  | Let_cont t -> ids_for_export_let_cont t
  | Apply t -> ids_for_export_apply t
  | Apply_cont t -> ids_for_export_apply_cont t
  | Switch t -> ids_for_export_switch t
  | Invalid _ -> Ids_for_export.empty

(* ids for [Let_expr] *)
and ids_for_export_let { let_abst; body } =
  let body_ids = ids_for_export body in
  let let_abst_ids =
    Name_abstraction.ids_for_export
      (module Bound_pattern)
      let_abst ~ids_for_export_of_term:ids_for_export
  in
  Ids_for_export.union body_ids let_abst_ids

and ids_for_export_named (t : named) =
  match t with
  | Simple simple -> Ids_for_export.from_simple simple
  | Prim prim -> ids_for_export_prim prim
  | Set_of_closures set -> Set_of_closures.ids_for_export set
  | Static_consts consts -> ids_for_export_static_const_group consts
  | Rec_info info -> Rec_info_expr.ids_for_export info

and ids_for_export_prim (t : primitive) =
  match t with
  | Nullary (Invalid _ | Optimised_out _ | Probe_is_enabled _ | Begin_region) ->
    Ids_for_export.empty
  | Unary (prim, arg) ->
    Ids_for_export.union
      (P.ids_for_export_unary_primitive prim)
      (ids_for_export arg)
  | Binary (prim, arg1, arg2) ->
    Ids_for_export.union
      (Ids_for_export.union
        (P.ids_for_export_binary_primitive prim)
        (ids_for_export arg1))
      (ids_for_export arg2)
  | Ternary (prim, arg1, arg2, arg3) ->
    Ids_for_export.union
      (Ids_for_export.union
        (Ids_for_export.union
          (P.ids_for_export_ternary_primitive prim)
          (ids_for_export arg1))
        (ids_for_export arg2))
      (ids_for_export arg3)
  | Variadic (prim, args) ->
    Ids_for_export.union
      (P.ids_for_export_variadic_primitive prim)
      (List.fold_left (fun acc x -> Ids_for_export.union (ids_for_export x) acc)
         Ids_for_export.empty args)

and ids_for_export_static_const_group t =
  List.map ids_for_export_static_const_or_code t |> Ids_for_export.union_list

and ids_for_export_static_const_or_code t =
  match t with
  | Code code ->
    Code0.ids_for_export ~ids_for_export_function_params_and_body code
  | Deleted_code -> Ids_for_export.empty
  | Static_const const -> Static_const.ids_for_export const

and ids_for_export_function_params_and_body abst =
  Name_abstraction.ids_for_export
    (module Bound_for_function) abst
    ~ids_for_export_of_term:ids_for_export

(* ids for [Let_cont] *)
and ids_for_export_let_cont (t : let_cont_expr) =
  match t with
  | Non_recursive { handler; body } ->
    let handler_ids = ids_for_export_cont_handler handler in
    let body_ids =
      Name_abstraction.ids_for_export
        (module Bound_continuation)
        body ~ids_for_export_of_term:ids_for_export in
    Ids_for_export.union handler_ids body_ids
  | Recursive t ->
    Name_abstraction.ids_for_export
      (module Bound_continuations)
      t ~ids_for_export_of_term:ids_for_export_recursive_let_expr

and ids_for_export_recursive_let_expr ({continuation_map; body} : recursive_let_expr) =
  let cont_map_ids =
    Name_abstraction.ids_for_export
      (module Bound_parameters)
      continuation_map ~ids_for_export_of_term:ids_for_export_cont_map in
  let body_ids = ids_for_export body in
  Ids_for_export.union cont_map_ids body_ids

and ids_for_export_cont_handler (t : continuation_handler) =
  Name_abstraction.ids_for_export
    (module Bound_parameters) t ~ids_for_export_of_term:ids_for_export

and ids_for_export_cont_map (t : continuation_handler_map) =
  Continuation.Map.fold
    (fun k handler ids ->
       Ids_for_export.union ids
         (Ids_for_export.add_continuation
            (ids_for_export_cont_handler handler)
            k))
    t Ids_for_export.empty

(* ids for [Apply] *)
and ids_for_export_apply
      { callee; continuation; exn_continuation; args; call_kind } =
  let callee_ids = ids_for_export callee in
  let callee_and_args_ids =
    List.fold_left
      (fun ids arg -> Ids_for_export.union ids (ids_for_export arg))
       callee_ids args in
  let result_continuation_ids =
    Apply_expr.Result_continuation.ids_for_export continuation in
  let exn_continuation_ids =
    Ids_for_export.add_continuation Ids_for_export.empty exn_continuation in
  let call_kind_ids = Call_kind.ids_for_export call_kind in
  (Ids_for_export.union
    (Ids_for_export.union callee_and_args_ids call_kind_ids)
    (Ids_for_export.union result_continuation_ids exn_continuation_ids))

(* ids for [Apply_cont] *)
and ids_for_export_apply_cont { k; args } =
  List.fold_left
    (fun ids arg -> Ids_for_export.union ids (ids_for_export arg))
    (Ids_for_export.add_continuation Ids_for_export.empty k)
    args

and ids_for_export_switch { scrutinee; arms } =
  let scrutinee_ids = ids_for_export scrutinee in
  Targetint_31_63.Map.fold
    (fun _discr action ids ->
        Ids_for_export.union ids (ids_for_export action))
    arms scrutinee_ids

(* Module definitions for [Name_abstraction]*)
module T0 = struct
  type t = core_exp
  let apply_renaming = apply_renaming
  let ids_for_export = ids_for_export
end

module ContMap = struct
  type t = continuation_handler_map
  let apply_renaming = apply_renaming_cont_map
  let ids_for_export = ids_for_export_cont_map
end

module RecursiveLetExpr = struct
  type t = recursive_let_expr
  let apply_renaming = apply_renaming_recursive_let_expr
  let ids_for_export = ids_for_export_recursive_let_expr
end

module Core_let = struct
  module A = Name_abstraction.Make (Bound_pattern) (T0)
  let create ~(x : Bound_pattern.t) ~(e1 : core_exp) ~(e2 : core_exp)  =
    Let { let_abst = A.create x e2; body = e1 }

  module Pattern_match_pair_error = struct
    type t = Mismatched_let_bindings
  end

  let pattern_match t ~(f : x:Bound_pattern.t -> e1:core_exp -> e2:core_exp -> 'a) : 'a =
    let open A in
    let<> x, e2 = t.let_abst in
    f ~x ~e1:t.body ~e2

  (* Treat "dynamic binding" (statically scoped binding under lambda abstraction)
     and "static binding" (globally scoped mapping of statics) differently *)
  let pattern_match_pair
        ({let_abst = let_abst1; body = _}) ({let_abst = let_abst2; body = _})
        (dynamic : Bound_pattern.t -> core_exp -> core_exp -> 'a)
        (static : Bound_static.t -> Bound_static.t -> core_exp -> core_exp -> 'a):
    ('a, Pattern_match_pair_error.t) Result.t =
    A.pattern_match let_abst1 ~f:(fun let_bound1 let_body1 ->
      A.pattern_match let_abst2 ~f:(fun let_bound2 let_body2 ->
        let dynamic_case () =
          let ans = A.pattern_match_pair let_abst1 let_abst2 ~f:dynamic
          in Ok ans
        in
        match let_bound1, let_bound2 with
        | Bound_pattern.Singleton _, Bound_pattern.Singleton _ -> dynamic_case ()
        | Set_of_closures vars1, Set_of_closures vars2 ->
          if List.compare_lengths vars1 vars2 = 0
          then dynamic_case ()
          else Error Pattern_match_pair_error.Mismatched_let_bindings
        | Static bound_static1, Static bound_static2 ->
          let patterns1 = bound_static1 |> Bound_static.to_list in
          let patterns2 = bound_static2 |> Bound_static.to_list in
          if List.compare_lengths patterns1 patterns2 = 0
          then
            let ans = static bound_static1 bound_static2 let_body1 let_body2 in
            Ok ans
          else Error Pattern_match_pair_error.Mismatched_let_bindings
        | (Singleton _ | Set_of_closures _ | Static _), _ ->
            Error Pattern_match_pair_error.Mismatched_let_bindings
      )
    )
end

module Core_continuation_handler = struct
  module A = Name_abstraction.Make (Bound_parameters) (T0)
  type t = continuation_handler
  let create = A.create
  let pattern_match (e : t) (f : Bound_parameters.t -> core_exp -> 'a) : 'a =
    A.pattern_match e ~f:(fun cont body -> f cont body)
  let pattern_match_pair (t1 : t) (t2 : t)
        (f : Bound_parameters.t -> core_exp -> core_exp -> 'a) : 'a =
    A.pattern_match_pair t1 t2 ~f:(fun params body1 body2 ->
        f params body1 body2)
end

module Core_letcont_body = struct
  module A = Name_abstraction.Make (Bound_continuation) (T0)
  type t = (Bound_continuation.t, core_exp) Name_abstraction.t
  let create = A.create
  let pattern_match (e : t) (f : Bound_continuation.t -> core_exp -> 'a) : 'a =
    A.pattern_match e ~f:(fun cont body -> f cont body)
  let pattern_match_pair (t1 : t) (t2 : t)
        (f : Bound_continuation.t -> core_exp -> core_exp -> 'a) : 'a =
    A.pattern_match_pair t1 t2 ~f:(fun cont body1 body2 ->
      f cont body1 body2)
end

module Core_continuation_map = struct
  module A = Name_abstraction.Make (Bound_parameters) (ContMap)
  let create = A.create
  let pattern_match_pair = A.pattern_match_pair
end

module Core_recursive = struct
  module A = Name_abstraction.Make (Bound_continuations) (RecursiveLetExpr)

  type t = (Bound_continuations.t, recursive_let_expr) Name_abstraction.t
  let create = A.create
  let pattern_match_pair (t1 : t) (t2 : t)
    (f : Bound_parameters.t ->
         core_exp ->
         core_exp -> continuation_handler_map -> continuation_handler_map -> 'a)
    = A.pattern_match_pair t1 t2
        ~f:(fun (_:Bound_continuations.t)
                (t1 : recursive_let_expr)
                (t2 : recursive_let_expr) ->
          let body1 = t1.body in
          let body2 = t2.body in
          Core_continuation_map.pattern_match_pair
            t1.continuation_map t2.continuation_map
            ~f:(fun params h1 h2 -> f params body1 body2 h1 h2))
end

module Core_function_params_and_body = struct
  module A = Name_abstraction.Make (Bound_for_function) (T0)
  let create = A.create

  let pattern_match_pair t1 t2 ~f =
    A.pattern_match_pair t1 t2
      ~f:(fun
           bound_for_function body1 body2
           -> f ~return_continuation:
                 (Bound_for_function.return_continuation bound_for_function)
                ~exn_continuation:
                  (Bound_for_function.exn_continuation bound_for_function)
                (Bound_for_function.params bound_for_function)
                ~body1 ~body2
                ~my_closure:(Bound_for_function.my_closure bound_for_function)
                ~my_region:(Bound_for_function.my_region bound_for_function)
                ~my_depth:(Bound_for_function.my_depth bound_for_function))
end

module Core_code = struct
  type t = function_params_and_body Code0.t

  let code_metadata = Code0.code_metadata

  let params_and_body = Code0.params_and_body

  module Metadata_view = struct
    type nonrec 'a t = t

    let metadata = code_metadata
  end

  include Code_metadata.Code_metadata_accessors [@inlined hint] (Metadata_view)

  let create_with_metadata =
    Code0.create_with_metadata
      ~print_function_params_and_body:print_function_params_and_body
end

(** Translation from flambda2 terms to simplified core language **)
let simple_to_core (v : Simple.t) : core_exp = Named (Simple v)

let rec flambda_expr_to_core (e: expr) : core_exp =
  let e = Expr.descr e in
  match e with
  | Flambda.Let t -> let_to_core t
  | Flambda.Let_cont t -> let_cont_to_core t
  | Flambda.Apply t -> apply_to_core t
  | Flambda.Apply_cont t -> apply_cont_to_core t
  | Flambda.Switch t -> switch_to_core t
  | Flambda.Invalid { message = t } -> Invalid { message = t }

and let_to_core (e : Let_expr.t) : core_exp =
  let (var, body) = Let_expr.pattern_match e ~f:(fun var ~body -> (var, body)) in
  Core_let.create ~x:var
    ~e1:(Let_expr.defining_expr e |> named_to_core)
    ~e2:(flambda_expr_to_core body)

and named_to_core (e : Flambda.named) : core_exp =
  Named (
    match e with
    | Simple e -> Simple e
    | Prim (t, _) -> Prim (prim_to_core t)
    | Set_of_closures e -> Set_of_closures e
    | Static_consts e -> Static_consts (static_consts_to_core e)
    | Rec_info t -> Rec_info t)

and prim_to_core (e : P.t) : primitive =
  match e with
  | Nullary v -> Nullary v
  | Unary (prim, arg) ->
    Unary (prim, Named (Simple arg))
  | Binary (prim, arg1, arg2) ->
    Binary (prim, Named (Simple arg1), Named (Simple arg2))
  | Ternary (prim, arg1, arg2, arg3) ->
    Ternary (prim, Named (Simple arg1), Named (Simple arg2), Named (Simple arg3))
  | Variadic (prim, args) ->
    Variadic (prim, List.map (fun x -> Named (Simple x)) args)

and static_consts_to_core (e : Flambda.static_const_group) : static_const_group =
  Static_const_group.to_list e |> List.map static_const_to_core

and static_const_to_core (e : Flambda.static_const_or_code) : static_const_or_code =
  match e with
  | Code e -> Code (function_params_and_body_to_code0
                      (Code0.code_metadata e)
                      (Code0.params_and_body e)
                      (Code0.free_names_of_params_and_body e))
  | Deleted_code -> Deleted_code
  | Static_const t -> Static_const t

and function_params_and_body_to_code0 metadata (e : Flambda.function_params_and_body) free
  : function_params_and_body Code0.t =
  Core_code.create_with_metadata
    ~params_and_body:(function_params_and_body_to_core e)
    ~free_names_of_params_and_body:free
    ~code_metadata:metadata

and function_params_and_body_to_core (t : Flambda.function_params_and_body) :
  function_params_and_body =
  Function_params_and_body.pattern_match' t
    ~f:(fun (bound: Bound_for_function.t) ~body ->
      Core_function_params_and_body.create bound (flambda_expr_to_core body))

and let_cont_to_core (e : Let_cont_expr.t) : core_exp =
  match e with
  | Non_recursive
      {handler = h; num_free_occurrences = _; is_applied_with_traps = _} ->
    let (contvar, scoped_body) =
      Non_recursive_let_cont_handler.pattern_match
        h ~f:(fun contvar ~body -> (contvar, body)) in
    Let_cont (Non_recursive {
      handler =
        Non_recursive_let_cont_handler.handler h |> cont_handler_to_core;
      body = flambda_expr_to_core scoped_body |>
        Core_letcont_body.create contvar;})

  | Recursive r ->
    let (bound, params, body, handler) = Recursive_let_cont_handlers.pattern_match_bound
      r ~f:(fun bound ~invariant_params ~body t -> (bound, invariant_params, body, t)) in
    Let_cont
      (Recursive (Core_recursive.create bound
        {continuation_map =
            Core_continuation_map.create params (cont_handlers_to_core handler);
         body = flambda_expr_to_core body;}))

and cont_handler_to_core (e : Continuation_handler.t) : continuation_handler =
  let (var, handler) =
    Continuation_handler.pattern_match e ~f:(fun var ~handler -> (var, handler)) in
  Core_continuation_handler.create var (flambda_expr_to_core handler)

and cont_handlers_to_core (e : Continuation_handlers.t) :
  continuation_handler Continuation.Map.t =
  let e : Continuation_handler.t Continuation.Map.t =
    Continuation_handlers.to_map e in
  Continuation.Map.map cont_handler_to_core e

and apply_to_core (e : Apply.t) : core_exp =
  Apply {
    callee = Apply_expr.callee e |> simple_to_core;
    continuation = Apply_expr.continuation e;
    exn_continuation = Apply_expr.exn_continuation e |>
                        Exn_continuation.exn_handler;
    args = Apply_expr.args e |> List.map simple_to_core;
    call_kind = Apply_expr.call_kind e;}

and apply_cont_to_core (e : Apply_cont.t) : core_exp =
  Apply_cont {
    k = Apply_cont_expr.continuation e;
    args = Apply_cont_expr.args e |> List.map simple_to_core;}

and switch_to_core (e : Switch.t) : core_exp =
  Switch {
    scrutinee = Switch_expr.scrutinee e |> simple_to_core;
    arms = Switch_expr.arms e |> Targetint_31_63.Map.map apply_cont_to_core;}

let flambda_unit_to_core e : core_exp =
  Flambda_unit.body e |> flambda_expr_to_core

(* The most naive equality type, a boolean *)
type eq = bool

let eq_string = string_of_bool

(** Simple program context **)
(* LATER: Same structure used as [compare/compare.ml],
   might be useful to refactor the structure out of the file *)
module Env = struct
  type t =
    { mutable symbols : Symbol.t Symbol.Map.t;
      mutable code_ids : Code_id.t Code_id.Map.t;
      mutable function_slots : Function_slot.t Function_slot.Map.t;
      mutable function_slots_rev : Function_slot.t Function_slot.Map.t;
      mutable value_slots : Value_slot.t Value_slot.Map.t;
      mutable value_slots_rev : Value_slot.t Value_slot.Map.t
    }

  let create () =
    { symbols = Symbol.Map.empty;
      code_ids = Code_id.Map.empty;
      function_slots = Function_slot.Map.empty;
      function_slots_rev = Function_slot.Map.empty;
      value_slots = Value_slot.Map.empty;
      value_slots_rev = Value_slot.Map.empty }

  let add_symbol t symbol1 symbol2 =
    t.symbols <- Symbol.Map.add symbol1 symbol2 t.symbols

  let add_code_id t code_id1 code_id2 =
    t.code_ids <- Code_id.Map.add code_id1 code_id2 t.code_ids

  let add_function_slot t function_slot1 function_slot2 =
    t.function_slots
      <- Function_slot.Map.add function_slot1 function_slot2 t.function_slots;
    t.function_slots
      <- Function_slot.Map.add function_slot2 function_slot1
           t.function_slots_rev

  let add_value_slot t value_slot1 value_slot2 =
    t.value_slots <- Value_slot.Map.add value_slot1 value_slot2 t.value_slots;
    t.value_slots
      <- Value_slot.Map.add value_slot2 value_slot1 t.value_slots_rev

  let find_symbol t sym = Symbol.Map.find_opt sym t.symbols

  let find_code_id t code_id = Code_id.Map.find_opt code_id t.code_ids

  let find_function_slot t function_slot =
    Function_slot.Map.find_opt function_slot t.function_slots

  let find_function_slot_rev t function_slot =
    Function_slot.Map.find_opt function_slot t.function_slots_rev

  let find_value_slot t value_slot =
    Value_slot.Map.find_opt value_slot t.value_slots

  let find_value_slot_rev t value_slot =
    Value_slot.Map.find_opt value_slot t.value_slots_rev
end

(* Used for unification of environments while comparing function and value slots in
  [set_of_closures]. This is necessary because function and value slots do not have
  an explicit binding site. *)
let subst_symbol (env : Env.t) symbol =
  Env.find_symbol env symbol |> Option.value ~default:symbol

let subst_function_slot (env : Env.t) slot =
  Env.find_function_slot env slot |> Option.value ~default:slot

let subst_value_slot (env : Env.t) var =
  Env.find_value_slot env var |> Option.value ~default:var

let subst_unary_primitive env (p : Flambda_primitive.unary_primitive) :
  Flambda_primitive.unary_primitive =
  match p with
  | Project_function_slot { move_from; move_to } ->
    let move_from = subst_function_slot env move_from in
    let move_to = subst_function_slot env move_to in
    Project_function_slot { move_from; move_to }
  | Project_value_slot { project_from; value_slot; kind } ->
    let project_from = subst_function_slot env project_from in
    let value_slot = subst_value_slot env value_slot in
    Project_value_slot { project_from; value_slot; kind }
  | _ -> p

let subst_name env n =
  Name.pattern_match n
    ~var:(fun _ -> n)
    ~symbol:(fun s -> Name.symbol (subst_symbol env s))

let subst_simple env s =
  Simple.pattern_match s
    ~const:(fun _ -> s)
    ~name:(fun n ~coercion:_ -> Simple.name (subst_name env n))

let subst_code_id env code_id =
  Env.find_code_id env code_id |> Option.value ~default:code_id

let subst_primitive env (p : Flambda_primitive.t) : Flambda_primitive.t =
  match p with
  | Unary (unary_primitive, arg) ->
    Unary (subst_unary_primitive env unary_primitive, subst_simple env arg)
  | _ -> p

let subst_code_id (env : Env.t) code_id =
  Env.find_code_id env code_id |> Option.value ~default:code_id

let subst_func_decl env code_id = subst_code_id env code_id

let subst_func_decls env decls =
  Function_declarations.funs_in_order decls
  |> Function_slot.Lmap.bindings
  |> List.map (fun (function_slot, func_decl) ->
    let function_slot = subst_function_slot env function_slot in
    let func_decl = subst_func_decl env func_decl in
    function_slot, func_decl)
  |> Function_slot.Lmap.of_list |> Function_declarations.create

(** Equality between two programs given a context **)
(* For now, following a naive alpha-equivalence equality from [compare/compare]
    (without the discriminant) *)

let equiv_symbols env sym1 sym2 : eq =
  let sym1 = subst_symbol env sym1 in
  Symbol.equal sym1 sym2

let equiv_names env name1 name2 : eq =
  Name.pattern_match name1
    ~var:(fun var1 ->
      Name.pattern_match name2
        ~var:(fun var2 -> Variable.equal var1 var2)
        ~symbol:(fun _ -> false))
    ~symbol:(fun symbol1 ->
      Name.pattern_match name2
        ~var:(fun _ -> false)
        ~symbol:(fun symbol2 -> equiv_symbols env symbol1 symbol2))

let equiv_value_slots env value_slot1 value_slot2 : eq =
  match Env.find_value_slot env value_slot1 with
  | Some value_slot ->
    Value_slot.equal value_slot value_slot2
  | None ->
      match Env.find_value_slot_rev env value_slot2 with
      | Some _ -> false
      | None -> Env.add_value_slot env value_slot1 value_slot2; false

let zip_fold l1 l2 ~f ~acc =
  List.combine l1 l2 |> List.fold_left f acc

let zip_sort_fold l1 l2 ~compare ~f ~acc =
  let l1 = List.sort compare l1 in
  let l2 = List.sort compare l2 in
  zip_fold l1 l2 ~f ~acc

let equiv_function_slot env
  (slot1 : Function_slot.t) (slot2 : Function_slot.t) : eq =
  match Env.find_function_slot env slot1 with
  | Some slot -> Function_slot.equal slot slot2
  | None ->
    match Env.find_function_slot_rev env slot2 with
    | Some _ -> false
    | None -> Env.add_function_slot env slot1 slot2; true

let equiv_code_ids env id1 id2 =
  let id1 = subst_code_id env id1 in
  Code_id.equal id1 id2

let equiv_function_decl = equiv_code_ids

let equiv_set_of_closures env
  (set1 : Set_of_closures.t) (set2 : Set_of_closures.t) : eq =
  (* Unify value and function slots *)
  (* Comparing value slots *)
  let value_slots_by_value set =
    Value_slot.Map.bindings (Set_of_closures.value_slots set)
    |> List.map (fun (var, (value, kind)) -> kind, subst_simple env value, var)
  in
  let compare (kind1, value1, _var1) (kind2, value2, _var2) =
    let c = Flambda_kind.With_subkind.compare kind1 kind2 in
    if c = 0 then Simple.compare value1 value2 else c
  in
  let value_slots_eq =
    zip_sort_fold (value_slots_by_value set1) (value_slots_by_value set2)
      ~compare
      ~f:(fun x ((_, _, var1), (_, _, var2)) ->
            x && equiv_value_slots env var1 var2)
      ~acc:true
  in
  (* Comparing function slots *)
  let function_slots_and_fun_decls_by_code_id (set : Set_of_closures.t)
      : (Code_id.t * (Function_slot.t * Code_id.t)) list =
    let map = Function_declarations.funs (Set_of_closures.function_decls set) in
    Function_slot.Map.bindings map
    |> List.map (fun (function_slot, code_id) ->
      subst_code_id env code_id, (function_slot, code_id))
  in
  let function_slots_eq =
    zip_fold
      (function_slots_and_fun_decls_by_code_id set1)
      (function_slots_and_fun_decls_by_code_id set2)
      ~f:(fun acc ((_, (slot1, decl1)), (_, (slot2, decl2))) ->
        acc &&
        equiv_function_slot env slot1 slot2 &&
        equiv_function_decl env decl1 decl2)
      ~acc: true
  in
  value_slots_eq && function_slots_eq

let equiv_rec_info _env info1 info2 : eq =
  Rec_info_expr.equal info1 info2

let equiv_method_kind _env (k1 : Call_kind.Method_kind.t) (k2 : Call_kind.Method_kind.t)
  : eq =
  match k1, k2 with
  | Self, Self | Public, Public | Cached, Cached -> true
  | (Self | Public | Cached), _ -> false

let rec equiv (env:Env.t) e1 e2 : eq =
  match e1, e2 with
  | Named v1, Named v2 -> equiv_named env v1 v2
  | Let e1, Let e2 -> equiv_let env e1 e2
  | Let_cont e1, Let_cont e2 -> equiv_let_cont env e1 e2
  | Apply e1, Apply e2 -> equiv_apply env e1 e2
  | Apply_cont e1, Apply_cont e2 -> equiv_apply_cont env e1 e2
  | Switch e1, Switch e2 -> equiv_switch env e1 e2
  | Invalid _, Invalid _ -> true
  | (Named _ | Let _ | Let_cont _ | Apply _ | Apply_cont _ | Switch _ | Invalid _), _ ->
    false

(* [let_expr] *)
and equiv_let env e1 e2 : eq =
  Core_let.pattern_match_pair e1 e2
    (fun _bound let_bound1 let_bound2 ->
       equiv env let_bound1 let_bound2 && equiv env e1.body e2.body)
    (fun bound1 bound2 let_bound1 let_bound2 ->
         equiv_let_symbol_exprs env
           (bound1, e1.body, let_bound1)
           (bound2, e2.body, let_bound2))
  |> function | Ok comp -> comp | Error _ -> false

and equiv_let_symbol_exprs env
      (static1, const1, body1) (static2, const2, body2) : eq =
  equiv_bound_static env static1 static2 &&
  equiv env const1 const2 &&
  equiv env body1 body2

and equiv_static_consts env
  (const1 : static_const_or_code) (const2 : static_const_or_code) : eq =
  match const1, const2 with
  | Code code1, Code code2 -> equiv_code env code1 code2
  | Static_const (Block (tag1, mut1, fields1)),
    Static_const (Block (tag2, mut2, fields2)) ->
    equiv_block env (tag1, mut1, fields1) (tag2, mut2, fields2)
  | Static_const (Set_of_closures set1), Static_const (Set_of_closures set2) ->
    equiv_set_of_closures env set1 set2
  | Deleted_code, Deleted_code -> true
  (* IY: Is it fine to treat all the other static constants uniformly? *)
  | (Static_const (Set_of_closures _) |
     Static_const (Block _) |
     Static_const (Boxed_float _) |
     Static_const (Boxed_int32 _) |
     Static_const (Boxed_int64 _) |
     Static_const (Boxed_nativeint _) |
     Static_const (Immutable_float_block _) |
     Static_const (Immutable_float_array _) |
     Static_const (Immutable_value_array _) |
     Static_const Empty_array |
     Static_const (Mutable_string _)|
     Static_const (Immutable_string _)|
     Code _ | Deleted_code), _ -> compare const1 const2 = 0

and equiv_code env
  (code1 : function_params_and_body Code0.t) (code2 : function_params_and_body Code0.t) =
  let code1 : function_params_and_body = Core_code.params_and_body code1 in
  let code2 : function_params_and_body = Core_code.params_and_body code2 in
  Core_function_params_and_body.pattern_match_pair code1 code2
    ~f:(fun
         ~return_continuation:_
         ~exn_continuation:_
         _params
         ~body1
         ~body2
         ~my_closure:_
         ~my_region:_
         ~my_depth:_ ->
         equiv env body1 body2)

and equiv_fields env
      (field1 : Field_of_static_block.t) (field2 : Field_of_static_block.t) =
  match field1, field2 with
  | Symbol symbol1, Symbol symbol2 ->
    equiv_symbols env symbol1 symbol2
  | _, _ -> Field_of_static_block.equal field1 field2

and equiv_block env (tag1, mut1, fields1) (tag2, mut2, fields2) =
  Tag.Scannable.equal tag1 tag2 &&
  Mutability.compare mut1 mut2 = 0 &&
  (List.combine fields1 fields2 |>
   List.fold_left (fun x (e1, e2) -> x && equiv_fields env e1 e2)
     true)

and equiv_bound_static env static1 static2 : eq =
  let static1 = Bound_static.to_list static1 in
  let static2 = Bound_static.to_list static2 in
  List.combine static1 static2 |>
  List.fold_left (fun x (e1, e2) -> x && equiv_pattern env e1 e2) true

(* Compare equal patterns and add variables to environment *)
and equiv_pattern env
      (pat1 : Bound_static.Pattern.t) (pat2 : Bound_static.Pattern.t) : eq =
  match pat1, pat2 with
  | Code id1, Code id2 ->
    Env.add_code_id env id1 id2; true
  | Block_like sym1, Block_like sym2 ->
    Env.add_symbol env sym1 sym2; true
  | Set_of_closures clo1, Set_of_closures clo2 ->
    let closure_bindings env (slot1, symbol1) (slot2, symbol2) : eq =
      Env.add_symbol env symbol1 symbol2;
      subst_function_slot env slot1;
      equiv_function_slots env slot1 slot2
    in
    let subst_closure_binding env (slot, symbol) =
      subst_function_slot env slot, symbol
    in
    let clo1 = Function_slot.Lmap.bindings clo1 in
    let clo2 = Function_slot.Lmap.bindings clo2 in
    List.combine clo1 clo2 |>
    List.fold_left (fun x (e1, e2) -> x && closure_bindings env e1 e2) true
  | (Code _ | Block_like _ | Set_of_closures _), _ -> false

and equiv_function_slots env slot1 slot2 =
  match Env.find_function_slot env slot1 with
  | Some function_slot ->
    Function_slot.equal function_slot slot2
  | None ->
    match Env.find_function_slot_rev env slot2 with
    | Some _ -> false
    | None -> Env.add_function_slot env slot1 slot2; true

and equiv_named env named1 named2 : eq =
  match named1, named2 with
  | Simple simple1, Simple simple2 ->
    equiv_simple env simple1 simple2
  | Prim prim1, Prim prim2 ->
    equiv_primitives env prim1 prim2
  | Set_of_closures set1, Set_of_closures set2 ->
    equiv_set_of_closures env set1 set2
  | Rec_info rec_info_expr1, Rec_info rec_info_expr2 ->
    equiv_rec_info env rec_info_expr1 rec_info_expr2
  | Static_consts const1, Static_consts const2 ->
    (List.combine const1 const2 |>
     List.fold_left (fun x (e1, e2) -> x && equiv_static_consts env e1 e2) true)
  | (Simple _ | Prim _ | Set_of_closures _ | Rec_info _ | Static_consts _ ), _ ->
    false

and equiv_simple env simple1 simple2 : eq =
  Simple.pattern_match simple1
    ~name:(fun name1 ~coercion:_ ->
      Simple.pattern_match simple2
        ~name:(fun name2 ~coercion:_ -> equiv_names env name1 name2)
        ~const:(fun _ -> false))
    ~const:(fun const1 ->
      Simple.pattern_match simple2
        ~name:(fun _ ~coercion:_ -> false)
        ~const:(fun const2 -> Reg_width_const.equal const1 const2))

and equiv_primitives env prim1 prim2 : eq =
  match (prim1:primitive), (prim2:primitive) with
  | Unary (op1, arg1), Unary (op2, arg2) ->
    P.equal_unary_primitive op1 op2 &&
    equiv env arg1 arg2
  | Binary (op1, arg1_1, arg1_2), Binary (op2, arg2_1, arg2_2) ->
    P.equal_binary_primitive op1 op2 &&
    equiv env arg1_1 arg2_1 &&
    equiv env arg1_2 arg2_2
  | Ternary (op1, arg1_1, arg1_2, arg1_3),
    Ternary (op2, arg2_1, arg2_2, arg2_3) ->
    P.equal_ternary_primitive op1 op2 &&
    equiv env arg1_1 arg2_1 &&
    equiv env arg1_2 arg2_2 &&
    equiv env arg1_3 arg2_3
  | Variadic (op1, args1), Variadic (op2, args2) ->
    P.equal_variadic_primitive op1 op2 &&
    (List.combine args1 args2 |>
     List.fold_left (fun x (e1, e2) -> x && equiv env e1 e2) true)
  | Nullary (Invalid _), Nullary (Invalid _) -> true
  | Nullary (Optimised_out _), Nullary (Optimised_out _) -> true
  | Nullary (Probe_is_enabled _), Nullary (Probe_is_enabled _) -> true
  | Nullary Begin_region, Nullary Begin_region -> true
  | (Nullary (Invalid _) | Nullary (Optimised_out _ ) | Nullary (Probe_is_enabled _)
    | Nullary (Begin_region)
    | Unary _ | Binary _ | Ternary _ | Variadic _), _ -> false

(* [let_cont_expr] *)
and equiv_let_cont env let_cont1 let_cont2 : eq =
  match let_cont1, let_cont2 with
  | Non_recursive {handler = handler1; body = body1},
    Non_recursive {handler = handler2; body = body2} ->
    equiv_cont_handler env handler1 handler2 &&
    Core_letcont_body.pattern_match_pair body1 body2
      (fun _bound b1 b2 -> equiv env b1 b2)
  | Recursive handlers1, Recursive handlers2 ->
    Core_recursive.pattern_match_pair handlers1 handlers2
      (fun (_params : Bound_parameters.t)
        (body1 : core_exp) (body2 : core_exp)
        (map1 : continuation_handler_map) (map2 : continuation_handler_map) ->
        equiv env body1 body2 &&
        equiv_cont_handler_map env map1 map2)
  | (Non_recursive _ | Recursive _), _ -> false

and equiv_cont_handler env handler1 handler2 =
  Core_continuation_handler.pattern_match_pair handler1 handler2
    (fun _bound h1 h2 -> equiv env h1 h2)

and equiv_cont_handler_map env
      (map1 : continuation_handler_map) (map2 : continuation_handler_map) =
  Continuation.Map.equal (equiv_cont_handler env) map1 map2

(* [apply] *)
and equiv_apply env (e1 : apply_expr) (e2 : apply_expr) : eq =
  let equiv_conts =
    Apply_expr.Result_continuation.equal (e1.continuation) (e2.continuation) &&
    Continuation.equal (e1.exn_continuation) (e2.exn_continuation) in
  let callee = equiv env (e1.callee) (e2.callee) in
  let args =
    zip_fold (e1.args) (e2.args)
      ~f:(fun x (e1, e2) -> x && equiv env e1 e2) ~acc:true in
  let call_kind = equiv_call_kind env (e1.call_kind) (e2.call_kind) in
  equiv_conts && callee && args && call_kind

and equiv_call_kind env (k1 : Call_kind.t) (k2 : Call_kind.t) : eq =
  match k1, k2 with
  (* Direct OCaml function calls *)
  | Function
      { function_call =
          Direct { code_id = code_id1; return_arity = return_arity1 }; _ },
    Function
      { function_call =
          Direct { code_id = code_id2; return_arity = return_arity2 }; _ } ->
    Code_id.equal code_id1 code_id2 &&
    Flambda_arity.With_subkinds.equal return_arity1 return_arity2

  (* Indirect OCaml function calls, with known arity  *)
  | Function
      { function_call =
          Indirect_known_arity
            { param_arity = param_arity1; return_arity = return_arity1 }; _},
    Function
      { function_call =
          Indirect_known_arity
            { param_arity = param_arity2; return_arity = return_arity2 }; _} ->
    Flambda_arity.With_subkinds.equal param_arity1 param_arity2 &&
    Flambda_arity.With_subkinds.equal return_arity1 return_arity2

  (* Indirect OCaml function calls, with unknown arity  *)
  | Function { function_call = Indirect_unknown_arity ; _ },
    Function { function_call = Indirect_unknown_arity ; _ } -> true

  (* OCaml method invocation *)
  | Method { kind = kind1; obj = obj1; _ },
    Method { kind = kind2; obj = obj2; _ } ->
    equiv_method_kind env kind1 kind2 && equiv_simple env obj1 obj2

  (* C calls *)
  | C_call
      { alloc = alloc1;
        param_arity = param_arity1;
        return_arity = return_arity1;
        is_c_builtin = _},
    C_call
      { alloc = alloc2;
        param_arity = param_arity2;
        return_arity = return_arity2;
        is_c_builtin = _} ->
    Bool.equal alloc1 alloc2
    && Flambda_arity.equal param_arity1 param_arity2
    && Flambda_arity.equal return_arity1 return_arity2

  | (Function { function_call = Direct _ ; _}
      | Function { function_call = Indirect_known_arity _ ; _}
      | Function { function_call = Indirect_unknown_arity ; _}
      | Method _ | C_call _), _ -> false

(* [apply_cont] *)
and equiv_apply_cont env
      ({k = k1; args = args1} : apply_cont_expr)
      ({k = k2; args = args2} : apply_cont_expr) : eq =
  equiv_cont env k1 k2 &&
  zip_fold args1 args2 ~f:(fun x (e1, e2) -> x && equiv env e1 e2) ~acc:true

and equiv_cont _env (e1 : Continuation.t) (e2 : Continuation.t) : eq =
  match Continuation.sort e1, Continuation.sort e2 with
  | Toplevel_return, Toplevel_return -> true
  | Normal_or_exn, Normal_or_exn
  | Return, Return
  | Define_root_symbol, Define_root_symbol -> Continuation.equal e1 e2
  | (Normal_or_exn | Return | Define_root_symbol | Toplevel_return), _ -> false

(* [switch] *)
and equiv_switch env
      ({scrutinee = scrutinee1; arms = arms1} : switch_expr)
      ({scrutinee = scrutinee2; arms = arms2} : switch_expr) : eq =
  equiv env scrutinee1 scrutinee2 &&
  Targetint_31_63.Map.equal (equiv env) arms1 arms2

let core_eq = Env.create () |> equiv

let _std_print =
  fprintf Format.std_formatter "@. TERM:%a@." print

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
    failwith "Should not be reached"
    (* subst_pattern_set_of_closures ~bound ~let_body e *)
  | Static bound ->
    subst_pattern_static_list ~bound ~let_body e

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
  | Block_load (kind, mut) ->
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
  | Make_block (Naked_floats, mut, _) ->
    failwith "Unimplemented_subst_pattern_primitive_variadic_make_block_floats"
  | Make_array _ ->
    failwith "Unimplemented_subst_pattern_primitive_variadic"

(* IY: What do coercions do? *)
and simple_to_field_of_static_block (x : Simple.t) (dbg : Debuginfo.t)
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
     let bound : Variable.t = Bound_var.var bound in
     (* TODO: Is it OK to assign a Simple to a Variable? *)
     let bound = Simple.var bound in
     if (Simple.equal s bound) then let_body else e
   | Named (Prim p) ->
     subst_pattern_primitive ~bound ~let_body p
   | Named (Static_consts [Code _ | Deleted_code]) -> e (* NEXT *)
   | Named (Static_consts [Static_const (Block (tag, mut, list))]) ->
      let bound : Variable.t = Bound_var.var bound in
      (* N.B: static constants can refer to variables. *)
      let list =
        List.map
          (fun x ->
            match x with
            | Field_of_static_block.Symbol _ | Tagged_immediate _ -> x
            | Dynamically_computed (var, dbg) ->
              if (Simple.same (Simple.var var) (Simple.var bound))
              then
                (match let_body with
                  | Named (Simple let_body) ->
                      simple_to_field_of_static_block let_body dbg
                  | _ -> x)
            else x) list
     in
     Named (Static_consts [Static_const (Static_const.block tag mut list)])
   | Named (Set_of_closures _) -> e
   | Named (Rec_info _) -> e
   | Let {let_abst; body} ->
     Core_let.pattern_match {let_abst; body}
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
    (* FIXME double-check *) Named e
  | Set_of_closures set ->
    Named e (* NEXT *)
  | Rec_info _ ->
    failwith "Unimplemented_block_like"

(* Set of closures:

   Given the code for its functions and closure variables, the set of closures
    keeps track of the mapping between them.

   From what I can tell right now, you get a new let bound set of closures every time
    you define code along with its closures

   i.e. it is the code generated by
    [let f = closure f_0 @f]
   where [f_0] refers to the code

    Apply2.camlApply2__f_1 <-| f/0 =
        (set_of_closures Heap ({f/0 camlApply2__f_0_1_code}))

*)
and subst_bound_set_of_closures (bound : Symbol.t Function_slot.Lmap.t) ~let_body (e : named) =
  match e with
  | Simple v -> (Named e)
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
    (* FIXME double-check *) Named e
  | Set_of_closures set ->
    Named e (* NEXT *)
  | Rec_info _ ->
    failwith "Unimplemented_block_like"

and subst_pattern_static
      ~(bound : Bound_static.Pattern.t) ~(let_body : core_exp) (e : core_exp) : core_exp =
  match e with
  | Apply_cont {k ; args} ->
    Apply_cont
      {k = k;
       args = List.map (subst_pattern_static ~bound ~let_body) args}
  | Let {let_abst; body} ->
    Core_let.pattern_match {let_abst; body}
      ~f:(fun ~x ~e1 ~e2 ->
        Core_let.create
          ~x
          ~e1:(subst_pattern_static bound let_body e1)
          ~e2:(subst_pattern_static bound let_body e2))
  | Switch {scrutinee; arms} ->
    Switch
      {scrutinee = subst_pattern_static bound let_body scrutinee;
        arms = Targetint_31_63.Map.map
                 (subst_pattern_static ~bound ~let_body) arms}
  | Named named ->
    (match bound with
     | Block_like bound ->
       subst_block_like ~bound ~let_body named
     | Set_of_closures set ->
       subst_bound_set_of_closures set ~let_body named
     | Code id -> failwith "Code case not handled")
  | Let_cont e ->
    (match e with
     | Non_recursive {handler; body} ->
       Let_cont
         (Non_recursive
            { handler =
                Core_continuation_handler.pattern_match handler
                  (fun param exp ->
                      Core_continuation_handler.create
                        param (subst_pattern_static bound let_body exp));
              body =
                Core_letcont_body.pattern_match body
                  (fun cont exp ->
                     Core_letcont_body.create
                       cont (subst_pattern_static bound let_body exp))})
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
         (subst_pattern_static hd let_body e)) in
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
  | Let { let_abst; body } ->
    let bound, e, body =
      Core_let.pattern_match {let_abst; body}
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

let eval_prim_nullary (v : P.nullary_primitive) : named =
  failwith "eval_prim_nullary"

let eval_prim_unary (v : P.unary_primitive) (arg : core_exp) : named =
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
  | Block_load (Values {tag = Known tag; size; field_kind},
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
     | Named (Prim (Variadic (Make_block (kind, Immutable, _), blocks))),
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
  | Block_load (kind, Mutable) ->
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

let eval_prim_ternary (v : P.ternary_primitive)
      (arg1 : core_exp) (arg2 : core_exp) (arg3 : core_exp) : named =
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
              let block = (Static_const.block tag Immutable [Tagged_immediate i])
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
  | Make_block (Naked_floats, _, _) ->
    failwith "eval_prim_variadic_naked_floats_unspported"
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
  | Let { let_abst; body } ->
    normalize_let let_abst body
  | Let_cont e ->
    normalize_let_cont e
    |> normalize
  | Apply {callee; continuation; exn_continuation; args; call_kind} ->
    normalize_apply callee continuation exn_continuation args call_kind
    |> normalize
  | Apply_cont {k ; args} ->
    (* The recursive call for [apply_cont] is done for the arguments *)
    normalize_apply_cont k args
  | Switch _ -> failwith "Unimplemented_normalize_switch"
  | Named e -> Named (normalize_named e)
  | Invalid _ -> e

and replace_set_of_closures (e : core_exp) (bound : Bound_var.t list) (static : Symbol.t list) =
  match e with
  | Apply_cont {k ; args} ->
    Apply_cont
      {k = k;
       args = List.map (fun x -> replace_set_of_closures x bound static) args}
  | Let {let_abst; body} ->
    Core_let.pattern_match {let_abst; body}
      ~f:(fun ~x ~e1 ~e2 ->
        Core_let.create
          ~x
          ~e1:(replace_set_of_closures e1 bound static)
          ~e2:(replace_set_of_closures e2 bound static))
  | Switch {scrutinee; arms} ->
    Switch
      {scrutinee =
         replace_set_of_closures scrutinee bound static;
       arms = Targetint_31_63.Map.map
                (fun x -> replace_set_of_closures x bound static) arms}
  | Named named ->
    replace_set_of_closures_named named bound static
  | Let_cont e ->
    (match e with
     | Non_recursive {handler; body} ->
       Let_cont
         (Non_recursive
            { handler =
                Core_continuation_handler.pattern_match handler
                  (fun param exp ->
                      Core_continuation_handler.create
                        param (replace_set_of_closures exp bound static));
              body =
                Core_letcont_body.pattern_match body
                  (fun cont exp ->
                     Core_letcont_body.create
                       cont (replace_set_of_closures exp bound static))})
     | Recursive _ ->
       failwith "Unimplemented_static_clo_recursive"
    )
  | Apply _ -> failwith "Unimplemented_subst_pattern_static"
  | Invalid _ -> e

and replace_set_of_closures_named (e : named) (vars : Bound_var.t list) (static: Symbol.t list) =
  match e with
  | Simple v ->
    let rec find_static vs ss =
      (match vs, ss with
      | [], [] -> Named e
      | v' :: vtl,s :: stl ->
        if (Simple.same v (Simple.var v')) then (Named (Simple (Simple.symbol s))) else Named e)
    in
    find_static (List.map Bound_var.var vars) static

  | Prim (Nullary e) -> Named (Prim (Nullary e))
  | Prim (Unary (e, arg1)) ->
    let arg1 = replace_set_of_closures arg1 vars static in
    Named (Prim (Unary (e, arg1)))
  | Prim (Binary (e, arg1, arg2)) ->
    let arg1 = replace_set_of_closures arg1 vars static in
    let arg2 = replace_set_of_closures arg2 vars static in
    Named (Prim (Binary (e, arg1, arg2)))
  | Prim (Ternary (e, arg1, arg2, arg3)) ->
    let arg1 = replace_set_of_closures arg1 vars static in
    let arg2 = replace_set_of_closures arg2 vars static in
    let arg3 = replace_set_of_closures arg3 vars static in
    Named (Prim (Ternary (e, arg1, arg2, arg3)))
  | Prim (Variadic (e, args)) ->
    let args =
      List.map
        (fun x -> replace_set_of_closures x vars static) args
    in
    Named (Prim (Variadic (e, args)))
  | Static_consts _ ->
    (* FIXME double-check *) Named e
  | Set_of_closures set ->
    Named e (* NEXT *)
  | Rec_info _ ->
    failwith "Unimplemented_block_like"

(* IY: Problematic when checking alpha-equivalence *)
and named_static_closures vars (e1 : core_exp) (e2 : core_exp)
  : Bound_pattern.t * core_exp * core_exp =
  match e1 with
  | Named (Set_of_closures set) ->
    let function_decls : Code_id.t Function_slot.Lmap.t =
      Set_of_closures.function_decls set |> Function_declarations.funs_in_order in
    let closure_symbols : Symbol.t Function_slot.Lmap.t =
      Function_slot.Lmap.mapi
        (fun function_slot _func_decl ->
           let name =
             function_slot |> Function_slot.rename |> Function_slot.to_string
             |> Linkage_name.of_string
           in
           Symbol.create (Compilation_unit.get_current_exn ()) name)
        function_decls in
    let set : static_const_or_code =
      Static_const (Static_const.set_of_closures set) in
    let bound =
      Bound_static.Pattern.set_of_closures closure_symbols |>
      Bound_static.singleton
    in
    let closure_list = closure_symbols |> Function_slot.Lmap.data in
    let e2 = replace_set_of_closures e2 vars closure_list in
    (Bound_pattern.static bound, Named (Static_consts [set]), e2)
  | _ -> failwith "Expected set of closures"

and normalize_let let_abst body : core_exp =
  (* [LetL]
                  e1 ⟶ e1'
     -------------------------------------
     let x = e1 in e2 ⟶ let x = e1' in e2 *)
  let x, e1, e2 =
    Core_let.pattern_match {let_abst; body}
      ~f:(fun ~x ~e1 ~e2 -> (x, normalize e1, e2))
  in
  (match x with
  | Static bound ->
    (let bound = Bound_static.to_list bound in
     match bound with

     (* [LetCode]
                          e2 ⟶ e2'
        ----------------------------------------------
        let code x = e1 in e2 -> let code x = e1 in e2'

        [LetCodeDeleted]
        let code x = Deleted in e2 -> e2

        [LetCodeNew]
        let code (newer_version_of x) x' = e1 in e2 ->
        let code x = e1 in e2 [x\x'] *)
     | [Code m] ->
       let letcode () = Core_let.create ~x ~e1 ~e2:(normalize e2) in
       (match e1 with
        | Named (Static_consts [Deleted_code]) -> normalize e2
        | Named (Static_consts [Code code]) ->
          let metadata = Core_code.code_metadata code in
          (match Code_metadata.newer_version_of metadata with
           | Some n ->
             Core_let.create
               ~x:(Bound_pattern.static (Bound_static.create [Bound_static.Pattern.code n]))
               ~e1:(apply_renaming e1 (Renaming.add_code_id Renaming.empty m n) |> normalize)
               ~e2:(apply_renaming e2 (Renaming.add_code_id Renaming.empty m n) |> normalize)
           | None -> letcode ())
        | _ -> letcode ())

      (* [Set_of_closures (static)]
                                  e2 ⟶ e2'
        --------------------------------------------------------------------
        let static_closures x = e1 in e2 -> let static_closures x = e1 in e2' *)
     | [Set_of_closures _] -> Core_let.create ~x ~e1 ~e2:(normalize e2)

     | _ -> subst_pattern ~bound:x ~let_body:e1 e2 |> normalize)

  (* [Set_of_closures]

     Turn a bound_pattern that is a list of variables to a static set of closures that is
     a function slot/symbol map.
     Then Replace the variables with assigned static closure variables in the body of e2

     let closures x = e1 in e2 ->
     let static_closures x = static e1 in subst e2 [x \ static_closures x] *)

  | Set_of_closures set ->
    let (xs, e1, e2) = named_static_closures set e1 e2 in
    Core_let.create ~x:xs ~e1 ~e2:(normalize e2) |> normalize

  (* [Let-β]
    let x = v in e2 ⟶ e2 [x\v] *)
  | _ -> subst_pattern ~bound:x ~let_body:e1 e2 |> normalize)

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
  core_eq src_core tgt_core

(** Top-level validator *)
let validate ~cmx_loader ~round src =
  let tgt = Simplify.run ~cmx_loader ~round src in
  simulation_relation src tgt
