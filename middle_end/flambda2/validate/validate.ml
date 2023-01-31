open! Flambda

let fprintf = Format.fprintf

(** Simplified core of [flambda2] terms **)
(* (1) Simple.t -> core_exp for [Apply*] expressions
   (2) Ignore [Num_occurrences] (which is used for making inlining decisions)
   (3) Ignored traps for now *)

type core_exp =
  | Var of Simple.t
  | Let of let_expr
  | Let_cont of let_cont_expr
  | Apply of apply_expr
  | Apply_cont of apply_cont_expr
  | Switch of switch_expr
  | Invalid of { message : string }

(** Let expressions [let x = e1 in e]

   [fun x -> e] = let_abst
   [e1] = body **)
and let_expr =
  { let_abst : (Bound_pattern.t, core_exp) Name_abstraction.t;
    body : named; }

and named =
  | Simple of Simple.t
  | Prim of Flambda_primitive.t
  | Set_of_closures of Set_of_closures.t
  | Static_consts of static_const_group
  | Rec_info of Rec_info_expr.t

and function_params_and_body =
  (Bound_for_function.t, core_exp) Name_abstraction.t

and static_const_or_code =
  | Code of function_params_and_body Code0.t
  | Deleted_code
  | Static_const of Static_const.t

and static_const_group = static_const_or_code list

and let_cont_expr =
  (** Non-recursive case [let k x = e1 in e2]

     [fun x -> e1] = handler
     bound variable [k] = Bound_continuation.t
     [e2] = body (has bound variable [k] in scope) **)
  | Non_recursive of
    { handler : continuation_handler;
      body : (Bound_continuation.t, core_exp) Name_abstraction.t;}

  (** Recursive case, we have a set of (mutually recursive) continuations
     [let rec K x in e] where [K] is a map of continuations
     [x] is the set of invariant parameters
     bound variable [K] is in the scope of [e]

     [x] = invariant_params (Bound_parameters.t)
     [K] = continuation_map
     [e] = body **)
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

(** [Name_abstraction] setup for [core_exp]s **)
(** Nominal renaming for [core_exp] **)
let rec apply_renaming t renaming : core_exp =
  match t with
  | Var t -> Var (Simple.apply_renaming t renaming)
  | Let t -> Let (apply_renaming_let t renaming)
  | Let_cont t -> Let_cont (apply_renaming_let_cont t renaming)
  | Apply t -> Apply (apply_renaming_apply t renaming)
  | Apply_cont t -> Apply_cont (apply_renaming_apply_cont t renaming)
  | Switch t -> Switch (apply_renaming_switch t renaming)
  | Invalid t -> Invalid t

(* renaming for [Let] *)
and apply_renaming_let ({ let_abst; body } as t) renaming : let_expr =
  let let_abst' =
    Name_abstraction.apply_renaming
      (module Bound_pattern)
      let_abst renaming
      ~apply_renaming_to_term:apply_renaming
  in
  let defining_expr' = apply_renaming_named body renaming in
  { let_abst = let_abst'; body = defining_expr' }

and apply_renaming_named t renaming : named =
  match t with
  | Simple simple ->
    Simple (Simple.apply_renaming simple renaming)
  | Prim prim ->
    Prim (Flambda_primitive.apply_renaming prim renaming)
  | Set_of_closures set ->
    Set_of_closures (Set_of_closures.apply_renaming set renaming)
  | Static_consts consts ->
    Static_consts (apply_renaming_static_const_group consts renaming)
  | Rec_info info ->
    Rec_info (Rec_info_expr.apply_renaming info renaming)

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

and apply_renaming_recursive_let_expr ({continuation_map; body} as t) renaming
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
      ({ callee; continuation; exn_continuation; args; call_kind} as t) renaming:
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
and apply_renaming_apply_cont ({k; args} as t) renaming : apply_cont_expr =
  let k = Renaming.apply_continuation renaming k in
  let args = List.map (fun x -> apply_renaming x renaming) args in
  { k = k; args = args }

(* renaming for [Switch] *)
and apply_renaming_switch ({scrutinee; arms} as t) renaming : switch_expr =
  let scrutinee = apply_renaming scrutinee renaming in
  let arms = Targetint_31_63.Map.map (fun x -> apply_renaming x renaming) arms in
  { scrutinee = scrutinee; arms = arms }

(** Basic pretty-printer for [core_exp]s **)
let rec print ppf e =
  match e with
  | Var t -> Simple.print ppf t
  | Let t -> print_let ppf t
  | Let_cont t -> print_let_cont ppf t
  | Apply t -> print_apply ppf t
  | Apply_cont t -> print_apply_cont ppf t
  | Switch t -> print_switch ppf t
  | Invalid { message } -> fprintf ppf "Invalid %s" message

and print_let ppf ({let_abst; body} as t : let_expr) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_pattern)
    let_abst ~apply_renaming_to_term:apply_renaming
    ~f:(fun bound let_body ->
      fprintf ppf "let %a = %a in\n %a"
        Bound_pattern.print bound
        print let_body
        print_named body)

and print_named ppf (t : named) =
  match t with
  | Simple simple -> Simple.print ppf simple
  | Prim prim -> Flambda_primitive.print ppf prim
  | Set_of_closures clo -> Set_of_closures.print ppf clo
  | Static_consts consts -> print_static_const_group ppf consts
  | Rec_info info -> Rec_info_expr.print ppf info

and print_static_const_group ppf t =
  Format.pp_print_list ~pp_sep:Format.pp_print_space print_static_const_or_code ppf t

and print_static_const_or_code ppf t =
  match t with
  | Code code -> Code0.print ~print_function_params_and_body ppf code
  | Deleted_code -> fprintf ppf "Deleted_code"
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
      ~f:(fun k body ->
        Bound_continuation.print ppf k;
        Name_abstraction.pattern_match_for_printing
          (module Bound_parameters) handler
          ~apply_renaming_to_term:apply_renaming
          ~f:(fun k let_body ->
            fprintf ppf "letc %a = %a in \n %a"
            Bound_parameters.print k
            print let_body
            print body))
  | Recursive t ->
    fprintf ppf "letc ";
    Name_abstraction.pattern_match_for_printing
      (module Bound_continuations) t
      ~apply_renaming_to_term:apply_renaming_recursive_let_expr
      ~f:(fun k body -> print_recursive_let_cont ppf k body)

and print_recursive_let_cont ppf (k : Bound_continuations.t)
      ({continuation_map; body} as t : recursive_let_expr) =
  fprintf ppf "[ %a ] " Bound_continuations.print k;
  Name_abstraction.pattern_match_for_printing
    (module Bound_parameters) continuation_map
    ~apply_renaming_to_term:apply_renaming_cont_map
    ~f:(fun k body ->
      fprintf ppf "(%a)\n" Bound_parameters.print k;
      Continuation.Map.iter (print_continuation_handler ppf) body;
    );
  fprintf ppf " in\n %a" print body

and print_continuation_handler ppf key (t : continuation_handler) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_parameters) t
    ~apply_renaming_to_term:apply_renaming
    ~f:(fun k body ->
      fprintf ppf "fun %a -> %a" Bound_parameters.print k print body)

and print_apply ppf
      ({callee; continuation; exn_continuation; args; _} as t : apply_expr) =
  fprintf ppf "%a %a %a "
    print callee
    Apply_expr.Result_continuation.print continuation
    Continuation.print exn_continuation;
  List.iter (print ppf) args

and print_apply_cont ppf ({k ; args} as t : apply_cont_expr) =
  fprintf ppf "%a " Continuation.print k;
  List.iter (print ppf) args

and print_switch ppf ({scrutinee; arms} as t : switch_expr) =
  fprintf ppf "switch %a :" print scrutinee;
  Targetint_31_63.Map.iter (print_arm ppf) arms

and print_arm ppf key arm =
  fprintf ppf "| %a -> %a\n"
    Targetint_31_63.print key
    print arm

(** [ids_for_export] is the set of bound variables for a given expression **)
let rec ids_for_export (t : core_exp) =
  match t with
  | Var t -> Ids_for_export.from_simple t
  | Let t -> ids_for_export_let t
  | Let_cont t -> ids_for_export_let_cont t
  | Apply t -> ids_for_export_apply t
  | Apply_cont t -> ids_for_export_apply_cont t
  | Switch t -> ids_for_export_switch t
  | Invalid t -> Ids_for_export.empty

(* ids for [Let_expr] *)
and ids_for_export_let { let_abst; body } =
  let body_ids = ids_for_export_named body in
  let let_abst_ids =
    Name_abstraction.ids_for_export
      (module Bound_pattern)
      let_abst ~ids_for_export_of_term:ids_for_export
  in
  Ids_for_export.union body_ids let_abst_ids

and ids_for_export_named (t : named) =
  match t with
  | Simple simple -> Ids_for_export.from_simple simple
  | Prim prim -> Flambda_primitive.ids_for_export prim
  | Set_of_closures set -> Set_of_closures.ids_for_export set
  | Static_consts consts -> ids_for_export_static_const_group consts
  | Rec_info info -> Rec_info_expr.ids_for_export info

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

and ids_for_export_recursive_let_expr ({continuation_map; body} as t : recursive_let_expr) =
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
  let create (bound_pattern : Bound_pattern.t) (defining_expr : named) body =
    (match defining_expr, bound_pattern with
    | Prim _, Singleton _
    | Simple _, Singleton _
    | Rec_info _, Singleton _
    | Set_of_closures _, Set_of_closures _ -> ()
    | _ , _ -> Misc.fatal_error "[Let.create] Mismatched bound pattern and defining expr");
    Let { let_abst = A.create bound_pattern body; body = defining_expr }

  module Pattern_match_pair_error = struct
    type t = Mismatched_let_bindings

    let to_string = function
      | Mismatched_let_bindings -> "Mismatched let bindings"
  end

  (* Treat "dynamic binding" (statically scoped binding under lambda abstraction)
     and "static binding" (globally scoped mapping of statics) differently *)
  let pattern_match_pair
        ({let_abst = let_abst1; body = body1} as t1)
        ({let_abst = let_abst2; body = body2} as t2)
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
        | _,_ -> Error Pattern_match_pair_error.Mismatched_let_bindings
      )
    )
end

module Core_continuation_handler = struct
  module A = Name_abstraction.Make (Bound_parameters) (T0)
  let create = A.create
  let pattern_match_pair = A.pattern_match_pair
end

module Core_letrec_body = struct
  module A = Name_abstraction.Make (Bound_continuation) (T0)
  let create = A.create
  let pattern_match_pair = A.pattern_match_pair
end

module Core_continuation_map = struct
  module A = Name_abstraction.Make (Bound_parameters) (ContMap)
  let create = A.create
  let pattern_match_pair = A.pattern_match_pair
end

module Core_recursive = struct
  module A = Name_abstraction.Make (Bound_continuations) (RecursiveLetExpr)
  let create = A.create
  let pattern_match_pair = A.pattern_match_pair
end

module Core_function_params_and_body = struct
  module A = Name_abstraction.Make (Bound_for_function) (T0)
  let create = A.create

  let pattern_match_pair t1 t2 ~f =
    A.pattern_match_pair t1 t2
      ~f:(fun
           bound_for_function body1 body2
           ->
             f
               ~return_continuation:
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

  let create =
    Code0.create
      ~print_function_params_and_body:print_function_params_and_body

  let with_code_id = Code0.with_code_id

  let with_params_and_body =
    Code0.with_params_and_body
      ~print_function_params_and_body:print_function_params_and_body

  let with_newer_version_of = Code0.with_newer_version_of

  let free_names = Code0.free_names

  let apply_renaming =
    Code0.apply_renaming
      ~apply_renaming_function_params_and_body:
        apply_renaming_function_params_and_body

  let print =
    Code0.print
      ~print_function_params_and_body:print_function_params_and_body

  let ids_for_export =
    Code0.ids_for_export
      ~ids_for_export_function_params_and_body:
        ids_for_export_function_params_and_body

  let map_result_types = Code0.map_result_types

  let free_names_of_params_and_body = Code0.free_names_of_params_and_body
end

(** Translation from flambda2 terms to simplified core language **)
let simple_to_core (v : Simple.t) : core_exp = Var v

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
  Core_let.create var (Let_expr.defining_expr e |> named_to_core)
    (flambda_expr_to_core body)

and named_to_core (e : Flambda.named) : named =
  match e with
  | Simple e -> Simple e
  | Prim (t, _) -> Prim t
  | Set_of_closures e -> Set_of_closures e
  | Static_consts e -> Static_consts (static_consts_to_core e)
  | Rec_info t -> Rec_info t

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
      {handler = h; num_free_occurrences; is_applied_with_traps} ->
    let (contvar, scoped_body) =
      Non_recursive_let_cont_handler.pattern_match
        h ~f:(fun contvar ~body -> (contvar, body)) in
    Let_cont (Non_recursive {
      handler =
        Non_recursive_let_cont_handler.handler h |> cont_handler_to_core;
      body = flambda_expr_to_core scoped_body |>
        Core_letrec_body.create contvar;})

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

(* The most naive equality type, a boolean *)
type eq = bool

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

(** Equality between two programs given a context **)
(* For now, following a naive alpha-equivalence equality from [compare/compare]
    (without the discriminant) *)

let equiv_symbols env sym1 sym2 : eq =
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
      ~f:(fun x ((id1, (slot1, decl1)), (id2, (slot2, decl2))) ->
        equiv_function_slot env slot1 slot2 &&
        equiv_function_decl env decl1 decl2)
      ~acc: true
  in
  value_slots_eq && function_slots_eq

let equiv_rec_info _env info1 info2 : eq =
  Rec_info_expr.equal info1 info2

let rec equiv (env:Env.t) e1 e2 : eq =
  match e1, e2 with
  | Let e1, Let e2 -> equiv_let env e1 e2
  | Let_cont e1, Let_cont e2 -> equiv_let_cont env e1 e2
  | Apply e1, Apply e2 -> equiv_apply env e1 e2
  | Apply_cont e1, Apply_cont e2 -> equiv_apply_cont env e1 e2
  | Switch e1, Switch e2 -> equiv_switch env e1 e2
  | Invalid _, Invalid _ -> true

(* [let_expr] *)
and equiv_let env ({let_abst = let_abst1; body = body1} as e1)
                    ({let_abst = let_abst2; body = body2} as e2) : eq =
  Core_let.pattern_match_pair e1 e2
    (fun bound let_bound1 let_bound2 ->
       equiv_named env body1 body2 && equiv env let_bound1 let_bound2)
    (fun bound1 bound2 let_bound1 let_bound2 ->
       match body1, body2 with
       | Static_consts consts1, Static_consts consts2 ->
         equiv_let_symbol_exprs env
           (bound1, consts1, body1)
           (bound2, consts2, body2)
       | _, _ -> Misc.fatal_error "Static LHS has dynamic RHS")
  |> function | Ok comp -> comp | _ -> false

and equiv_let_symbol_exprs env
      (static1, const1, body1) (static2, const2, body2) : eq =
  equiv_bound_static env static1 static2 &&
  (List.combine const1 const2 |>
   List.fold_left (fun x (e1, e2) -> x && equiv_static_consts env e1 e2) true) &&
  equiv_named env body1 body2

and equiv_static_consts env
  (const1 : static_const_or_code) (const2 : static_const_or_code) : eq =
  match const1, const2 with
  | Code code1, Code code2 -> equiv_code env code1 code2
  | Static_const (Block (tag1, mut1, fields1)),
    Static_const (Block (tag2, mut2, fields2)) ->
    equiv_block env (tag1, mut1, fields1) (tag2, mut2, fields2)
  | Static_const (Set_of_closures set1), Static_const (Set_of_closures set2) ->
    equiv_set_of_closures env set1 set2
  | _, _ -> compare const1 const2 = 0

and equiv_code env
  (code1 : function_params_and_body Code0.t) (code2 : function_params_and_body Code0.t) =
  let code1 : function_params_and_body = Core_code.params_and_body code1 in
  let code2 : function_params_and_body = Core_code.params_and_body code2 in
  Core_function_params_and_body.pattern_match_pair code1 code2
    ~f:(fun
         ~return_continuation
         ~exn_continuation
         params
         ~body1
         ~body2
         ~my_closure
         ~my_region
         ~my_depth ->
         equiv env body1 body2)

and equiv_block env (tag1, mut1, fields1) (tag2, mut2, fields2) =
  Tag.Scannable.equal tag1 tag2 &&
  Mutability.compare mut1 mut2 = 0 &&
  (List.combine fields1 fields2 |>
   List.fold_left (fun x (e1, e2) -> x && Field_of_static_block.equal e1 e2)
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
      equiv_function_slots env slot1 slot2
    in
    let clo1 = Function_slot.Lmap.bindings clo1 in
    let clo2 = Function_slot.Lmap.bindings clo2 in
    List.combine clo1 clo2 |>
    List.fold_left (fun x (e1, e2) -> x && closure_bindings env e1 e2) true
  | _, _ -> false

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
  | _, _ ->
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
  match (prim1:Flambda_primitive.t), (prim2:Flambda_primitive.t) with
  | Unary (op1, arg1), Unary (op2, arg2) ->
    Flambda_primitive.equal_unary_primitive op1 op2 &&
    equiv_simple env arg1 arg2
  | Binary (op1, arg1_1, arg1_2), Binary (op2, arg2_1, arg2_2) ->
    Flambda_primitive.equal_binary_primitive op1 op2 &&
    equiv_simple env arg1_1 arg2_1 &&
    equiv_simple env arg1_2 arg2_2
  | Ternary (op1, arg1_1, arg1_2, arg1_3),
    Ternary (op2, arg2_1, arg2_2, arg2_3) ->
    Flambda_primitive.equal_ternary_primitive op1 op2 &&
    equiv_simple env arg1_1 arg2_1 &&
    equiv_simple env arg1_2 arg2_2 &&
    equiv_simple env arg1_3 arg2_3
  | Variadic (op1, args1), Variadic (op2, args2) ->
    Flambda_primitive.equal_variadic_primitive op1 op2 &&
    (List.combine args1 args2 |>
      List.fold_left (fun x (e1, e2) -> x && equiv_simple env e1 e2) true)
  | _, _ -> false

(* [let_cont_expr] *)
and equiv_let_cont env let_cont1 let_cont2 : eq =
  match let_cont1, let_cont2 with
  | Non_recursive {handler = handler1; body = body1},
    Non_recursive {handler = handler2; body = body2} ->
    failwith "Unimplemented"
  | Recursive handlers1, Recursive handlers2 ->
    failwith "Unimplemented"

(* [let_apply] *)
and equiv_apply env e1 e2 : eq =
  failwith "Unimplemented"

and equiv_apply_cont env e1 e2 : eq =
  failwith "Unimplemented"

and equiv_switch env e1 e2 : eq =
  failwith "Unimplemented"

let core_eq = Env.create () |> equiv

(** Normalization *)
(* TODO *)
let rec normalize (e:core_exp) : core_exp =
  match e with
  | Var _ -> e
  | Let e -> failwith "Unimplemented"
  | Let_cont _ -> failwith "Unimplemented"
  | Apply _ -> failwith "Unimplemented"
  | Apply_cont _ -> failwith "Unimplemented"
  | Switch _ -> failwith "Unimplemented"
  | Invalid _ -> failwith "Unimplemented"

let simulation_relation src tgt =
  let {Simplify.unit = tgt; exported_offsets; cmx; all_code} = tgt in
  let src_core = Flambda_unit.body src |> flambda_expr_to_core in
  let tgt_core = Flambda_unit.body tgt |> flambda_expr_to_core in
  core_eq src_core tgt_core

(** Top-level validator *)
let validate ~cmx_loader ~round src =
  let tgt = Simplify.run ~cmx_loader ~round src in
  simulation_relation src tgt
