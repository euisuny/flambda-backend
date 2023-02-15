module P = Flambda_primitive

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
    expr_body : core_exp; }

and named =
  | Simple of Simple.t
  | Prim of primitive
  | Closure_expr of (Function_slot.t * set_of_closures)
  | Set_of_closures of set_of_closures
  | Static_consts of static_const_group
  | Rec_info of Rec_info_expr.t

and set_of_closures =
  { function_decls : function_declarations;
    value_slots : (Simple.t * Flambda_kind.With_subkind.t) Value_slot.Map.t;
    alloc_mode : Alloc_mode.For_allocations.t }

and function_declarations =
  { funs : function_expr Function_slot.Map.t;
    in_order : function_expr Function_slot.Lmap.t}

and function_expr =
  | Id of Code_id.t
  | Exp of core_exp

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
  | Static_const of static_const

and static_const_group = static_const_or_code list

and static_const =
  | Static_set_of_closures of set_of_closures
  | Block of Tag.Scannable.t * Mutability.t * core_exp list
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
    apply_args: core_exp list;
    call_kind: Call_kind.t; }

and apply_cont_expr =
  { k : Continuation.t;
    args : core_exp list }

and switch_expr =
  { scrutinee : core_exp;
    arms : core_exp Targetint_31_63.Map.t }

module T0 : sig
  type t = core_exp

  val apply_renaming : t -> Renaming.t -> t
  val ids_for_export : t -> Ids_for_export.t
end

module ContMap : sig
  type t = continuation_handler_map
  val apply_renaming : t -> Renaming.t -> t
  val ids_for_export : t -> Ids_for_export.t
end

module RecursiveLetExpr : sig
  type t = recursive_let_expr
  val apply_renaming : t -> Renaming.t -> t
  val ids_for_export : t -> Ids_for_export.t
end

module Core_let : sig
  val create : x:Bound_pattern.t -> e1:core_exp -> e2 :core_exp -> core_exp

  type t = let_expr

  module Pattern_match_pair_error : sig
    type t = Mismatched_let_bindings
  end

  val pattern_match :
    let_expr -> f:(x:Bound_pattern.t -> e1:core_exp -> e2:core_exp -> 'a) -> 'a

  val pattern_match_pair :
    t -> t -> (Bound_pattern.t -> core_exp -> core_exp -> 'a) ->
    (Bound_static.t -> Bound_static.t -> core_exp -> core_exp -> 'a) ->
    ('a, Pattern_match_pair_error.t) Result.t
end

module Core_continuation_handler : sig
  type t = continuation_handler
  val create : Bound_parameters.t -> core_exp -> t

  val pattern_match : t -> (Bound_parameters.t -> core_exp -> 'a) -> 'a
  val pattern_match_pair :
    t -> t -> (Bound_parameters.t -> core_exp -> core_exp -> 'a) -> 'a
end

module Core_letcont_body : sig
  type t = (Bound_continuation.t, core_exp) Name_abstraction.t

  val create : Bound_continuation.t -> core_exp -> t
  val pattern_match : t -> (Bound_continuation.t -> core_exp -> 'a) -> 'a
  val pattern_match_pair :
    t -> t -> (Bound_continuation.t -> core_exp -> core_exp -> 'a) -> 'a
end

module Core_recursive : sig

  type t = (Bound_continuations.t, recursive_let_expr) Name_abstraction.t

  val create : Bound_continuations.t -> recursive_let_expr -> t

  val pattern_match_pair :
    t -> t ->
    (Bound_parameters.t ->
     core_exp ->
     core_exp -> continuation_handler_map -> continuation_handler_map -> 'a) -> 'a
end

module Core_function_params_and_body : sig
  type t = (Bound_for_function.t, T0.t) Name_abstraction.t

  val create : Bound_for_function.t -> T0.t -> t

  val pattern_match_pair :
    t -> t -> f:(
      return_continuation:Continuation.t ->
      exn_continuation:Continuation.t ->
      Bound_parameters.t ->
      body1:core_exp -> body2:core_exp ->
      my_closure:Variable.t -> my_region:Variable.t -> my_depth:Variable.t -> 'a)
    -> 'a
end

module Core_code : sig
  type t = Core_function_params_and_body.t Code0.t

  val code_metadata : 'a Code0.t -> Code_metadata.t

  val params_and_body : 'a Code0.t -> 'a

  val create_with_metadata :
    params_and_body:function_params_and_body ->
    free_names_of_params_and_body:Name_occurrences.t ->
    code_metadata:Code_metadata.t -> t
end

module Core_continuation_map : sig
  type t = (Bound_parameters.t, continuation_handler_map) Name_abstraction.t
  val create : Bound_parameters.t -> continuation_handler_map -> t
end

val print : Format.formatter -> core_exp -> unit
val print_static_pattern : Format.formatter -> Bound_static.Pattern.t -> unit
val print_bound_pattern : Format.formatter -> Bound_pattern.t -> unit

val apply_renaming : core_exp -> Renaming.t -> core_exp
