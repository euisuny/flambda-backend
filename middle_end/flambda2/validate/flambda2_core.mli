module P = Flambda_primitive

(** Simplified core of [flambda2] terms **)
(* (1) Simple.t -> core_exp for [Apply*] expressions
   (2) Ignore [Num_occurrences] (which is used for making inlining decisions)
   (3) Ignored traps for now *)
module SlotMap : Map.S with type key = Function_slot.t

module With_delayed_renaming : sig
  type 'descr t
end

type core_exp = exp_descr With_delayed_renaming.t

and exp_descr =
  | Named of named
  | Let of let_expr
  | Let_cont of let_cont_expr
  | Apply of apply_expr
  | Lambda of lambda_expr (* A lambda for code expressions *)
  | Switch of switch_expr
  | Invalid of { message : string }

and lambda_expr = (Bound_parameters.t, core_exp) Name_abstraction.t

(** Let expressions [let x = e1 in e2]

   [fun x -> e2] = let_abst
   [e1] = body **)
and let_expr =
  { let_abst : (Bound_for_let.t, core_exp) Name_abstraction.t;
    expr_body : core_exp; }

and literal =
  | Simple of Simple.t
  | Cont of Continuation.t
  | Res_cont of Apply_expr.Result_continuation.t
  | Slot of (Variable.t * slot)
  | Code_id of Code_id.t

and named =
  | Literal of literal
  | Prim of primitive
  | Closure_expr of (Variable.t * Function_slot.t * set_of_closures)
  | Set_of_closures of set_of_closures
  | Static_consts of static_const_group
  | Rec_info of Rec_info_expr.t

and slot =
  | Function_slot of Function_slot.t
  | Value_slot of Value_slot.t

and set_of_closures =
  { function_decls : function_declarations;
    value_slots : core_exp Value_slot.Map.t}

and function_declarations = core_exp SlotMap.t

and primitive =
  | Nullary of P.nullary_primitive
  | Unary of P.unary_primitive * core_exp
  | Binary of P.binary_primitive * core_exp * core_exp
  | Ternary of P.ternary_primitive * core_exp * core_exp * core_exp
  | Variadic of P.variadic_primitive * core_exp list

(* Named lambda expression that has an additional closure parameter *)
and function_params_and_body =
  { expr: (Bound_var.t, lambda_expr) Name_abstraction.t;
    anon: bool }

and static_const_or_code =
  | Code of function_params_and_body
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
  { handler : lambda_expr;
    body : (Bound_continuation.t, core_exp) Name_abstraction.t;}

and apply_expr =
  { callee: core_exp;
    ret_continuation: core_exp;
    exn_continuation: core_exp;
    region: core_exp;
    apply_args: core_exp list; }

and switch_expr =
  { scrutinee : core_exp;
    arms : core_exp Targetint_31_63.Map.t }

type continuation_handler_map = lambda_expr Continuation.Map.t

type simple_type =
  | Var of Variable.t
  | Symbol of Symbol.t
  | Naked_immediate of Targetint_31_63.t
  | Tagged_immediate of Targetint_31_63.t
  | Naked_float of Numeric_types.Float_by_bit_pattern.t
  | Naked_int32 of Int32.t
  | Naked_int64 of Int64.t
  | Naked_nativeint of Targetint_32_64.t

val simple_with_type : Simple.t -> simple_type

module Expr : sig
  type t = core_exp
  type descr = exp_descr
  val ids_for_export : t -> Ids_for_export.t
  val descr : t -> exp_descr
  val create_named : named -> t
  val create_let : let_expr -> t
  val create_let_cont : let_cont_expr -> t
  val create_apply : apply_expr -> t
  val create_lambda : lambda_expr -> t
  val create_switch : switch_expr -> t
  val create_invalid : string -> t
end

module Core_let : sig
  type t = let_expr
  val create : x:Bound_for_let.t -> e1:core_exp -> e2 :core_exp -> core_exp

  module Pattern_match_pair_error : sig
    type t = Mismatched_let_bindings
  end

  val pattern_match :
    let_expr -> f:(x:Bound_for_let.t -> e1:core_exp -> e2:core_exp -> 'a) -> 'a

  val pattern_match_pair :
    t -> t -> (Bound_for_let.t -> core_exp -> core_exp -> 'a) ->
    (Bound_codelike.t -> Bound_codelike.t -> core_exp -> core_exp -> 'a) ->
    ('a, Pattern_match_pair_error.t) Result.t
end

module Core_letcont_body : sig
  type t = (Bound_continuation.t, core_exp) Name_abstraction.t

  val create : Bound_continuation.t -> core_exp -> t
  val pattern_match : t -> (Bound_continuation.t -> core_exp -> 'a) -> 'a
  val pattern_match_pair :
    t -> t -> (Bound_continuation.t -> core_exp -> core_exp -> 'a) -> 'a
end

module Core_letcont : sig
  type t

  val print : Format.formatter -> let_cont_expr -> unit

  val create :
    lambda_expr ->
    body:((Bound_continuation.t, core_exp) Name_abstraction.t) ->
    core_exp
end

module Core_lambda : sig
  type t = lambda_expr

  val create : Bound_parameters.t -> Expr.t -> t

  val pattern_match :
    t -> f:(Bound_parameters.t -> Expr.t -> 'a) -> 'a

  val pattern_match_pair:
    t -> t ->
    f:(Bound_parameters.t -> core_exp -> core_exp -> 'a) -> 'a
end

module Core_function_params_and_body : sig
  type t = (Bound_var.t, Core_lambda.t) Name_abstraction.t

  val create : Bound_var.t -> Core_lambda.t -> t

  val my_closure : t -> Bound_var.t

  val lambda_expr : t -> Core_lambda.t

  val pattern_match :
    t -> f:(Bound_var.t -> Core_lambda.t -> 'a) -> 'a

  val pattern_match_pair :
    t -> t -> f:(Bound_parameters.t ->
      body1:core_exp -> body2:core_exp ->
      my_closure:Bound_var.t -> 'a)
    -> 'a
end

val print : Format.formatter -> core_exp -> unit
val print_static_pattern : Format.formatter -> Bound_codelike.Pattern.t -> unit
val print_prim : Format.formatter -> primitive -> unit
val print_bound_pattern : Format.formatter -> Bound_for_let.t -> unit
val print_static_const : Format.formatter -> static_const -> unit

val descr : core_exp -> exp_descr

val apply_renaming : core_exp -> Renaming.t -> core_exp

val core_fmap : ('a -> literal -> core_exp) -> 'a -> core_exp -> core_exp

(* Fixpoint functions for core expressions *)
val let_fix : (core_exp -> core_exp) -> let_expr -> core_exp
val let_cont_fix : (core_exp -> core_exp) -> let_cont_expr -> core_exp
val apply_fix : (core_exp -> core_exp) -> apply_expr -> core_exp
val lambda_fix : (core_exp -> core_exp) -> lambda_expr -> core_exp
val switch_fix : (core_exp -> core_exp) -> switch_expr -> core_exp

val named_fix :
  (core_exp -> core_exp) ->
  ('a -> literal -> core_exp) ->
  'a -> named -> core_exp
val set_of_closures_fix :
  (core_exp -> core_exp) ->
  set_of_closures -> set_of_closures
val prim_fix : (core_exp -> core_exp) -> primitive -> core_exp
val static_const_group_fix :
  (core_exp -> core_exp) ->
  static_const_group -> core_exp

val print_set_of_closures : Format.formatter -> set_of_closures -> unit
val literal_contained : literal -> literal -> bool

(* Effects *)
val no_effects_or_coeffects : core_exp -> bool
val no_effects : core_exp -> bool
val can_inline : core_exp -> bool
val returns_unit : core_exp -> bool
