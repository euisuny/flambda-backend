module P = Flambda_primitive

(** Simplified core of [flambda2] terms **)
(* (1) Simple.t -> core_exp for [Apply*] expressions
   (2) Ignore [Num_occurrences] (which is used for making inlining decisions)
   (3) Ignored traps for now *)
module SlotMap : Map.S with type key = Function_slot.t

module With_delayed_renaming : sig
  type 'descr t
end

(* ========================================================================== *)
(** [Flambda2] core expressions. *)
(* Idealized lambda-calculus for [Flambda2] expressions. *)

type core_exp = exp_descr With_delayed_renaming.t

and exp_descr =
  | Var of variable
  (* Primitive operations *)
  | Prim of primitive
  (* Static constants, which include literal expressions and blocks *)
  | Consts of constant list
  (* Application *)
  | App of apply_expr
  (* A lambda for code expressions and continuations. *)
  | Lam of lambda_expr
  (* LATER: Is this necessary? *)
  | Closure_expr of (Variable.t * Function_slot.t * closures)
  (* Closures *)
  | Closures of closures
  (* Switch expression. *)
  | Switch of switch_expr
  (* "Invalid" *)
  | Error of { message : string }

(* Variables. *)
and variable =
  | Simple of Simple.t
  | Slot of (Variable.t * slot)

(* Lambda expressions: captures all variants of lambdas in Flambda2, including
   - code bindings
   - lambda expressions
   - "continuation handler" expressions

   Lambda expressions are of the form : [ λ k_r k_e region args => e ]
   where [k_r] and [k_e] are the return and exceptional continuations, the [region]
   variable indicates the closure environments, and [args] are the formal arguments
   to the function. *)
and lambda_expr = (Bound_parameters.t, core_exp) Name_abstraction.t

(* Slots for functions and values in the environment *)
and slot =
  | Function_slot of Function_slot.t
  | Value_slot of Value_slot.t

(* Closures, which store function declarations and an environment for values. *)
and closures =
  { (* Function declarations (N.B. the map is ordered.) *)
    function_decls : core_exp SlotMap.t;
    (* Environment *)
    value_slots : core_exp Value_slot.Map.t}

(* Application. *)
and apply_expr =
  { callee: core_exp;
    apply_args: core_exp list; }

(* Switch. *)
and switch_expr =
  { scrutinee : core_exp;
    arms : core_exp Targetint_31_63.Map.t }

(* Primitive operands. *)
and primitive =
  | Nullary of P.nullary_primitive
  | Unary of P.unary_primitive * core_exp
  | Binary of P.binary_primitive * core_exp * core_exp
  | Ternary of P.ternary_primitive * core_exp * core_exp * core_exp
  | Variadic of P.variadic_primitive * core_exp list

(* Constants. *)
and constant =
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

(* ========================================================================== *)

(* type simple_type = *)
(*   | Var of Variable.t *)
(*   | Symbol of Symbol.t *)
(*   | Naked_immediate of Targetint_31_63.t *)
(*   | Tagged_immediate of Targetint_31_63.t *)
(*   | Naked_float of Numeric_types.Float_by_bit_pattern.t *)
(*   | Naked_int32 of Int32.t *)
(*   | Naked_int64 of Int64.t *)
(*   | Naked_nativeint of Targetint_32_64.t *)

(* val simple_with_type : Simple.t -> simple_type *)

module Expr : sig
  type t = core_exp
  type descr = exp_descr
  val ids_for_export : t -> Ids_for_export.t
  val apply_renaming : core_exp -> Renaming.t -> core_exp
  val descr : t -> exp_descr
  val create_var : variable -> t
  val create_prim : primitive -> t
  val create_consts : constant list -> t
  val create_apply : apply_expr -> t
  val create_lambda : lambda_expr -> t
  val create_closure_expr : (Variable.t * Function_slot.t * closures) -> t
  val create_closures : closures -> t
  val create_switch : switch_expr -> t
  val create_invalid : string -> t
end

(* module Core_let : sig *)
(*   type t = let_expr *)
(*   val create : x:Bound_for_let.t -> e1:core_exp -> e2 :core_exp -> core_exp *)

(*   module Pattern_match_pair_error : sig *)
(*     type t = Mismatched_let_bindings *)
(*   end *)

(*   val pattern_match : *)
(*     let_expr -> f:(x:Bound_for_let.t -> e1:core_exp -> e2:core_exp -> 'a) -> 'a *)

(*   val pattern_match_pair : *)
(*     t -> t -> (Bound_for_let.t -> core_exp -> core_exp -> 'a) -> *)
(*     (Bound_codelike.t -> Bound_codelike.t -> core_exp -> core_exp -> 'a) -> *)
(*     ('a, Pattern_match_pair_error.t) Result.t *)
(* end *)

(* module Core_letcont_body : sig *)
(*   type t = (Bound_continuation.t, core_exp) Name_abstraction.t *)

(*   val create : Bound_continuation.t -> core_exp -> t *)
(*   val pattern_match : t -> (Bound_continuation.t -> core_exp -> 'a) -> 'a *)
(*   val pattern_match_pair : *)
(*     t -> t -> (Bound_continuation.t -> core_exp -> core_exp -> 'a) -> 'a *)
(* end *)

(* module Core_letcont : sig *)
(*   type t *)

(*   val print : Format.formatter -> let_cont_expr -> unit *)

(*   val create : *)
(*     lambda_expr -> *)
(*     body:((Bound_continuation.t, core_exp) Name_abstraction.t) -> *)
(*     core_exp *)
(* end *)

module Core_lambda : sig
  type t = lambda_expr

  val create : Bound_parameters.t -> Expr.t -> t

  val unary_create : Variable.t -> Expr.t -> t

  val pattern_match :
    t -> f:(Bound_parameters.t -> Expr.t -> 'a) -> 'a

  val pattern_match_pair:
    t -> t ->
    f:(Bound_parameters.t -> core_exp -> core_exp -> 'a) -> 'a
end

(* module Core_function_params_and_body : sig *)
(*   type t = (Bound_var.t, Core_lambda.t) Name_abstraction.t *)

(*   val create : Bound_var.t -> Core_lambda.t -> t *)

(*   val my_closure : t -> Bound_var.t *)

(*   val lambda_expr : t -> Core_lambda.t *)

(*   val pattern_match : *)
(*     t -> f:(Bound_var.t -> Core_lambda.t -> 'a) -> 'a *)

(*   val pattern_match_pair : *)
(*     t -> t -> f:(Bound_parameters.t -> *)
(*       body1:core_exp -> body2:core_exp -> *)
(*       my_closure:Bound_var.t -> 'a) *)
(*     -> 'a *)
(* end *)

val print : Format.formatter -> core_exp -> unit
(* val print_static_pattern : Format.formatter -> Bound_codelike.Pattern.t -> unit *)
(* val print_prim : Format.formatter -> primitive -> unit *)
(* val print_bound_pattern : Format.formatter -> Bound_for_let.t -> unit *)
(* val print_static_const : Format.formatter -> static_const -> unit *)

val descr : core_exp -> exp_descr

val apply_renaming : core_exp -> Renaming.t -> core_exp

(* val core_fmap : ('a -> literal -> core_exp) -> 'a -> core_exp -> core_exp *)

(* (\* Fixpoint functions for core expressions *\) *)
(* val let_fix : (core_exp -> core_exp) -> let_expr -> core_exp *)
(* val let_cont_fix : (core_exp -> core_exp) -> let_cont_expr -> core_exp *)
(* val apply_fix : (core_exp -> core_exp) -> apply_expr -> core_exp *)
(* val lambda_fix : (core_exp -> core_exp) -> lambda_expr -> core_exp *)
(* val switch_fix : (core_exp -> core_exp) -> switch_expr -> core_exp *)

(* val named_fix : *)
(*   (core_exp -> core_exp) -> *)
(*   ('a -> literal -> core_exp) -> *)
(*   'a -> named -> core_exp *)
(* val set_of_closures_fix : *)
(*   (core_exp -> core_exp) -> *)
(*   set_of_closures -> set_of_closures *)
(* val prim_fix : (core_exp -> core_exp) -> primitive -> core_exp *)
(* val static_const_group_fix : *)
(*   (core_exp -> core_exp) -> *)
(*   static_const_group -> core_exp *)

(* val print_set_of_closures : Format.formatter -> set_of_closures -> unit *)
(* val literal_contained : literal -> literal -> bool *)

(* (\* Effects *\) *)
(* val no_effects_or_coeffects : core_exp -> bool *)
(* val no_effects : core_exp -> bool *)
(* val can_inline : core_exp -> bool *)
(* val returns_unit : core_exp -> bool *)
