module P = Flambda_primitive

(** Simplified core of [flambda2] terms **)
(* (1) Simple.t -> core_exp for [Apply*] expessions
   (2) Ignore [Num_occurrences] (which is used for making inlining decisions)
   (3) Ignored traps for now *)

module Slot : sig include Slot.S end

type core_exp =
  | Base of base_exp
  | Lambda of lambda_exp
  | Let of let_exp
  | LetCont of let_cont_expr
  | Apply of apply_exp
  | ApplyCont of apply_cont_exp
  | Switch of switch_exp
  | Invalid of { message : string }

and base_exp =
  | Simple of Simple.t
  | Numeric of numeric
  | Slot of (Variable.t * Slot.t)
  | Closure_exp of (Variable.t * Slot.t * set_of_closures)
  | Consts of const
  | Prim of primitive
  | Set_of_closures of set_of_closures
  | Rec_info of Rec_info_expr.t

and numeric =
  | Float of Numeric_types.Float_by_bit_pattern.t
  | Int32 of Int32.t
  | Int64 of Int64.t
  | NativeInt of Targetint_32_64.t
  | Immediate of Targetint_31_63.t

and set_of_closures =
  { function_decls : core_exp Slot.Lmap.t;
    value_slots : core_exp Slot.Lmap.t}

and primitive =
  | Nullary of P.nullary_primitive
  | Unary of P.unary_primitive * core_exp
  | Binary of P.binary_primitive * core_exp * core_exp
  | Ternary of P.ternary_primitive * core_exp * core_exp * core_exp
  | Variadic of P.variadic_primitive * core_exp list

and const =
  | Block of Tag.Scannable.t * Mutability.t * core_exp list
  | Boxed_float of core_exp
  | Boxed_int32 of core_exp
  | Boxed_int64 of core_exp
  | Boxed_nativeint of core_exp
  | Immutable_float_block of core_exp list
  | Immutable_float_array of core_exp list
  | Immutable_value_array of core_exp list
  | Empty_array
  | Mutable_string of { initial_value : string }
  | Immutable_string of string

(** Let expessions [let x = e1 in e2]

    [fun x -> e2] = let_abst
    [e1] = body **)
and let_exp =
  { let_abst : (Bound_for_let.t, core_exp) Name_abstraction.t;
    (* Can have multiple in the case of a recursive let binding *)
    (* FIXME: Needs to change *)
    exp_body : core_exp list; }

and lambda_exp = (Bound_parameters.t, core_exp) Name_abstraction.t

and let_cont_expr =
  (* Non-recursive case [e1 where k x = e2]
     [fun x -> e2] = handler
     bound variable [k] = Bound_continuation.t
     [e1] = body (has bound variable [k] in scope) *)
  | Non_recursive of
    { handler : lambda_exp;
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
  { handlers : lambda_exp Continuation.Map.t;
    body : core_exp; }

and apply_exp =
  { callee: core_exp;
    continuation: core_exp;
    exn_continuation: core_exp;
    apply_args: core_exp list; }

and apply_cont_exp =
  { k : core_exp;
    args : core_exp list }

and switch_exp =
  { scrutinee : core_exp;
    arms : core_exp Targetint_31_63.Map.t }

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

val must_be_prim : core_exp -> primitive option

val must_be_slot : core_exp -> (Variable.t * Slot.t) option

val must_be_lambda : core_exp -> lambda_exp option

val must_be_apply : core_exp -> apply_exp option

val must_be_simple : core_exp -> Simple.t option

val must_be_simple_or_immediate : core_exp -> Simple.t option

val must_be_tagged_immediate : core_exp -> base_exp option

val must_be_untagged_immediate : core_exp -> base_exp option

val must_be_string_length :
  core_exp -> (Flambda_primitive.string_or_bytes * core_exp) option

val must_be_slot_exp :
  core_exp -> (Variable.t * Slot.t) option

val must_be_set_of_closures : core_exp -> set_of_closures option

val must_be_static_set_of_closures : const -> set_of_closures option

val must_have_closure : core_exp -> set_of_closures option

module T0 : sig
  type t = core_exp

  val apply_renaming : t -> Renaming.t -> t
  val ids_for_export : t -> Ids_for_export.t
end

module Core_let : sig
  val create : x:Bound_for_let.t -> e1:core_exp -> e2 :core_exp -> core_exp

  type t = let_exp

  module Pattern_match_pair_error : sig
    type t = Mismatched_let_bindings
  end

  val pattern_match :
    let_exp -> f:(x:Bound_for_let.t -> e1:core_exp -> e2:core_exp -> 'a) -> 'a

  val pattern_match_pair :
    t -> t -> (Bound_for_let.t -> core_exp -> core_exp -> 'a) ->
    (Bound_codelike.t -> Bound_codelike.t -> core_exp -> core_exp -> 'a) ->
    ('a, Pattern_match_pair_error.t) Result.t
end

module Core_lambda : sig
  type t = lambda_exp

  val create : Bound_for_lambda.t -> T0.t -> t

  val pattern_match :
    t -> f:(Bound_for_lambda.t -> T0.t -> 'a) -> 'a

  val pattern_match_pair:
    t -> t ->
    f:(return_continuation:Continuation.t ->
       exn_continuation:Continuation.t ->
       Bound_parameters.t -> core_exp -> core_exp -> 'a) -> 'a
end

val print : Format.formatter -> core_exp -> unit
val print_static_pattern : Format.formatter -> Bound_codelike.Pattern.t -> unit
val print_prim : Format.formatter -> primitive -> unit
val print_bound_pattern : Format.formatter -> Bound_for_let.t -> unit

val apply_renaming : core_exp -> Renaming.t -> core_exp

val core_fmap : ('a -> base_exp -> core_exp) -> 'a -> core_exp -> core_exp

(* Fixpoint functions for core expessions *)
val let_fix : (core_exp -> core_exp) -> let_exp -> core_exp
val apply_fix : (core_exp -> core_exp) -> apply_exp -> core_exp
val apply_cont_fix : (core_exp -> core_exp) -> apply_cont_exp -> core_exp
val lambda_fix : (core_exp -> core_exp) -> lambda_exp -> core_exp
val switch_fix : (core_exp -> core_exp) -> switch_exp -> core_exp

val base_exp_fix :
  (core_exp -> core_exp) ->
  ('a -> base_exp -> core_exp) ->
  'a -> base_exp -> core_exp
val set_of_closures_fix :
  (core_exp -> core_exp) ->
  set_of_closures -> set_of_closures
val prim_fix : (core_exp -> core_exp) -> primitive -> core_exp

val base_exp_contained : base_exp -> base_exp -> bool
