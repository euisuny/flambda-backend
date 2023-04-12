open! Flambda
open! Flambda2_core

(** The core language simplifies any bureaucratic redundancies, and alleviates
    syntactic restrictions of terms in the negative position (i.e.arguments).

    Note that the syntactic restrictions are a necessary part of the "Compiling-
    with- continuations" style optimization used in Flambda2; however this
    validator removes this restriction to check for term equality *)

(** [simple_to_core] is a value-lifting translation:

    [Simple.t] corresponds to a register-sized value.
    By using this translation, we can allow for more liberal β - reductions in
    while normalizing [core_exp] terms. **)

type substitutions

module Clo : sig
  type 'a t
  val find : Variable.t -> 'a t -> 'a
end

type clo = set_of_closures Clo.t

type code

type env = substitutions * clo * code

val create_env : env

val simple_to_core : Simple.t -> core_exp

val prim_to_core : Flambda_primitive.t -> primitive

(* The environment keeps track of the closures.

   Translation pass creates consistent phi-nodes for all lambda-like code bindings *)
val flambda_expr_to_core :
  Flambda.expr -> env -> core_exp * env

val flambda_unit_to_core : Flambda_unit.t -> core_exp * clo

val tagged_immediate_to_core : Targetint_31_63.t -> core_exp
