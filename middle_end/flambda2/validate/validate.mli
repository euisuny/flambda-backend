(** Simple validator for Flambda2

   This is the interface for a simple Flambda2 validator, which performs basic
   semantic equivalence between terms. Given the simplifying pass (after CPS
   translation), this validator does the following:


      [Flambda_unit.t]   ------- Simplify.run --------> [simplify_result]
              |                                                 |
              |                                                 |
          translate                                         translate
    (flambda_expr_to_core)                          (simplify_result_to_core)
              |                                                 |
              |                                                 |
              ↓                                                 ↓
          [core_exp]                                        [core_exp]
              |                                                 |
              |                                                 |
          β - reduce                                        β - reduce
          (normalize)                                       (normalize)
              |                                                 |
              |                                                 |
              ↓                                                 ↓
        [core_exp]              ≅[validate]                [core_exp]

   i.e. the validate function in this module performs the equivalence check
   between the source and target of the flambda2 simplification.

   To use this validator, use the [-validate] flag.

   N.B. Note the difference between this validator and the comparison check
   function available through [-cfg-equivalence-check].
   The CFG equivalence checker takes as assumption that the output of the
   simplifier has not changed and shows a syntactic equality up to
   alpha-equivalence. **)

(** The core language simplifies any bureaucratic redundancies, and alleviates
   syntactic restrictions of terms in the negative position (i.e.arguments).

   Note that the syntactic restrictions are a necessary part of the "Compiling-
   with- continuations" style optimization used in Flambda2; however this
   validator removes this restriction to check for term equality *)
type core_exp

type eq

val core_eq : core_exp -> core_exp -> eq

(** [simple_to_core] is a value-lifting translation:

   [Simple.t] corresponds to a register-sized value.
   By using this translation, we can allow for more liberal β - reductions in
   while normalizing [core_exp] terms. **)
val simple_to_core : Simple.t -> core_exp

val flambda_expr_to_core : Flambda.expr -> core_exp

val normalize : core_exp -> core_exp

val simulation_relation : Flambda_unit.t -> Simplify.simplify_result -> eq

val validate : cmx_loader:Flambda_cmx.loader -> round:int -> Flambda_unit.t -> bool
