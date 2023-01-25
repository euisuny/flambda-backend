(* Simple validator for Flambda2

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
   alpha-equivalence. *)

type core_exp

type eq

val core_eq : core_exp -> core_exp -> eq

val flambda_expr_to_core : Flambda.expr -> core_exp

val simplify_result_to_core : Simplify.simplify_result -> core_exp

val normalize : core_exp -> core_exp

val validate : Flambda_unit.t -> Simplify.simplify_result -> eq
