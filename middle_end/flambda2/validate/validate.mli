(* Simple validator for Flambda2

   This is the interface for a simple Flambda2 validator, which performs basic
   semantic equivalence between terms. Given the simplifying pass (after CPS
   translation), this validator does the following:


   [Flambda_unit.t]   ------- Simplify.run --------> [simplify_result]
          |                                                 |
          |                                                 |
     β - reduce                                          β - reduce
          |                                                 |
          |                                                 |
          ↓                                                 ↓
  [Flambda_core.t]            ≅[validate]            [Flambda_core.t]

   i.e. the validate function in this module performs the equivalence check
   between the source and target of the flambda2 simplification.

   To use this validator, use the [-validate] flag.

   N.B. Note the difference between this validator and the comparison check
   function available through [-cfg-equivalence-check].
   The CFG equivalence checker takes as assumption that the output of the
   simplifier has not changed and shows a syntactic equality up to
   alpha-equivalence. *)

(* module Validate : sig
 *   type t = bool (* FIXME *)
 * end *)

val validate :
  Flambda_unit.t -> Flambda_unit.t -> bool
