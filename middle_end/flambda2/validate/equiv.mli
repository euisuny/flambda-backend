(** Alpha-equivalence checker **)

type eq = bool

val eq_string : eq -> string

val core_eq : Flambda2_core.core_exp -> Flambda2_core.core_exp -> eq
