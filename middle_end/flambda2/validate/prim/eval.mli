module P = Flambda_primitive

type primitive =
  | Simple of Simple.t
  | Nullary of P.nullary_primitive
  | Unary of P.unary_primitive
  | Binary of P.binary_primitive * primitive * primitive
  | Ternary of P.ternary_primitive * primitive * primitive * primitive
  | Variadic of P.variadic_primitive * primitive list

val eval_primitive : primitive -> primitive
