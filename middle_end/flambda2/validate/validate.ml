type core_exp = bool

type eq = bool

let core_eq _e1 _e2 = true

let flambda_unit_to_core _e = true

let simplify_result_to_core _e = true

let validate src tgt =
  let src_core = flambda_unit_to_core src in
  let tgt_core = simplify_result_to_core tgt in
  core_eq src_core tgt_core
