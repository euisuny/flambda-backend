open! Flambda2_core

let debug = ref true

let unequal (e1 : core_exp) (e2 : core_exp) =
  if !debug then
    Format.fprintf Format.std_formatter "Unequal:@ %a <>@ %a@."
      print e1
      print e2
  else ();
  false

(** Simple program context **)
(* LATER: Same structure used as [compare/compare.ml],
   might be useful to refactor the structure out of the file *)
module Env = struct
  type t =
    { mutable symbols : Symbol.t Symbol.Map.t;
      mutable code_ids : Code_id.t Code_id.Map.t;
      mutable slots : Slot.t Slot.Lmap.t;
      mutable slots_rev : Slot.t Slot.Lmap.t;
    }

  let create () =
    { symbols = Symbol.Map.empty;
      code_ids = Code_id.Map.empty;
      slots = Slot.Lmap.empty;
      slots_rev = Slot.Lmap.empty; }

  let add_symbol t symbol1 symbol2 =
    t.symbols <- Symbol.Map.add symbol1 symbol2 t.symbols

  let add_code_id t code_id1 code_id2 =
    t.code_ids <- Code_id.Map.add code_id1 code_id2 t.code_ids

  let add_slot t slot1 slot2 =
    t.slots
      <- Slot.Lmap.add slot1 slot2 t.slots;
    t.slots_rev
      <- Slot.Lmap.add slot2 slot1 t.slots_rev

  let find_symbol t sym = Symbol.Map.find_opt sym t.symbols

  let find_slot t slot =
    Slot.Lmap.find_opt slot t.slots

  let find_slot_rev t slot =
    Slot.Lmap.find_opt slot t.slots_rev
end

(* Used for unification of environments while comparing function and value slots in
  [set_of_closures]. This is necessary because function and value slots do not have
  an explicit binding site. *)
let subst_symbol (env : Env.t) symbol =
  Env.find_symbol env symbol |> Option.value ~default:symbol

let subst_slot (env : Env.t) slot =
  Env.find_slot env slot |> Option.value ~default:slot

(** Equality between two programs given a context **)
(* For now, following a naive alpha-equivalence equality from [compare/compare]
    (without the discriminant) *)

(* The most naive equality type, a boolean *)
type eq = bool

let eq_string = string_of_bool

let equiv_symbols env sym1 sym2 : eq =
  let sym1 = subst_symbol env sym1 in
  Symbol.equal sym1 sym2

let equiv_names env name1 name2 : eq =
  let result =
    Name.pattern_match name1
      ~var:(fun var1 ->
        Name.pattern_match name2
          ~var:(fun var2 -> Variable.equal var1 var2)
          ~symbol:(fun _ -> false))
      ~symbol:(fun symbol1 ->
        Name.pattern_match name2
          ~var:(fun _ ->
            unequal
              (Named (Base (Simple (Simple.name name1))))
              (Named (Base (Simple (Simple.name name2)))))
          ~symbol:(fun symbol2 -> equiv_symbols env symbol1 symbol2))
  in
  if result then result
  else
    (Format.fprintf Format.std_formatter "@.%a <> %a@."
      Name.print name1
      Name.print name2;
     false)

let equiv_slots env slot1 slot2 : eq =
  let _ = subst_slot env slot1 in
  match Env.find_slot env slot1 with
  | Some slot ->
    Slot.equal slot slot2
  | None ->
      match Env.find_slot_rev env slot2 with
      | Some _ ->
        unequal
          (Named (Base (Slot (Variable.create "", slot1))))
          (Named (Base (Slot (Variable.create "", slot2))))
      | None -> Env.add_slot env slot1 slot2;
        unequal
          (Named (Base (Slot (Variable.create "", slot1))))
          (Named (Base (Slot (Variable.create "", slot2))))

let zip_fold l1 l2 ~f ~acc =
  List.combine l1 l2 |> List.fold_left f acc

let rec equiv (env:Env.t) e1 e2 : eq =
  match e1, e2 with
  | Named (Closure_exp (_, slot1, {function_decls;_})), Lambda _ ->
    let e1 = Slot.Lmap.find slot1 function_decls in
    equiv env e1 e2
  | Lambda _, Named (Closure_exp (_, slot1, {function_decls;_}))  ->
    let e2 = Slot.Lmap.find slot1 function_decls in
    equiv env e1 e2
  | Named v1, Named v2 -> equiv_named env v1 v2
  | Let e1, Let e2 -> equiv_let env e1 e2
  | Apply e1, Apply e2 -> equiv_apply env e1 e2
  | Apply_cont e1, Apply_cont e2 -> equiv_apply_cont env e1 e2
  | Lambda e1, Lambda e2 -> equiv_lambda env e1 e2
  | Switch e1, Switch e2 -> equiv_switch env e1 e2
  | Invalid _, Invalid _ -> true
  | (Named (Base _ | Prim _ | Closure_exp _ | Set_of_closures _
           | Static_consts _ | Rec_info _) | Let _ | Apply _ |
     Apply_cont _ | Switch _ | Invalid _ | Lambda _), _ ->
    unequal e1 e2

(* [let_exp] *)
and equiv_let env e1 e2 : eq =
  Core_let.pattern_match_pair e1 e2
    (fun _bound let_bound1 let_bound2 ->
       equiv env let_bound1 let_bound2 && equiv env e1.exp_body e2.exp_body)
    (fun bound1 bound2 let_bound1 let_bound2 ->
         equiv_let_symbol_exps env
           (bound1, e1.exp_body, let_bound1)
           (bound2, e2.exp_body, let_bound2))
  |> function | Ok comp -> comp | Error _ ->
    unequal (Let e1) (Let e2)

and equiv_let_symbol_exps env
      (static1, const1, body1) (static2, const2, body2) : eq =
  equiv_bound_static env static1 static2 &&
  equiv env const1 const2 &&
  equiv env body1 body2

and equiv_static_consts env
      (const1 : Flambda2_core.static_const)
      (const2 : Flambda2_core.static_const) : eq =
  match const1, const2 with
  | Block (tag1, mut1, fields1), Block (tag2, mut2, fields2) ->
    equiv_block env (tag1, mut1, fields1) (tag2, mut2, fields2)
  (* IY: Is it fine to treat all the other static constants uniformly? *)
  | ((Block _) |
      (Boxed_float _) |
      (Boxed_int32 _) |
      (Boxed_int64 _) |
      (Boxed_nativeint _) |
      (Immutable_float_block _) |
      (Immutable_float_array _) |
      (Immutable_value_array _) |
      Empty_array |
      (Mutable_string _)|
      (Immutable_string _) ), _ -> compare const1 const2 = 0

and equiv_block env (tag1, mut1, fields1) (tag2, mut2, fields2) =
  Tag.Scannable.equal tag1 tag2 &&
  Mutability.compare mut1 mut2 = 0 &&
  (List.combine fields1 fields2 |>
   List.fold_left (fun x (e1, e2) -> x && equiv env e1 e2)
     true)

and equiv_bound_static env static1 static2 : eq =
  let static1 = Bound_codelike.to_list static1 in
  let static2 = Bound_codelike.to_list static2 in
  List.combine static1 static2 |>
  List.fold_left (fun x (e1, e2) -> x && equiv_pattern env e1 e2) true

(* Compare equal patterns and add variables to environment *)
and equiv_pattern env
      (pat1 : Bound_codelike.Pattern.t) (pat2 : Bound_codelike.Pattern.t) : eq =
  match pat1, pat2 with
  | Code id1, Code id2 ->
    Env.add_code_id env id1 id2; true
  | Block_like sym1, Block_like sym2 ->
    Env.add_symbol env sym1 sym2; true
  | Set_of_closures clo1, Set_of_closures clo2 ->
    equiv_simple env
      (Simple.var (Bound_var.var clo1)) (Simple.var (Bound_var.var clo2))
  | (Code _ | Block_like _ | Set_of_closures _), _ -> false

and equiv_set_of_closures env
  (set1 : set_of_closures) (set2 : set_of_closures) : eq =
  (* Unify value and function slots *)
  (* Comparing value slots *)
  (* let slots_by_value set =
   *   Slot.Lmap.bindings (set.slots)
   *   |> List.map (fun (var, value) -> value, var)
   * in *)
  (* let compare (exp1, _var1) (exp2, _var2) =
   *   if equiv env exp1 exp2 then 0 else 1
   * in *)
  (* let slots_eq =
   *   zip_sort_fold (slots_by_value set1) (slots_by_value set2)
   *     ~compare
   *     ~f:(fun x ((_, var1), (_, var2)) ->
   *           x && equiv_slots env var1 var2)
   *     ~acc:true
   * in *)
  (* Comparing function slots *)
  let slots_and_fun_decls_by_code_id (set : set_of_closures)
      : (core_exp * (Slot.t * core_exp)) list =
    let map = set.function_decls in
    Slot.Lmap.bindings map
    |> List.map (fun (slot, code_id) ->
      code_id, (slot, code_id))
  in
  let slots_eq =
    zip_fold
      (slots_and_fun_decls_by_code_id set1)
      (slots_and_fun_decls_by_code_id set2)
      ~f:(fun acc ((_, (slot1, decl1)), (_, (slot2, decl2))) ->
        acc &&
        equiv_slots env slot1 slot2 &&
        equiv env decl1 decl2)
      ~acc: true
  in
  slots_eq

and equiv_base_exp env base_exp1 base_exp2 : eq =
  match base_exp1, base_exp2 with
  | Simple simple1, Simple simple2 ->
    equiv_simple env simple1 simple2
  | Slot (_, slot1), Slot (_, slot2) ->
    equiv_slots env slot1 slot2
  | (Simple _ | Slot (_, _)), _ -> false

(* N.B. ignore Phi slots assigned *)
and equiv_named env named1 named2 : eq =
  match named1, named2 with
  | Base base_exp1, Base base_exp2 ->
    equiv_base_exp env base_exp1 base_exp2
  | Prim prim1, Prim prim2 ->
    equiv_primitives env prim1 prim2
  | Closure_exp (_, slot1, set1), Closure_exp (_, slot2, set2) ->
    equiv_slots env slot1 slot2 &&
    equiv_set_of_closures env set1 set2
  | Set_of_closures set1, Set_of_closures set2 ->
    equiv_set_of_closures env set1 set2
  | Rec_info _, Rec_info _ -> true
  | Static_consts const1, Static_consts const2 ->
    (List.combine const1 const2 |>
     List.fold_left (fun x (e1, e2) -> x && equiv_static_consts env e1 e2) true)
  | (Base _ | Prim _ |
     Set_of_closures _ | Rec_info _ | Static_consts _ | Closure_exp _), _ ->
    unequal (Named named1) (Named named2)

and equiv_simple env simple1 simple2 : eq =
  Simple.pattern_match simple1
    ~name:(fun name1 ~coercion:_ ->
      Simple.pattern_match simple2
        ~name:(fun name2 ~coercion:_ -> equiv_names env name1 name2)
        ~const:(fun _ -> false))
    ~const:(fun const1 ->
      Simple.pattern_match simple2
        ~name:(fun _ ~coercion:_ -> false)
        ~const:(fun const2 -> Reg_width_const.equal const1 const2))

and equiv_primitives env prim1 prim2 : eq =
  match (prim1:primitive), (prim2:primitive) with
  | Unary (op1, arg1), Unary (op2, arg2) ->
    P.equal_unary_primitive op1 op2 &&
    equiv env arg1 arg2
  | Binary (op1, arg1_1, arg1_2), Binary (op2, arg2_1, arg2_2) ->
    P.equal_binary_primitive op1 op2 &&
    equiv env arg1_1 arg2_1 &&
    equiv env arg1_2 arg2_2
  | Ternary (op1, arg1_1, arg1_2, arg1_3),
    Ternary (op2, arg2_1, arg2_2, arg2_3) ->
    P.equal_ternary_primitive op1 op2 &&
    equiv env arg1_1 arg2_1 &&
    equiv env arg1_2 arg2_2 &&
    equiv env arg1_3 arg2_3
  | Variadic (op1, args1), Variadic (op2, args2) ->
    P.equal_variadic_primitive op1 op2 &&
    (List.combine args1 args2 |>
     List.fold_left (fun x (e1, e2) -> x && equiv env e1 e2) true)
  | Nullary (Invalid _), Nullary (Invalid _) -> true
  | Nullary (Optimised_out _), Nullary (Optimised_out _) -> true
  | Nullary (Probe_is_enabled _), Nullary (Probe_is_enabled _) -> true
  | Nullary Begin_region, Nullary Begin_region -> true
  | (Nullary (Invalid _) | Nullary (Optimised_out _ ) | Nullary (Probe_is_enabled _)
    | Nullary (Begin_region) | Nullary (Enter_inlined_apply _)
    | Unary _ | Binary _ | Ternary _ | Variadic _), _ ->
    false

(* [apply] *)
and equiv_apply env (e1 : apply_exp) (e2 : apply_exp) : eq =
  let equiv_conts =
    equiv env (e1.continuation) (e2.continuation) &&
    equiv env (e1.exn_continuation) (e2.exn_continuation) in
  let callee = equiv env (e1.callee) (e2.callee) in
  let args =
    zip_fold (e1.apply_args) (e2.apply_args)
      ~f:(fun x (e1, e2) -> x && equiv env e1 e2) ~acc:true in
  equiv_conts && callee && args

(* [apply_cont] *)
and equiv_apply_cont env
      ({k = k1; args = args1} : apply_cont_exp)
      ({k = k2; args = args2} : apply_cont_exp) : eq =
  equiv env k1 k2 &&
  zip_fold args1 args2 ~f:(fun x (e1, e2) -> x && equiv env e1 e2) ~acc:true

and equiv_lambda env (e1 : lambda_exp) (e2 : lambda_exp) : eq =
  Core_lambda.pattern_match_pair e1 e2
    ~f:(fun
         ~return_continuation:_ ~exn_continuation:_ _params e1 e2 ->
         equiv env e1 e2)

(* [switch] *)
and equiv_switch env
      ({scrutinee = scrutinee1; arms = arms1} : switch_exp)
      ({scrutinee = scrutinee2; arms = arms2} : switch_exp) : eq =
  equiv env scrutinee1 scrutinee2 &&
  Targetint_31_63.Map.equal (equiv env) arms1 arms2

let core_eq e1 e2 =
  try (equiv (Env.create ()) e1 e2) with
  Invalid_argument _ -> unequal e1 e2
