open! Flambda

(** Simplified core of [flambda2] terms **)
(* (1) Simple.t -> core_exp for [Apply*] expressions
   (2) Ignore [Num_occurrences] (which is used for making inlining decisions)
   (3) Ignored traps for now *)

type core_exp =
  | Var of Simple.t
  | Let of let_expr
  | Let_cont of let_cont_expr
  | Apply of apply_expr
  | Apply_cont of apply_cont_expr
  | Switch of switch_expr
  | Invalid of { message : string }

(** Let expressions [let x = e1 in e]

   [fun x -> e] = let_abst
   [e1] = body **)
and let_expr =
  { let_abst : (Bound_pattern.t, core_exp) Name_abstraction.t;
    body : Named.t; }

and let_cont_expr =
  (** Non-recursive case [let k x = e1 in e2]

     [fun x -> e1] = handler
     bound variable [k] = Bound_continuation.t
     [e2] = body (has bound variable [k] in scope) **)
  | Non_recursive of
    { handler : continuation_handler;
      body : (Bound_continuation.t, core_exp) Name_abstraction.t;}

  (** Recursive case, we have a set of (mutually recursive) continuations
     [let rec K x in e] where [K] is a map of continuations
     [x] is the set of invariant parameters
     bound variable [K] is in the scope of [e]

     [x] = invariant_params (Bound_parameters.t)
     [K] = continuation_map
     [e] = body **)
  | Recursive of
      (Bound_continuations.t, recursive_let_expr) Name_abstraction.t

and recursive_let_expr =
  { continuation_map :
      (Bound_parameters.t, continuation_handler_map) Name_abstraction.t;
    body : core_exp; }

and continuation_handler_map =
  continuation_handler Continuation.Map.t

and continuation_handler =
  (Bound_parameters.t, core_exp) Name_abstraction.t

and apply_expr =
  { callee: core_exp;
    continuation: Apply_expr.Result_continuation.t;
    exn_continuation: Continuation.t;
    args: core_exp list;
    call_kind: Call_kind.t; }

and apply_cont_expr =
  { k : Continuation.t;
    args : core_exp list }

and switch_expr =
  { scrutinee : core_exp;
    arms : core_exp Targetint_31_63.Map.t }

(** [Name_abstraction] setup for [core_exp]s **)
(** Nominal renaming for [core_exp] **)
let rec apply_renaming t renaming : core_exp =
  match t with
  | Var t -> Var (Simple.apply_renaming t renaming)
  | Let t -> Let (apply_renaming_let t renaming)
  | Let_cont t -> Let_cont (apply_renaming_let_cont t renaming)
  | Apply t -> Apply (apply_renaming_apply t renaming)
  | Apply_cont t -> Apply_cont (apply_renaming_apply_cont t renaming)
  | Switch t -> Switch (apply_renaming_switch t renaming)
  | Invalid t -> Invalid t

(* renaming for [Let] *)
and apply_renaming_let ({ let_abst; body } as t) renaming : let_expr =
  let let_abst' =
    Name_abstraction.apply_renaming
      (module Bound_pattern)
      let_abst renaming
      ~apply_renaming_to_term:apply_renaming
  in
  let defining_expr' = Named.apply_renaming body renaming in
  { let_abst = let_abst'; body = defining_expr' }

(* renaming for [Let_cont] *)
and apply_renaming_let_cont t renaming : let_cont_expr =
  match t with
  | Non_recursive { handler; body } ->
    let handler =
      apply_renaming_cont_handler handler renaming
    in
    let body =
      Name_abstraction.apply_renaming
        (module Bound_continuation)
        body renaming ~apply_renaming_to_term:apply_renaming
    in
    Non_recursive { handler = handler ; body = body }
  | Recursive t ->
    Recursive (Name_abstraction.apply_renaming
        (module Bound_continuations)
        t renaming ~apply_renaming_to_term:apply_renaming_recursive_let_expr)

and apply_renaming_recursive_let_expr ({continuation_map; body} as t) renaming
  : recursive_let_expr =
  let continuation_map =
    Name_abstraction.apply_renaming
      (module Bound_parameters)
      continuation_map renaming ~apply_renaming_to_term:apply_renaming_cont_map
  in
  { continuation_map = continuation_map ;
    body = apply_renaming body renaming }

and apply_renaming_cont_handler t renaming : continuation_handler =
  Name_abstraction.apply_renaming
    (module Bound_parameters)
    t renaming ~apply_renaming_to_term:apply_renaming

and apply_renaming_cont_map t renaming : continuation_handler_map =
  Continuation.Map.fold
    (fun k handler result ->
       let k = Renaming.apply_continuation renaming k in
       let handler = apply_renaming_cont_handler handler renaming in
       Continuation.Map.add k handler result) t Continuation.Map.empty

(* renaming for [Apply] *)
and apply_renaming_apply
      ({ callee; continuation; exn_continuation; args; call_kind} as t) renaming:
  apply_expr =
  let continuation =
    Apply_expr.Result_continuation.apply_renaming continuation renaming in
  let exn_continuation =
    Renaming.apply_continuation renaming exn_continuation in
  let callee = apply_renaming callee renaming in
  let args = List.map (fun x -> apply_renaming x renaming) args in
  let call_kind = Call_kind.apply_renaming call_kind renaming in
  { callee = callee; continuation = continuation;
    exn_continuation = exn_continuation; args = args; call_kind = call_kind }

(* renaming for [Apply_cont] *)
and apply_renaming_apply_cont ({k; args} as t) renaming : apply_cont_expr =
  let k = Renaming.apply_continuation renaming k in
  let args = List.map (fun x -> apply_renaming x renaming) args in
  { k = k; args = args }

(* renaming for [Switch] *)
and apply_renaming_switch ({scrutinee; arms} as t) renaming : switch_expr =
  let scrutinee = apply_renaming scrutinee renaming in
  let arms = Targetint_31_63.Map.map (fun x -> apply_renaming x renaming) arms in
  { scrutinee = scrutinee; arms = arms }

(** [ids_for_export] is the set of bound variables for a given expression **)
let rec ids_for_export (t:core_exp) =
  match t with
  | Var t -> Ids_for_export.from_simple t
  | Let t -> ids_for_export_let t
  | Let_cont t -> ids_for_export_let_cont t
  | Apply t -> ids_for_export_apply t
  | Apply_cont t -> ids_for_export_apply_cont t
  | Switch t -> ids_for_export_switch t
  | Invalid t -> Ids_for_export.empty

(* ids for [Let_expr] *)
and ids_for_export_let { let_abst; body } =
  let body_ids = Named.ids_for_export body in
  let let_abst_ids =
    Name_abstraction.ids_for_export
      (module Bound_pattern)
      let_abst ~ids_for_export_of_term:ids_for_export
  in
  Ids_for_export.union body_ids let_abst_ids

(* ids for [Let_cont] *)
and ids_for_export_let_cont (t : let_cont_expr) =
  match t with
  | Non_recursive { handler; body } ->
    let handler_ids = ids_for_export_cont_handler handler in
    let body_ids =
      Name_abstraction.ids_for_export
        (module Bound_continuation)
        body ~ids_for_export_of_term:ids_for_export in
    Ids_for_export.union handler_ids body_ids
  | Recursive t ->
    Name_abstraction.ids_for_export
      (module Bound_continuations)
      t ~ids_for_export_of_term:ids_for_export_recursive_let_expr

and ids_for_export_recursive_let_expr ({continuation_map; body} as t : recursive_let_expr) =
  let cont_map_ids =
    Name_abstraction.ids_for_export
      (module Bound_parameters)
      continuation_map ~ids_for_export_of_term:ids_for_export_cont_map in
  let body_ids = ids_for_export body in
  Ids_for_export.union cont_map_ids body_ids

and ids_for_export_cont_handler (t : continuation_handler) =
  Name_abstraction.ids_for_export
    (module Bound_parameters) t ~ids_for_export_of_term:ids_for_export

and ids_for_export_cont_map (t : continuation_handler_map) =
  Continuation.Map.fold
    (fun k handler ids ->
       Ids_for_export.union ids
         (Ids_for_export.add_continuation
            (ids_for_export_cont_handler handler)
            k))
    t Ids_for_export.empty

(* ids for [Apply] *)
and ids_for_export_apply
      { callee; continuation; exn_continuation; args; call_kind } =
  let callee_ids = ids_for_export callee in
  let callee_and_args_ids =
    List.fold_left
      (fun ids arg -> Ids_for_export.union ids (ids_for_export arg))
       callee_ids args in
  let result_continuation_ids =
    Apply_expr.Result_continuation.ids_for_export continuation in
  let exn_continuation_ids =
    Ids_for_export.add_continuation Ids_for_export.empty exn_continuation in
  let call_kind_ids = Call_kind.ids_for_export call_kind in
  (Ids_for_export.union
    (Ids_for_export.union callee_and_args_ids call_kind_ids)
    (Ids_for_export.union result_continuation_ids exn_continuation_ids))

(* ids for [Apply_cont] *)
and ids_for_export_apply_cont { k; args } =
  List.fold_left
    (fun ids arg -> Ids_for_export.union ids (ids_for_export arg))
    (Ids_for_export.add_continuation Ids_for_export.empty k)
    args

and ids_for_export_switch { scrutinee; arms } =
  let scrutinee_ids = ids_for_export scrutinee in
  Targetint_31_63.Map.fold
    (fun _discr action ids ->
        Ids_for_export.union ids (ids_for_export action))
    arms scrutinee_ids

(* Module definitions for [Name_abstraction]*)
module T0 = struct
  type t = core_exp
  let apply_renaming = apply_renaming
  let ids_for_export = ids_for_export
end

module ContMap = struct
  type t = continuation_handler_map
  let apply_renaming = apply_renaming_cont_map
  let ids_for_export = ids_for_export_cont_map
end

module RecursiveLetExpr = struct
  type t = recursive_let_expr
  let apply_renaming = apply_renaming_recursive_let_expr
  let ids_for_export = ids_for_export_recursive_let_expr
end

module Core_let = struct
  module A = Name_abstraction.Make (Bound_pattern) (T0)
  let create (bound_pattern : Bound_pattern.t) (defining_expr : named) body =
    (match defining_expr, bound_pattern with
    | Prim _, Singleton _
    | Simple _, Singleton _
    | Rec_info _, Singleton _
    | Set_of_closures _, Set_of_closures _ -> ()
    | _ , _ -> failwith "[Let.create] Mismatched bound pattern and defining expr");
    Let { let_abst = A.create bound_pattern body; body = defining_expr }

  (* Ignores distinction in binding variables/symbols *)
  let pattern_match_pair = A.pattern_match_pair
end

module Core_continuation_handler = struct
  module A = Name_abstraction.Make (Bound_parameters) (T0)
  let create = A.create
  let pattern_match_pair = A.pattern_match_pair
end

module Core_letrec_body = struct
  module A = Name_abstraction.Make (Bound_continuation) (T0)
  let create = A.create
  let pattern_match_pair = A.pattern_match_pair
end

module Core_continuation_map = struct
  module A = Name_abstraction.Make (Bound_parameters) (ContMap)
  let create = A.create
  let pattern_match_pair = A.pattern_match_pair
end

module Core_recursive = struct
  module A = Name_abstraction.Make (Bound_continuations) (RecursiveLetExpr)
  let create = A.create
  let pattern_match_pair = A.pattern_match_pair
end

(** Translation from flambda2 terms to simplified core language **)
let simple_to_core (v : Simple.t) : core_exp = Var v

let rec flambda_expr_to_core (e: expr) : core_exp =
  let e = Expr.descr e in
  match e with
  | Flambda.Let t -> let_to_core t
  | Flambda.Let_cont t -> let_cont_to_core t
  | Flambda.Apply t -> apply_to_core t
  | Flambda.Apply_cont t -> apply_cont_to_core t
  | Flambda.Switch t -> switch_to_core t
  | Flambda.Invalid { message = t } -> Invalid { message = t }

and let_to_core (e : Let_expr.t) : core_exp =
  let (var, body) = Let_expr.pattern_match e ~f:(fun var ~body -> (var, body)) in
  Core_let.create var (Let_expr.defining_expr e) (flambda_expr_to_core body)

and let_cont_to_core (e : Let_cont_expr.t) : core_exp =
  match e with
  | Non_recursive
      {handler = h; num_free_occurrences; is_applied_with_traps} ->
    let (contvar, scoped_body) =
      Non_recursive_let_cont_handler.pattern_match
        h ~f:(fun contvar ~body -> (contvar, body)) in
    Let_cont (Non_recursive {
      handler =
        Non_recursive_let_cont_handler.handler h |> cont_handler_to_core;
      body = flambda_expr_to_core scoped_body |>
        Core_letrec_body.create contvar;})

  | Recursive r ->
    let (bound, params, body, handler) = Recursive_let_cont_handlers.pattern_match_bound
      r ~f:(fun bound ~invariant_params ~body t -> (bound, invariant_params, body, t)) in
    Let_cont
      (Recursive (Core_recursive.create bound
        {continuation_map =
            Core_continuation_map.create params (cont_handlers_to_core handler);
         body = flambda_expr_to_core body;}))

and cont_handler_to_core (e : Continuation_handler.t) : continuation_handler =
  let (var, handler) =
    Continuation_handler.pattern_match e ~f:(fun var ~handler -> (var, handler)) in
  Core_continuation_handler.create var (flambda_expr_to_core handler)

and cont_handlers_to_core (e : Continuation_handlers.t) :
  continuation_handler Continuation.Map.t =
  let e : Continuation_handler.t Continuation.Map.t =
    Continuation_handlers.to_map e in
  Continuation.Map.map cont_handler_to_core e

and apply_to_core (e : Apply.t) : core_exp =
  Apply {
    callee = Apply_expr.callee e |> simple_to_core;
    continuation = Apply_expr.continuation e;
    exn_continuation = Apply_expr.exn_continuation e |>
                        Exn_continuation.exn_handler;
    args = Apply_expr.args e |> List.map simple_to_core;
    call_kind = Apply_expr.call_kind e;}

and apply_cont_to_core (e : Apply_cont.t) : core_exp =
  Apply_cont {
    k = Apply_cont_expr.continuation e;
    args = Apply_cont_expr.args e |> List.map simple_to_core;}

and switch_to_core (e : Switch.t) : core_exp =
  Switch {
    scrutinee = Switch_expr.scrutinee e |> simple_to_core;
    arms = Switch_expr.arms e |> Targetint_31_63.Map.map apply_cont_to_core;}

(* The most naive equality type, a boolean *)
type eq = bool

(** Simple program context **)
(* FIXME: Same structure used as [compare/compare.ml],
   might be useful to refactor the structure out of the file *)
module Env = struct
  type t =
    { mutable symbols : Symbol.t Symbol.Map.t;
      mutable code_ids : Code_id.t Code_id.Map.t;
      mutable function_slots : Function_slot.t Function_slot.Map.t;
      mutable function_slots_rev : Function_slot.t Function_slot.Map.t;
      mutable value_slots : Value_slot.t Value_slot.Map.t;
      mutable value_slots_rev : Value_slot.t Value_slot.Map.t
    }

  let create () =
    { symbols = Symbol.Map.empty;
      code_ids = Code_id.Map.empty;
      function_slots = Function_slot.Map.empty;
      function_slots_rev = Function_slot.Map.empty;
      value_slots = Value_slot.Map.empty;
      value_slots_rev = Value_slot.Map.empty }

  let add_symbol t symbol1 symbol2 =
    t.symbols <- Symbol.Map.add symbol1 symbol2 t.symbols

  let add_code_id t code_id1 code_id2 =
    t.code_ids <- Code_id.Map.add code_id1 code_id2 t.code_ids

  let add_function_slot t function_slot1 function_slot2 =
    t.function_slots
      <- Function_slot.Map.add function_slot1 function_slot2 t.function_slots;
    t.function_slots
      <- Function_slot.Map.add function_slot2 function_slot1
           t.function_slots_rev

  let add_value_slot t value_slot1 value_slot2 =
    t.value_slots <- Value_slot.Map.add value_slot1 value_slot2 t.value_slots;
    t.value_slots
      <- Value_slot.Map.add value_slot2 value_slot1 t.value_slots_rev

  let find_symbol t sym = Symbol.Map.find_opt sym t.symbols

  let find_code_id t code_id = Code_id.Map.find_opt code_id t.code_ids

  let find_function_slot t function_slot =
    Function_slot.Map.find_opt function_slot t.function_slots

  let find_function_slot_rev t function_slot =
    Function_slot.Map.find_opt function_slot t.function_slots_rev

  let find_value_slot t value_slot =
    Value_slot.Map.find_opt value_slot t.value_slots

  let find_value_slot_rev t value_slot =
    Value_slot.Map.find_opt value_slot t.value_slots_rev
end

let subst_symbol (env : Env.t) symbol =
  Env.find_symbol env symbol |> Option.value ~default:symbol

(** Equality between two programs given a context **)
(* For now, following a naive alpha-equivalence equality from [compare/compare]
    (without the discriminant) *)
let rec equiv (env:Env.t) e1 e2 : eq =
  match e1, e2 with
  | Let e1, Let e2 -> equiv_let env e1 e2
  | Let_cont _, Let_cont _ -> failwith "Unimplemented"
  | Apply _, Apply _ -> failwith "Unimplemented"
  | Apply_cont _, Apply_cont _ -> failwith "Unimplemented"
  | Switch _, Switch _ -> failwith "Unimplemented"
  | Invalid _, Invalid _ -> failwith "Unimplemented"

(* IY: Do we need to add special treatment for static vars? *)
and equiv_let env ({let_abst = let_abst1; body = body1} as e1)
                    ({let_abst = let_abst2; body = body2} as e2) : eq =
  equiv_named env body1 body2 &&
  Core_let.pattern_match_pair let_abst1 let_abst2
    ~f:(fun b t1 t2 -> equiv env t1 t2)

and equiv_named env named1 named2 : eq =
  match named1, named2 with
  | Simple simple1, Simple simple2 ->
    equiv_simple env simple1 simple2
  | Prim (prim1, dbg1), Prim (prim2, _) ->
    equiv_primitives env prim1 prim2
  | Set_of_closures set1, Set_of_closures set2 ->
    equiv_sets_of_closures env set1 set2
  | Rec_info rec_info_expr1, Rec_info rec_info_expr2 ->
    equiv_rec_info env rec_info_expr1 rec_info_expr2
  | Static_consts const1, Static_consts const2 ->
    equiv_static_consts env const1 const2
  | (Simple _ | Prim _ | Set_of_closures _ | Static_consts _ | Rec_info _), _ ->
    false

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

and equiv_names env name1 name2 : eq =
  Name.pattern_match name1
    ~var:(fun var1 ->
      Name.pattern_match name2
        ~var:(fun var2 -> Variable.equal var1 var2)
        ~symbol:(fun _ -> false))
    ~symbol:(fun symbol1 ->
      Name.pattern_match name2
        ~var:(fun _ -> false)
        ~symbol:(fun symbol2 -> equiv_symbols env symbol1 symbol2))

and equiv_symbols env sym1 sym2 : eq =
  let symbol1 = subst_symbol env sym1 in
  let symbol2 = subst_symbol env sym2 in
  Symbol.equal sym1 sym2

and equiv_primitives env prim1 prim2 : eq =
  failwith "Unimplemented"

and equiv_sets_of_closures env set1 set2 : eq =
  failwith "Unimplemented"

and equiv_rec_info env info1 info2 : eq =
  failwith "Unimplemented"

and equiv_static_consts env set1 set2 : eq =
  failwith "Unimplemented"

let core_eq = Env.create () |> equiv

(** Normalization *)
(* TODO *)
let rec normalize (e:core_exp) : core_exp =
  match e with
  | Var _ -> e
  | Let e -> failwith "Unimplemented"
  | Let_cont _ -> failwith "Unimplemented"
  | Apply _ -> failwith "Unimplemented"
  | Apply_cont _ -> failwith "Unimplemented"
  | Switch _ -> failwith "Unimplemented"
  | Invalid _ -> failwith "Unimplemented"

let simulation_relation src tgt =
  let {Simplify.unit = tgt; exported_offsets; cmx; all_code} = tgt in
  let src_core = Flambda_unit.body src |> flambda_expr_to_core in
  let tgt_core = Flambda_unit.body tgt |> flambda_expr_to_core in
  core_eq src_core tgt_core

(** Top-level validator *)
let validate ~cmx_loader ~round src =
  let tgt = Simplify.run ~cmx_loader ~round src in
  simulation_relation src tgt
