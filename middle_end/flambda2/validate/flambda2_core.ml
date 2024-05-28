module P = Flambda_primitive
let fprintf = Format.fprintf

(** Simplified core of [flambda2] terms **)
(* (1) Simple.t -> core_exp for [Apply*] expressions
   (2) Ignore [Num_occurrences] (which is used for making inlining decisions)
   (3) Ignored traps for now *)

module SlotMap = Map.Make (Function_slot)

(* This signature ensures absolutely that the insides of an expression cannot be
   accessed before any necessary delayed renaming has been applied. *)
module With_delayed_renaming : sig
  type 'descr t

  val create : 'descr -> 'descr t

  val apply_renaming : 'descr t -> Renaming.t -> 'descr t

  val descr :
    'descr t -> apply_renaming_descr:('descr -> Renaming.t -> 'descr) -> 'descr
end = struct
  type 'descr t =
    { mutable descr : 'descr;
      mutable delayed_renaming : Renaming.t
    }

  let create descr = { descr; delayed_renaming = Renaming.empty }

  let apply_renaming t renaming =
    let delayed_renaming =
      Renaming.compose ~second:renaming ~first:t.delayed_renaming
    in
    { t with delayed_renaming }

  let[@inline always] descr t ~apply_renaming_descr =
    if Renaming.is_empty t.delayed_renaming
    then t.descr
    else
      let descr = apply_renaming_descr t.descr t.delayed_renaming in
      t.descr <- descr;
      t.delayed_renaming <- Renaming.empty;
      descr
end

type core_exp = exp_descr With_delayed_renaming.t

and exp_descr =
  | Named of named
  | Let of let_expr
  | Let_cont of let_cont_expr
  | Apply of apply_expr
  | Apply_cont of apply_cont_expr
  | Lambda of lambda_expr (* A lambda for code expressions *)
  | Handler of continuation_handler
  | Switch of switch_expr
  | Invalid of { message : string }

and lambda_expr = (Bound_for_lambda.t, core_exp) Name_abstraction.t

(** Let expressions [let x = e1 in e2]

   [fun x -> e2] = let_abst
   [e1] = body **)
and let_expr =
  { let_abst : (Bound_for_let.t, core_exp) Name_abstraction.t;
    expr_body : core_exp; }

and literal =
  | Simple of Simple.t
  | Cont of Continuation.t
  | Res_cont of Apply_expr.Result_continuation.t
  | Slot of (Variable.t * slot)
  | Code_id of Code_id.t

and named =
  | Literal of literal
  | Prim of primitive
  | Closure_expr of (Variable.t * Function_slot.t * set_of_closures)
  | Set_of_closures of set_of_closures
  | Static_consts of static_const_group
  | Rec_info of Rec_info_expr.t

and slot =
  | Function_slot of Function_slot.t
  | Value_slot of Value_slot.t

and set_of_closures =
  { function_decls : function_declarations;
    value_slots : core_exp Value_slot.Map.t}

(* functions that are in-order *)
and function_declarations = core_exp SlotMap.t

and primitive =
  | Nullary of P.nullary_primitive
  | Unary of P.unary_primitive * core_exp
  | Binary of P.binary_primitive * core_exp * core_exp
  | Ternary of P.ternary_primitive * core_exp * core_exp * core_exp
  | Variadic of P.variadic_primitive * core_exp list

and function_params_and_body =
  { expr: (Bound_var.t, lambda_expr) Name_abstraction.t;
    anon: bool }

and static_const_or_code =
  | Code of function_params_and_body (* FIXME: Remove *)
  | Deleted_code (* FIXME: Remove *)
  | Static_const of static_const

and static_const =
  | Static_set_of_closures of set_of_closures (* FIXME: Remove *)
  | Block of Tag.Scannable.t * Mutability.t * core_exp list
  | Boxed_float of Numeric_types.Float_by_bit_pattern.t Or_variable.t
  | Boxed_int32 of Int32.t Or_variable.t
  | Boxed_int64 of Int64.t Or_variable.t
  | Boxed_nativeint of Targetint_32_64.t Or_variable.t
  | Immutable_float_block of
      Numeric_types.Float_by_bit_pattern.t Or_variable.t list
  | Immutable_float_array of
      Numeric_types.Float_by_bit_pattern.t Or_variable.t list
  | Immutable_value_array of Field_of_static_block.t list
  | Empty_array
  | Mutable_string of { initial_value : string }
  | Immutable_string of string

and static_const_group = static_const_or_code list

and let_cont_expr =
  (* Non-recursive case [e1 where k x = e2]

     [fun x -> e2] = handler
     bound variable [k] = Bound_continuation.t
     [e1] = body (has bound variable [k] in scope) *)
  { handler : continuation_handler;
    body : (Bound_continuation.t, core_exp) Name_abstraction.t;}

and continuation_handler_map =
  continuation_handler Continuation.Map.t

and continuation_handler =
  (Bound_parameters.t, core_exp) Name_abstraction.t

and apply_expr =
  { callee: core_exp;
    continuation: core_exp;
    exn_continuation: core_exp;
    region: core_exp;
    apply_args: core_exp list; }

and apply_cont_expr =
  { k : core_exp;
    args : core_exp list }

and switch_expr =
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

let simple_with_type (s : Simple.t) : simple_type =
  Simple.pattern_match' s
    ~var:(fun v ~coercion:_ -> Var v)
    ~symbol:(fun s ~coercion:_ -> Symbol s)
    ~const:(fun x ->
      match Int_ids.Const.descr x with
      | Naked_immediate i -> Naked_immediate i
      | Tagged_immediate i -> Tagged_immediate i
      | Naked_float i -> Naked_float i
      | Naked_int32 i -> Naked_int32 i
      | Naked_int64 i -> Naked_int64 i
      | Naked_nativeint i -> Naked_nativeint i)

let is_static_set_of_closures (e : static_const_or_code) =
  match e with
  | Static_const (Static_set_of_closures _) -> true
  | (Static_const
       (Block _ | Boxed_float _ | Boxed_int32 _ | Boxed_int64 _
       | Boxed_nativeint _ | Immutable_float_block _
       | Immutable_float_array _ | Immutable_value_array _
       | Empty_array | Mutable_string _ | Immutable_string _)
    | Code _ | Deleted_code) -> false

let is_code (e : static_const_or_code) =
  match e with
  | Code _ -> true
  | (Static_const _ | Deleted_code) -> false

(** Nominal renaming for [core_exp] **)
let rec descr expr =
  With_delayed_renaming.descr expr
    ~apply_renaming_descr:apply_renaming_expr_descr

and apply_renaming = With_delayed_renaming.apply_renaming

and apply_renaming_expr_descr t renaming =
  match t with
  | Named named ->
    let named' = apply_renaming_named named renaming in
    if named == named' then t else Named named'
  | Let let_expr ->
    let let_expr' = apply_renaming_let let_expr renaming in
    if let_expr == let_expr' then t else Let let_expr'
  | Let_cont let_cont_expr ->
    let let_cont_expr' = apply_renaming_let_cont let_cont_expr renaming in
    if let_cont_expr == let_cont_expr' then t else Let_cont let_cont_expr'
  | Apply apply_expr ->
    let apply_expr' = apply_renaming_apply apply_expr renaming in
    if apply_expr == apply_expr' then t else Apply apply_expr'
  | Apply_cont apply_cont_expr ->
    let apply_cont_expr' = apply_renaming_apply_cont apply_cont_expr renaming in
    if apply_cont_expr == apply_cont_expr' then t
    else Apply_cont apply_cont_expr'
  | Lambda lambda_expr ->
    let lambda_expr' = apply_renaming_lambda lambda_expr renaming in
    if lambda_expr == lambda_expr' then t else Lambda lambda_expr'
  | Handler continuation_handler ->
    let continuation_handler' =
      apply_renaming_handler continuation_handler renaming
    in
    if continuation_handler == continuation_handler' then t
    else Handler continuation_handler'
  | Switch switch_expr ->
    let switch_expr' = apply_renaming_switch switch_expr renaming in
    if switch_expr == switch_expr' then t else Switch switch_expr'
  | Invalid _ -> t

and apply_renaming_lambda t renaming : lambda_expr =
  Name_abstraction.apply_renaming (module Bound_for_lambda) t renaming
    ~apply_renaming_to_term:apply_renaming

and apply_renaming_handler t renaming =
  Name_abstraction.apply_renaming (module Bound_parameters) t renaming
    ~apply_renaming_to_term:apply_renaming

(* renaming for [Let] *)
and apply_renaming_let ({ let_abst; expr_body } as t) renaming : let_expr =
  let let_abst' =
    Name_abstraction.apply_renaming
      (module Bound_for_let)
      let_abst renaming
      ~apply_renaming_to_term:apply_renaming
  in
  let expr_body' = apply_renaming expr_body renaming in
  if let_abst == let_abst' && expr_body == expr_body'
  then t
  else { let_abst = let_abst'; expr_body = expr_body' }

and apply_renaming_literal t renaming : literal =
  match t with
  | Simple simple ->
    let simple' = Simple.apply_renaming simple renaming in
    if simple == simple' then t else Simple simple'
  | Cont cont ->
    let cont' = Renaming.apply_continuation renaming cont in
    if cont == cont' then t else Cont cont'
  | Res_cont (Return cont) ->
    let cont' = Renaming.apply_continuation renaming cont in
    if cont == cont' then t else Cont cont'
  | Res_cont Never_returns -> t
  | Slot (var, slot) ->
    let var' = Renaming.apply_variable renaming var in
    if var == var' then t else Slot (var', slot)
  | Code_id id ->
    let id' = Renaming.apply_code_id renaming id in
    if id == id' then t else Code_id id'

and apply_renaming_named t renaming : named =
  match t with
  | Literal literal ->
    let literal' = apply_renaming_literal literal renaming in
    if literal == literal' then t else Literal literal'
  | Prim prim ->
    let prim' = apply_renaming_prim prim renaming in
    if prim == prim' then t else Prim prim'
  | Closure_expr (var, slot, set) ->
    let var' = Renaming.apply_variable renaming var in
    let set' = apply_renaming_set_of_closures set renaming in
    if var == var' && set == set' then t else Closure_expr (var', slot, set')
  | Set_of_closures set ->
    let set' = apply_renaming_set_of_closures set renaming in
    if set == set' then t else Set_of_closures set'
  | Static_consts consts ->
    let consts' = apply_renaming_static_const_group consts renaming in
    if consts == consts' then t else Static_consts consts'
  | Rec_info info ->
    Rec_info (Rec_info_expr.apply_renaming info renaming)

and apply_renaming_function_declarations
      (funs : function_declarations) renaming =
  SlotMap.map (fun x -> apply_renaming x renaming) funs

and apply_renaming_set_of_closures
      ({ function_decls; value_slots } as t : set_of_closures)
      renaming : set_of_closures =
  let function_decls' =
    apply_renaming_function_declarations function_decls renaming
  in
  let changed = ref false in
  let value_slots' =
    Value_slot.Map.filter_map
      (fun var expr ->
         if Renaming.value_slot_is_used renaming var
         then (
          let simple' = apply_renaming expr renaming in
          if not (expr == simple') then changed := true;
          Some simple'
         )
         else (
           changed := true;
           None))
      value_slots
  in
  if function_decls == function_decls'
  && not !changed
  then t
  else
    { function_decls = function_decls';
      value_slots = value_slots'}

and apply_renaming_prim t renaming : primitive =
  match t with
  | Nullary (Invalid _ | Optimised_out _ | Probe_is_enabled _ | Begin_region
            | Enter_inlined_apply _) ->
    t
  | Unary (prim, arg) ->
    let prim' = P.apply_renaming_unary_primitive prim renaming in
    let arg' = apply_renaming arg renaming in
    if prim == prim' && arg == arg' then t else Unary (prim', arg')
  | Binary (prim, arg1, arg2) ->
    let prim' = P.apply_renaming_binary_primitive prim renaming in
    let arg1' = apply_renaming arg1 renaming in
    let arg2' = apply_renaming arg2 renaming in
    if prim == prim' && arg1 == arg1' && arg2 == arg2'
    then t
    else Binary (prim', arg1', arg2')
  | Ternary (prim, arg1, arg2, arg3) ->
    let prim' = P.apply_renaming_ternary_primitive prim renaming in
    let arg1' = apply_renaming arg1 renaming in
    let arg2' = apply_renaming arg2 renaming in
    let arg3' = apply_renaming arg3 renaming in
    if prim == prim' && arg1 == arg1' && arg2 == arg2' && arg3 == arg3'
    then t
    else Ternary (prim', arg1', arg2', arg3')
  | Variadic (prim, args) ->
    let prim' = P.apply_renaming_variadic_primitive prim renaming in
    let args' = List.map (fun x -> apply_renaming x renaming) args in
    if prim == prim' && args == args' then t else Variadic (prim', args')

and apply_renaming_static_const_group t renaming : static_const_group =
  Misc.Stdlib.List.map_sharing (fun static_const ->
    apply_renaming_static_const_or_code static_const renaming) t

and apply_renaming_static_const_or_code t renaming : static_const_or_code =
  match t with
  | Code code ->
    let code' = apply_renaming_function_params_and_body code renaming in
    if code == code' then t else Code code'
  | Deleted_code -> Deleted_code
  | Static_const const ->
    let const' = apply_renaming_static_const const renaming in
    if const == const' then t else Static_const const'

and apply_renaming_static_const t renaming =
  if Renaming.is_empty renaming
  then t
  else
    match t with
    | Static_set_of_closures set ->
      let set' = apply_renaming_set_of_closures set renaming in
      if set == set' then t else Static_set_of_closures set'
    | Block (tag, mut, fields) ->
      let fields' =
        Misc.Stdlib.List.map_sharing
          (fun field -> apply_renaming field renaming)
          fields
      in
      if fields' == fields then t else Block (tag, mut, fields')
    | Boxed_float or_var ->
      let or_var' = Or_variable.apply_renaming or_var renaming in
      if or_var == or_var' then t else Boxed_float or_var'
    | Boxed_int32 or_var ->
      let or_var' = Or_variable.apply_renaming or_var renaming in
      if or_var == or_var' then t else Boxed_int32 or_var'
    | Boxed_int64 or_var ->
      let or_var' = Or_variable.apply_renaming or_var renaming in
      if or_var == or_var' then t else Boxed_int64 or_var'
    | Boxed_nativeint or_var ->
      let or_var' = Or_variable.apply_renaming or_var renaming in
      if or_var == or_var' then t else Boxed_nativeint or_var'
    | Mutable_string { initial_value = _ } | Immutable_string _ -> t
    | Immutable_float_block fields ->
      let fields' =
        Misc.Stdlib.List.map_sharing
          (fun (field : _ Or_variable.t) : _ Or_variable.t ->
            match field with
            | Var (v, dbg) ->
              let v' = Renaming.apply_variable renaming v in
              if v == v' then field else Var (v', dbg)
            | Const _ -> field)
          fields
      in
      if fields' == fields then t else Immutable_float_block fields'
    | Immutable_float_array fields ->
      let fields' =
        Misc.Stdlib.List.map_sharing
          (fun (field : _ Or_variable.t) : _ Or_variable.t ->
            match field with
            | Var (v, dbg) ->
              let v' = Renaming.apply_variable renaming v in
              if v == v' then field else Var (v', dbg)
            | Const _ -> field)
          fields
      in
      if fields' == fields then t else Immutable_float_array fields'
    | Immutable_value_array fields ->
      let fields' =
        Misc.Stdlib.List.map_sharing
          (fun field -> Field_of_static_block.apply_renaming field renaming)
          fields
      in
      if fields' == fields then t else Immutable_value_array fields'
    | Empty_array -> Empty_array

and apply_renaming_function_params_and_body ({expr; anon} as t) renaming =
  let expr' =
    Name_abstraction.apply_renaming
      (module Bound_var) expr renaming
      ~apply_renaming_to_term:apply_renaming_lambda
  in
  if expr == expr' then t else { expr = expr'; anon = anon }


(* renaming for [Let_cont] *)
and apply_renaming_let_cont ({handler; body} as t) renaming : let_cont_expr =
  let handler' =
    apply_renaming_cont_handler handler renaming
  in
  let body' =
    Name_abstraction.apply_renaming
      (module Bound_continuation)
      body renaming ~apply_renaming_to_term:apply_renaming
  in
  if handler == handler' && body == body'
  then t
  else { handler = handler'; body = body' }

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
      ({ callee; continuation; exn_continuation; region; apply_args} as t)
      renaming : apply_expr =
  let continuation' = apply_renaming continuation renaming in
  let exn_continuation' = apply_renaming exn_continuation renaming in
  let callee' = apply_renaming callee renaming in
  let region' = apply_renaming region renaming in
  let apply_args' =
    Misc.Stdlib.List.map_sharing (fun x -> apply_renaming x renaming) apply_args
  in
  if    continuation == continuation' && exn_continuation == exn_continuation'
     && callee == callee' && region == region' && apply_args == apply_args'
  then t
  else
    { callee = callee';
      continuation = continuation';
      exn_continuation = exn_continuation';
      region = region';
      apply_args = apply_args';
    }

(* renaming for [Apply_cont] *)
and apply_renaming_apply_cont ({k; args} as t) renaming : apply_cont_expr =
  let k' = apply_renaming k renaming in
  let args' =
    Misc.Stdlib.List.map_sharing (fun x -> apply_renaming x renaming) args
  in
  if k == k' && args == args' then t else { k = k'; args = args' }

(* renaming for [Switch] *)
and apply_renaming_switch ({scrutinee; arms} as t) renaming : switch_expr =
  let scrutinee' = apply_renaming scrutinee renaming in
  let arms' =
    Targetint_31_63.Map.map_sharing (fun x -> apply_renaming x renaming) arms
  in
  if scrutinee == scrutinee' && arms == arms'
  then t
  else { scrutinee = scrutinee'; arms = arms' }

let must_be_named (e : core_exp) : named option =
  match descr e with
  | Named n -> Some n
  | (Let _ | Let_cont _ | Apply _ | Apply_cont _ | Lambda _ | Switch _
    | Handler _ | Invalid _) -> None

let must_be_literal (e : core_exp) : literal option =
  match must_be_named e with
  | Some (Literal n) -> Some n
  | (Some (Prim _ | Closure_expr _ | Set_of_closures _ | Static_consts _
          | Rec_info _)
    | None) -> None

let must_be_cont (e : core_exp) : Continuation.t option =
  match must_be_literal e with
  | Some (Cont k | Res_cont (Return k)) -> Some k
  | (Some (Res_cont Never_returns | Simple _ | Slot _ | Code_id _) | None) ->
    None

let must_be_prim (e : core_exp) : primitive option =
  match must_be_named e with
  | Some e ->
    (match e with
     | Prim e -> Some e
     | (Literal _ | Closure_expr _ | Set_of_closures _ | Static_consts _
       | Rec_info _) -> None)
  | None -> None

let must_be_simple (e : core_exp) : Simple.t option =
  match descr e with
  | Named (Literal (Simple s)) -> Some s
  | (Named (Literal (Cont _ | Res_cont _ | Slot _ | Code_id _)) |
    Named (Prim _ | Closure_expr _ | Set_of_closures _ |
            Static_consts _ | Rec_info _)
    | Let _ | Let_cont _ | Apply _ | Apply_cont _ | Lambda _ | Switch _
    | Handler _ | Invalid _) -> None

let must_be_lambda (e : core_exp) : lambda_expr option =
  match descr e with
  | Lambda e -> Some e
  | (Named _ | Let _ | Let_cont _ | Apply _ | Apply_cont _ | Switch _
    | Handler _ | Invalid _) -> None

let must_be_handler (e : core_exp) : continuation_handler option =
  match descr e with
  | Handler e -> Some e
  | (Named _ | Let _ | Let_cont _ | Apply _ | Apply_cont _ | Switch _
    | Lambda _ | Invalid _) -> None

let must_be_apply (e : core_exp) : apply_expr option =
  match descr e with
  | Apply e -> Some e
  | (Named _ | Let _ | Let_cont _ | Lambda _ | Apply_cont _ | Switch _
    | Handler _ | Invalid _) -> None

let must_be_static_consts (e : core_exp) : static_const_group option  =
  match must_be_named e with
  | Some (Static_consts g) -> Some g
  | Some (Literal _ | Prim _ | Closure_expr _ | Set_of_closures _
         | Rec_info _) | None -> None

let must_be_code (e : static_const_group) : function_params_and_body option =
  match e with
  | [Code code] -> Some code
  | ([] | (Code _ | Deleted_code | Static_const _)::_) -> None

let must_be_code (e : core_exp) : function_params_and_body option =
  match must_be_static_consts e with
  | Some e -> must_be_code e
  | None -> None

let must_be_tagged_immediate (e : named) : named option =
  match e with
  | Literal (Simple s) ->
    (match simple_with_type s with
    | Tagged_immediate _ -> Some (Literal (Simple s))
    | (Naked_immediate _ | Naked_float _ | Naked_int32 _ | Naked_int64 _
      | Naked_nativeint _ | Var _ | Symbol _) -> None)
  | Prim (Unary (Tag_immediate, arg)) -> must_be_named arg
  | Prim (Unary
            ((Untag_immediate | Duplicate_block _ | Duplicate_array _ | Is_int _
             | Get_tag | Array_length | Bigarray_length _ | String_length _
             | Int_as_pointer | Opaque_identity _ | Int_arith _ | Float_arith _
             | Num_conv _ | Boolean_not | Reinterpret_int64_as_float | Unbox_number _
             | Box_number _ | Project_function_slot _ | Project_value_slot _
             | Is_boxed_float | Is_flat_float_array | Begin_try_region | End_region
             | Obj_dup), _)) -> None
  | (Prim (Nullary _ | Binary  _ | Ternary _ | Variadic _) |
     Literal (Cont _ | Res_cont _ | Slot _ | Code_id _) | Closure_expr _
    | Set_of_closures _ | Static_consts _ | Rec_info _) -> None

let must_be_tagged_immediate (e : core_exp) : named option =
  match must_be_named e with
  | Some n -> must_be_tagged_immediate n
  | None -> None

let must_be_untagged_immediate (e : named) : named option =
  match e with
  | Literal (Simple s) ->
    begin match Simple.must_be_constant s with
    | Some c ->
      begin match[@warning "-4"] Reg_width_const.descr c with
      | Naked_immediate i ->
        Some (Literal (Simple (Simple.const_int i)))
      | Tagged_immediate _ | Naked_float _ | Naked_int32 _
      | Naked_int64 _ | Naked_nativeint _ ->
        (* CR ccasinghino: Could do something sensible here, probably, but without an
           example I'm unsure if we need to add the tag bit. *)
        None
      end
    | None -> None
    end
  | Prim (Unary (Untag_immediate, arg)) -> must_be_named arg
  | Prim (Unary
            ((Tag_immediate | Duplicate_block _ | Duplicate_array _ | Is_int _
             | Get_tag | Array_length | Bigarray_length _ | String_length _
             | Int_as_pointer | Opaque_identity _ | Int_arith _ | Float_arith _
             | Num_conv _ | Boolean_not | Reinterpret_int64_as_float | Unbox_number _
             | Box_number _ | Project_function_slot _ | Project_value_slot _
             | Is_boxed_float | Is_flat_float_array | Begin_try_region | End_region
             | Obj_dup), _)) -> None
  | (Prim (Nullary _ | Binary  _ | Ternary _ | Variadic _) |
     Literal (Cont _ | Res_cont _ | Slot _ | Code_id _) | Closure_expr _
    | Set_of_closures _ | Static_consts _ | Rec_info _) -> None

let must_be_untagged_immediate (e : core_exp) : named option =
  match must_be_named e with
  | Some n -> must_be_untagged_immediate n
  | None -> None

let must_be_simple_or_immediate (e : named) : Simple.t option =
  match e with
  | Literal (Simple s) -> Some s
  | Prim (Unary ((Tag_immediate | Untag_immediate), arg)) ->
    must_be_simple arg
  | Prim (Unary
             ((Duplicate_block _ | Duplicate_array _ | Is_int _ | Get_tag
              | Array_length | Bigarray_length _ | String_length _
              | Int_as_pointer | Opaque_identity _ | Int_arith _ | Float_arith _
              | Num_conv _ | Boolean_not | Reinterpret_int64_as_float | Unbox_number _
              | Box_number _ | Project_function_slot _ | Project_value_slot _
              | Is_boxed_float | Is_flat_float_array | Begin_try_region | End_region
              | Obj_dup), _)) -> None
  | (Prim (Nullary _ | Binary  _ | Ternary _ | Variadic _) |
     Literal (Cont _ | Res_cont _ | Slot _ | Code_id _) | Closure_expr _
    | Set_of_closures _ | Static_consts _ | Rec_info _) -> None

let must_be_simple_or_immediate (e : core_exp) : Simple.t option =
  match must_be_named e with
  | Some n -> must_be_simple_or_immediate n
  | None -> None

let must_be_string_length (e : named) : (Flambda_primitive.string_or_bytes * core_exp) option =
  match e with
  | Prim (Unary (String_length sb, arg)) -> Some (sb, arg)
  | Prim (Unary
            ((Tag_immediate | Untag_immediate | Duplicate_block _ | Duplicate_array _
             | Is_int _ | Get_tag | Array_length | Bigarray_length _
             | Int_as_pointer | Opaque_identity _ | Int_arith _ | Float_arith _
             | Num_conv _ | Boolean_not | Reinterpret_int64_as_float | Unbox_number _
             | Box_number _ | Project_function_slot _ | Project_value_slot _
             | Is_boxed_float | Is_flat_float_array | Begin_try_region | End_region
             | Obj_dup), _))
  | (Prim (Nullary _ | Binary  _ | Ternary _ | Variadic _) |
     Literal _ | Closure_expr _ | Set_of_closures _ | Static_consts _
    | Rec_info _) -> None

let must_be_string_length (e : core_exp) : (Flambda_primitive.string_or_bytes * core_exp) option =
  match must_be_named e with
  | Some n -> must_be_string_length n
  | None -> None


let must_be_slot (e : core_exp) : (Variable.t * slot) option =
  match must_be_literal e with
  | Some (Slot v) -> Some v
  | (Some (Simple _ | Cont _ | Res_cont _ | Code_id _) | None) -> None

let must_be_function_slot_expr (e : literal) :
  (Variable.t * Function_slot.t) option =
  match e with
  | Slot (phi, Function_slot slot) -> Some (phi, slot)
  | (Slot (_, Value_slot _) | Simple _ | Cont _ | Res_cont _ | Code_id _) ->
    None

let must_be_function_slot_expr (e : core_exp) :
  (Variable.t * Function_slot.t) option =
  match must_be_literal e with
  | Some n -> must_be_function_slot_expr n
  | None -> None

let must_be_set_of_closures (e : named) =
  match e with
  | Set_of_closures e -> Some e
  | (Literal _ | Prim _ | Closure_expr _ | Static_consts _ | Rec_info _) ->
    None

let must_be_set_of_closures (e : core_exp) =
  match must_be_named e with
  | Some n -> must_be_set_of_closures n
  | None -> None

let must_have_closure (e : named) : set_of_closures option =
  match e with
  | (Closure_expr (_, _, clo) | Set_of_closures clo) -> Some clo
  | (Literal _ | Prim _ | Static_consts _ | Rec_info _) -> None

let must_have_closure (e : core_exp) =
  match must_be_named e with
  | Some n -> must_have_closure n
  | None -> None

let must_be_static_set_of_closures (e : static_const) =
  match e with
  | Static_set_of_closures clo -> Some clo
  | (Block _ | Boxed_float _ | Boxed_int32 _ | Boxed_int64 _ | Boxed_nativeint _
    | Immutable_float_block _ | Immutable_float_array _
    | Immutable_value_array _ | Empty_array
    | Mutable_string _ | Immutable_string _) -> None

(** Sexp-ish simple pretty-printer for [core_exp]s.
  Ignores name_stamp, compilation_unit, and debug_info for simplicity. **)
let rec print ppf e =
  match descr e with
   | Named t ->
     fprintf ppf "@[<hov 1>%a@]"
     print_named t
   | Let t -> print_let ppf t
   | Let_cont t ->
     print_let_cont ppf t
   | Apply t ->
     fprintf ppf "@[<hov 1>apply %a@]"
     print_apply t
   | Lambda t ->
     fprintf ppf "@[<hov 1>λ@ %a@]"
     print_lambda t
   | Apply_cont t ->
     fprintf ppf "@[<hov 1>apply_cont %a@]"
       print_apply_cont t
   | Handler t ->
     fprintf ppf "@[<hov 1>%a@]"
       print_handler t
   | Switch t ->
     fprintf ppf "@[<hov 1>switch %a@]"
     print_switch t
   | Invalid { message } ->
     fprintf ppf "@[<hov 1>invalid %s@]" message

and print_lambda ppf t =
  Name_abstraction.pattern_match_for_printing
    (module Bound_for_lambda)
    t ~apply_renaming_to_term:apply_renaming
    ~f:(fun bound body ->
      fprintf ppf "%a ->@.   @[<hov 1>%a@]"
        Bound_for_lambda.print bound
        print body)

and print_let ppf ({let_abst; expr_body} : let_expr) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_for_let)
    let_abst ~apply_renaming_to_term:apply_renaming
    ~f:(fun bound body ->
      fprintf ppf
        "@[<v 0>@[<hov 1>let (%a) =@ %a in@]@;%a@]"
        print_bound_pattern bound
        print expr_body
        print body)

and print_bound_pattern ppf (t : Bound_for_let.t) =
  match t with
  | Singleton v ->
    fprintf ppf "singleton %a"
      Bound_var.print v
  | Static v ->
    fprintf ppf "static %a"
      print_bound_static v

and print_bound_static ppf (t : Bound_codelike.t) =
  Format.fprintf ppf "@[<hov 0>%a@]"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space print_static_pattern)
    (t |> Bound_codelike.to_list)

and print_static_pattern ppf (t : Bound_codelike.Pattern.t) =
  match t with
  | Code v ->
    fprintf ppf "%a" Code_id.print v
  | Set_of_closures v ->
    fprintf ppf "var %a" Bound_var.print v
  | Block_like v ->
    Format.fprintf ppf "(block_like %a)" Symbol.print v

and print_literal ppf (t : literal) =
  match t with
  | Simple simple ->
    fprintf ppf "simple %a"
      Simple.print simple
  | Cont k | Res_cont (Return k) ->
    fprintf ppf "%a"
      Continuation.print k
  | Res_cont (Never_returns) ->
    fprintf ppf "never_returns"
  | Slot (var, Function_slot slot) ->
    fprintf ppf "slot(%a, %a)"
      Variable.print var
      Function_slot.print slot
  | Slot (var, Value_slot slot) ->
    fprintf ppf "slot(%a, %a)"
      Variable.print var
      Value_slot.print slot
  | Code_id id ->
    fprintf ppf "%a"
      Code_id.print id

and print_named ppf (t : named) =
  match t with
  | Literal literal ->
    fprintf ppf "%a" print_literal literal
  | Prim prim -> print_prim ppf prim;
  | Closure_expr (var, slot, clo) ->
    fprintf ppf "@[<hov 3>clo(%a,@ %a,@. %a)@]"
      Variable.print var
      Function_slot.print slot
      (fun ppf clo ->
         print_named ppf (Set_of_closures clo)) clo
  | Set_of_closures clo ->
    fprintf ppf "set_of_closures@. @[<hov 2>%a@]"
    print_set_of_closures clo
  | Static_consts consts ->
    fprintf ppf "@[<hov 0>%a@]"
      print_static_const_group consts
  | Rec_info info ->
    fprintf ppf "rec_info %a"
      Rec_info_expr.print info

and print_set_of_closures ppf
      { function_decls;
        value_slots } =
  if Value_slot.Map.is_empty value_slots then
    Format.fprintf ppf "(%a)"
      print_function_declaration function_decls
  else
    Format.fprintf ppf "(%a@.)"
      print_function_declaration function_decls
      (* (Value_slot.Map.print print_value_slot) value_slots *)

(* and print_value_slot ppf value = *)
(*   Format.fprintf ppf "@[(%a)@]" print value *)

and print_function_declaration ppf in_order =
  Format.fprintf ppf "@[<hov 1>{%a}@]"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space
       (fun ppf (key, datum) ->
          Format.fprintf ppf "@[<hov 1>(%a@ %a)@]"
            Function_slot.print key print
            datum)) (in_order |> SlotMap.bindings)
  (* Format.fprintf ppf "(%a)"
   *   (SlotMap.print print) (in_order |> SlotMap.bindings) *)

and print_prim ppf (t : primitive) =
  match t with
  | Nullary prim ->
    fprintf ppf "@[<v 0>prim %a@]"
    print_nullary_prim prim
  | Unary (prim, arg) ->
    fprintf ppf "@[@[<v 0>prim %a@]@ (%a)@]"
     P.print_unary_primitive prim
     print arg
  | Binary (prim, arg1, arg2) ->
    fprintf ppf "@[@[<v 0>prim %a@]@ (%a,@ %a)@]"
    P.print_binary_primitive prim
    print arg1
    print arg2
  | Ternary (prim, arg1, arg2, arg3) ->
    fprintf ppf "@[@[<v 0>prim %a@]@ (%a@, %a@, %a)@]"
    P.print_ternary_primitive prim
    print arg1
    print arg2
    print arg3
  | Variadic (prim, args) ->
    fprintf ppf "@[@[<v 0>prim %a@]@ (%a)@]"
    P.print_variadic_primitive prim
    (Format.pp_print_list
       ~pp_sep:(fun ppf () ->
         Format.pp_print_custom_break ~fits:("", 0, "") ~breaks:(",", 0, "") ppf)
       print) args

and print_nullary_prim ppf (t : P.nullary_primitive) =
  match t with
  | Invalid _ ->
    fprintf ppf "Invalid"
  | Optimised_out _ ->
    fprintf ppf "Optimised_out"
  | Probe_is_enabled { name } ->
    fprintf ppf "(Probe_is_enabled@ %s)" name
  | Begin_region ->
    fprintf ppf "Begin_region"
  | Enter_inlined_apply _ ->
    fprintf ppf "Enter_inlined_apply"

and print_static_const_group ppf t =
  Format.pp_print_list ~pp_sep:Format.pp_print_space print_static_const_or_code ppf t

and print_static_const_or_code ppf t =
  match t with
  | Code code -> print_function_params_and_body ppf code
  | Deleted_code -> fprintf ppf "deleted_code"
  | Static_const const -> print_static_const ppf const

and print_static_const ppf (t : static_const) : unit =
  match t with
  | Static_set_of_closures set ->
    fprintf ppf "%a"
      print_set_of_closures set
  | Block (tag, mut, fields) ->
    fprintf ppf "(%sblock@ (tag %a)@ (%a))"
      (match mut with
        | Immutable -> "Immutable_"
        | Immutable_unique -> "Unique_"
        | Mutable -> "Mutable_")
      Tag.Scannable.print tag
      (Format.pp_print_list ~pp_sep:Format.pp_print_space
        print) fields
  | Boxed_float or_var ->
    fprintf ppf "(Boxed_float@ %a)"
      (Or_variable.print Numeric_types.Float_by_bit_pattern.print) or_var
  | Boxed_int32 or_var ->
    fprintf ppf "(Boxed_int32@ %a)"
      (Or_variable.print Numeric_types.Int32.print) or_var
  | Boxed_int64 or_var ->
    fprintf ppf "(Boxed_int64@ %a)"
      (Or_variable.print Numeric_types.Int64.print) or_var
  | Boxed_nativeint or_var ->
    fprintf ppf "(Boxed_nativeint@ %a)"
      (Or_variable.print Targetint_32_64.print) or_var
  | Immutable_float_block fields ->
    fprintf ppf "(Immutable_float_block@ %a)"
      (Format.pp_print_list
        ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "@; ")
        (Or_variable.print Numeric_types.Float_by_bit_pattern.print))
      fields
  | Immutable_float_array fields ->
    fprintf ppf "(Immutable_float_array@ [| %a |])"
      (Format.pp_print_list
        ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "@; ")
        (Or_variable.print Numeric_types.Float_by_bit_pattern.print))
      fields
  | Immutable_value_array fields ->
    fprintf ppf "(Immutable_value_array@ (%a))"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space
        Field_of_static_block.print) fields
  | Empty_array ->
    fprintf ppf "Empty_array"
  | Mutable_string { initial_value = s; } ->
    fprintf ppf "(Mutable_string@ %S)"
      s
  | Immutable_string s ->
    fprintf ppf "(Immutable_string@ %S)"
      s

and print_function_params_and_body ppf ({expr;anon=_}:function_params_and_body) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_var) expr
    ~apply_renaming_to_term:apply_renaming_lambda
    ~f:(fun t expr ->
      fprintf ppf "@[<hov 2>λ %a%a@]"
        Variable.print (Bound_var.var t)
        print_lambda expr)

and print_let_cont ppf ({handler; body} : let_cont_expr) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_continuation) body
    ~apply_renaming_to_term:apply_renaming
    ~f:(fun cont body ->
      Name_abstraction.pattern_match_for_printing
        (module Bound_parameters) handler
        ~apply_renaming_to_term:apply_renaming
        ~f:(fun k expr_body ->
          fprintf ppf
            "@[(%a)@; (@[<hov 1>where %a (%a) = @;%a)@]@]"
            print body
            print_cont cont
            print_params k
            print expr_body))

and print_params ppf (k : Bound_parameters.t) =
  Format.fprintf ppf "@[<hov 0>%a@]"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space print_param)
    (k |> Bound_parameters.to_list)

and print_param ppf (k : Bound_parameter.t) =
  fprintf ppf "%s" (Bound_parameter.var k |> Variable.name)

and print_cont ppf (k : Bound_continuation.t) =
  fprintf ppf "%a" Continuation.print k

and print_handler ppf (t : continuation_handler) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_parameters) t
    ~apply_renaming_to_term:apply_renaming
    ~f:(fun k expr_body ->
      fprintf ppf "@[<hov 1>(λ@ %a,@ %a)@]"
        print_params k
        print expr_body)

and print_apply ppf
      ({callee; continuation; exn_continuation; region; apply_args} : apply_expr) =
  fprintf ppf "(callee:@[<hov 2>%a@])@ (ret:%a)@ (exn:%a)@ (reg: %a)"
    print callee
    print continuation
    print exn_continuation
    print region;
  fprintf ppf " (args:";
  Format.pp_print_list ~pp_sep:Format.pp_print_space print ppf apply_args;
  fprintf ppf ")"

and print_apply_cont ppf ({k ; args} : apply_cont_expr) =
  fprintf ppf "(%a)@ "
    print k;
    fprintf ppf " (args:";
    Format.pp_print_list ~pp_sep:Format.pp_print_space print ppf args;
  fprintf ppf ")"

and print_switch ppf ({scrutinee; arms} : switch_expr) =
  fprintf ppf "(%a) with @ @[<v 0>" print scrutinee;
  Targetint_31_63.Map.iter (print_arm ppf) arms;
  fprintf ppf "@]"

and print_arm ppf key arm =
  fprintf ppf "@[<hov 2>@[<hov 0>| %a -> @]%a@]@ "
    Targetint_31_63.print key
    print arm

(** [ids_for_export] is the set of bound variables for a given expression **)
let rec ids_for_export (t : core_exp) =
  match descr t with
  | Named t -> ids_for_export_named t
  | Let t -> ids_for_export_let t
  | Let_cont t -> ids_for_export_let_cont t
  | Apply t -> ids_for_export_apply t
  | Apply_cont t -> ids_for_export_apply_cont t
  | Lambda t -> ids_for_export_lambda t
  | Handler t -> ids_for_export_handler t
  | Switch t -> ids_for_export_switch t
  | Invalid _ -> Ids_for_export.empty

(* ids for [Let_expr] *)
and ids_for_export_let { let_abst; expr_body } =
  let body_ids = ids_for_export expr_body in
  let let_abst_ids =
    Name_abstraction.ids_for_export
      (module Bound_for_let)
      let_abst ~ids_for_export_of_term:ids_for_export
  in
  Ids_for_export.union body_ids let_abst_ids

and ids_for_export_literal (t : literal) =
  match t with
  | Simple simple ->
    Ids_for_export.from_simple simple
  | Res_cont (Return k) | Cont k ->
    Ids_for_export.add_continuation Ids_for_export.empty k
  | Slot (var, _) ->
    Ids_for_export.singleton_variable var
  | Res_cont Never_returns ->
    Ids_for_export.empty
  | Code_id id ->
    Ids_for_export.add_code_id Ids_for_export.empty id

and ids_for_export_named (t : named) =
  match t with
  | Literal literal -> ids_for_export_literal literal
  | Closure_expr (var, _, set) ->
    Ids_for_export.add_variable
    (ids_for_export_set_of_closures set) var
  | Prim prim -> ids_for_export_prim prim
  | Set_of_closures set -> ids_for_export_set_of_closures set
  | Static_consts consts -> ids_for_export_static_const_group consts
  | Rec_info info -> Rec_info_expr.ids_for_export info

and ids_for_export_function_decls funs =
  SlotMap.fold
    (fun _function_slot fn_expr ids ->
       Ids_for_export.union (ids_for_export fn_expr) ids)
    funs Ids_for_export.empty

and ids_for_export_set_of_closures
      ({function_decls; value_slots} : set_of_closures) =
  let function_decls_ids =
    ids_for_export_function_decls function_decls
  in
  Value_slot.Map.fold
      (fun _value_slot value ids ->
          Ids_for_export.union ids (ids_for_export value))
      value_slots function_decls_ids

and ids_for_export_prim (t : primitive) =
  match[@warning "-4"] t with
  | Nullary
      (Invalid _ | Optimised_out _ | Probe_is_enabled _ | Begin_region
      | Enter_inlined_apply _) ->
    Ids_for_export.empty
  | Unary (End_region, _region) ->
    (* Following [simplify/flow/flow_acc.ml], uses of a region in [End_region] don't count
       as uses. *)
    (* CR: But is that actually OK for all uses of [ids_for_export], or should I have a
       separate free_vars function for this? *)
    Ids_for_export.empty
  | Unary (prim, arg) ->
    Ids_for_export.union
      (P.ids_for_export_unary_primitive prim)
      (ids_for_export arg)
  | Binary (prim, arg1, arg2) ->
    Ids_for_export.union
      (Ids_for_export.union
        (P.ids_for_export_binary_primitive prim)
        (ids_for_export arg1))
      (ids_for_export arg2)
  | Ternary (prim, arg1, arg2, arg3) ->
    Ids_for_export.union
      (Ids_for_export.union
        (Ids_for_export.union
          (P.ids_for_export_ternary_primitive prim)
          (ids_for_export arg1))
        (ids_for_export arg2))
      (ids_for_export arg3)
  | Variadic (prim, args) ->
    Ids_for_export.union
      (P.ids_for_export_variadic_primitive prim)
      (List.fold_left (fun acc x -> Ids_for_export.union (ids_for_export x) acc)
         Ids_for_export.empty args)

and ids_for_export_static_const_group t =
  List.map ids_for_export_static_const_or_code t |> Ids_for_export.union_list

and ids_for_export_static_const_or_code t =
  match t with
  | Code code ->
    ids_for_export_function_params_and_body code
  | Deleted_code -> Ids_for_export.empty
  | Static_const const -> ids_for_export_static_const const

and ids_for_export_fields fields =
  List.fold_left
    (fun ids field ->
       Ids_for_export.union ids (Field_of_static_block.ids_for_export field))
    Ids_for_export.empty fields

and ids_for_export_static_const t =
  match t with
  | Static_set_of_closures set -> ids_for_export_set_of_closures set
  | Block (_tag, _mut, fields) ->
    List.fold_left (fun acc x -> Ids_for_export.union (ids_for_export x) acc)
      Ids_for_export.empty fields
  | Boxed_float (Var (var, _dbg))
  | Boxed_int32 (Var (var, _dbg))
  | Boxed_int64 (Var (var, _dbg))
  | Boxed_nativeint (Var (var, _dbg)) ->
    Ids_for_export.add_variable Ids_for_export.empty var
  | Boxed_float (Const _)
  | Boxed_int32 (Const _)
  | Boxed_int64 (Const _)
  | Boxed_nativeint (Const _)
  | Mutable_string { initial_value = _ }
  | Immutable_string _ ->
    Ids_for_export.empty
  | Immutable_float_block fields ->
    List.fold_left
      (fun ids (field : _ Or_variable.t) ->
        match field with
        | Var (var, _dbg) -> Ids_for_export.add_variable ids var
        | Const _ -> ids)
      Ids_for_export.empty fields
  | Immutable_float_array fields ->
    List.fold_left
      (fun ids (field : _ Or_variable.t) ->
        match field with
        | Var (var, _dbg) -> Ids_for_export.add_variable ids var
        | Const _ -> ids)
      Ids_for_export.empty fields
  | Immutable_value_array fields -> ids_for_export_fields fields
  | Empty_array -> Ids_for_export.empty

and ids_for_export_function_params_and_body {expr; anon=_} =
  Name_abstraction.ids_for_export (module Bound_var) expr
    ~ids_for_export_of_term:ids_for_export_lambda

(* ids for [Let_cont] *)
and ids_for_export_let_cont ({handler; body} : let_cont_expr) =
  let handler_ids = ids_for_export_cont_handler handler in
  let body_ids =
    Name_abstraction.ids_for_export
      (module Bound_continuation)
      body ~ids_for_export_of_term:ids_for_export in
  Ids_for_export.union handler_ids body_ids

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
      { callee; continuation; exn_continuation; region; apply_args } =
  let callee_ids = ids_for_export callee in
  let callee_and_args_ids =
    List.fold_left
      (fun ids arg -> Ids_for_export.union ids (ids_for_export arg))
       callee_ids apply_args in
  let result_continuation_ids = ids_for_export continuation in
  let exn_continuation_ids = ids_for_export exn_continuation in
  let region_ids = ids_for_export region in
  (Ids_for_export.union
     region_ids
     (Ids_for_export.union
        callee_and_args_ids
        (Ids_for_export.union result_continuation_ids exn_continuation_ids)))

(* ids for [Apply_cont] *)
and ids_for_export_apply_cont { k; args } =
  let continuation_ids = ids_for_export k in
  List.fold_left
    (fun ids arg -> Ids_for_export.union ids (ids_for_export arg))
    continuation_ids
    args

and ids_for_export_handler t =
  Name_abstraction.ids_for_export
    (module Bound_parameters) t ~ids_for_export_of_term:ids_for_export

and ids_for_export_lambda t =
   Name_abstraction.ids_for_export
     (module Bound_for_lambda) t ~ids_for_export_of_term:ids_for_export

and ids_for_export_switch { scrutinee; arms } =
  let scrutinee_ids = ids_for_export scrutinee in
  Targetint_31_63.Map.fold
    (fun _discr action ids ->
        Ids_for_export.union ids (ids_for_export action))
    arms scrutinee_ids

(* Module definitions for [Name_abstraction]*)
module Expr = struct
  type t = core_exp
  type descr = exp_descr
  let apply_renaming = apply_renaming
  let ids_for_export = ids_for_export
  let descr = descr
  let create = With_delayed_renaming.create
  let create_named named = create (Named named)
  let create_let let_expr = create (Let let_expr)
  let create_let_cont let_cont = create (Let_cont let_cont)
  let create_apply apply = create (Apply apply)
  let create_apply_cont apply_cont = create (Apply_cont apply_cont)
  let create_lambda lambda = create (Lambda lambda)
  let create_handler handler = create (Handler handler)
  let create_switch switch = create (Switch switch)
  let create_invalid msg = create (Invalid {message = msg})
end

module ContMap = struct
  type t = continuation_handler_map
  let apply_renaming = apply_renaming_cont_map
  let ids_for_export = ids_for_export_cont_map
end

module Core_let = struct
  module A = Name_abstraction.Make (Bound_for_let) (Expr)
  type t = let_expr
  let create ~(x : Bound_for_let.t) ~(e1 : core_exp) ~(e2 : core_exp)  =
    Expr.create_let { let_abst = A.create x e2; expr_body = e1 }

  module Pattern_match_pair_error = struct
    type t = Mismatched_let_bindings
  end

  let pattern_match t ~(f : x:Bound_for_let.t -> e1:core_exp -> e2:core_exp -> 'a) : 'a =
    let open A in
    let<> x, e2 = t.let_abst in
    f ~x ~e1:t.expr_body ~e2

  (* Treat "dynamic binding" (statically scoped binding under lambda abstraction)
     and "static binding" (globally scoped mapping of statics) differently *)
  let pattern_match_pair
        ({let_abst = let_abst1; expr_body = _})
        ({let_abst = let_abst2; expr_body = _})
        (dynamic : Bound_for_let.t -> core_exp -> core_exp -> 'a)
        (static : Bound_codelike.t -> Bound_codelike.t -> core_exp -> core_exp -> 'a):
    ('a, Pattern_match_pair_error.t) Result.t =
    A.pattern_match let_abst1 ~f:(fun let_bound1 expr_body1 ->
      A.pattern_match let_abst2 ~f:(fun let_bound2 expr_body2 ->
        let dynamic_case () =
          let ans = A.pattern_match_pair let_abst1 let_abst2 ~f:dynamic
          in Ok ans
        in
        match let_bound1, let_bound2 with
        | Bound_for_let.Singleton _, Bound_for_let.Singleton _ -> dynamic_case ()
        | Static bound_static1, Static bound_static2 ->
          let patterns1 = bound_static1 |> Bound_codelike.to_list in
          let patterns2 = bound_static2 |> Bound_codelike.to_list in
          if List.compare_lengths patterns1 patterns2 = 0
          then
            let ans = static bound_static1 bound_static2 expr_body1 expr_body2 in
            Ok ans
          else Error Pattern_match_pair_error.Mismatched_let_bindings
        | (Singleton _ | Static _), _ ->
            Error Pattern_match_pair_error.Mismatched_let_bindings
      )
    )

  let let_var_free_in : Bound_for_let.t -> core_exp -> bool = fun var exp ->
    let free_vars = ids_for_export exp in
    Bound_for_let.fold_all_bound_names var
      ~init:false
      ~var:(fun acc v -> acc || Variable.Set.mem (Bound_var.var v) free_vars.variables)
      ~symbol:(fun acc v -> acc || Symbol.Set.mem v free_vars.symbols)
      ~code_id:(fun acc v -> acc || Code_id.Set.mem v free_vars.code_ids)
end

module Core_continuation_handler = struct
  module A = Name_abstraction.Make (Bound_parameters) (Expr)
  type t = continuation_handler
  let create = A.create
  let pattern_match (e : t) (f : Bound_parameters.t -> core_exp -> 'a) : 'a =
    A.pattern_match e ~f:(fun cont body -> f cont body)
  let pattern_match_pair (t1 : t) (t2 : t)
        (f : Bound_parameters.t -> core_exp -> core_exp -> 'a) : 'a =
    A.pattern_match_pair t1 t2 ~f:(fun params body1 body2 ->
        f params body1 body2)
end

module Core_letcont_body = struct
  module A = Name_abstraction.Make (Bound_continuation) (Expr)
  type t = (Bound_continuation.t, core_exp) Name_abstraction.t
  let create = A.create
  let pattern_match (e : t) (f : Bound_continuation.t -> core_exp -> 'a) : 'a =
    A.pattern_match e ~f:(fun cont body -> f cont body)
  let pattern_match_pair (t1 : t) (t2 : t)
        (f : Bound_continuation.t -> core_exp -> core_exp -> 'a) : 'a =
    A.pattern_match_pair t1 t2 ~f:(fun cont body1 body2 ->
      f cont body1 body2)
end

module Core_continuation_map = struct
  module A = Name_abstraction.Make (Bound_parameters) (ContMap)
  type t = (Bound_parameters.t, continuation_handler_map) Name_abstraction.t
  let create = A.create
  let pattern_match = A.pattern_match
end

module Core_letcont = struct
  type t = let_cont_expr

  let print = print_let_cont

  let create handler ~body =
    Expr.create_let_cont {handler; body}

end

module Core_lambda = struct
  module A = Name_abstraction.Make (Bound_for_lambda) (Expr)
  type t = lambda_expr

  let pattern_match x ~f =
    A.pattern_match x ~f:(fun b e -> f b e)

  let create = A.create

  let apply_renaming = apply_renaming_lambda
  let ids_for_export = ids_for_export_lambda

  let pattern_match_pair t1 t2 ~f =
    A.pattern_match_pair t1 t2
      ~f:(fun
           bound body1 body2
           -> f ~return_continuation:(bound.return_continuation)
                ~exn_continuation:(bound.exn_continuation)
                (bound.params) body1 body2)
end

module Core_function_params_and_body = struct
  module A = Name_abstraction.Make (Bound_var) (Core_lambda)
  type t = (Bound_var.t, Core_lambda.t) Name_abstraction.t

  let create = A.create

  let my_closure t = A.pattern_match t ~f:(fun param _ -> param)

  let lambda_expr t = A.pattern_match t ~f:(fun _ body -> body)

  let pattern_match = A.pattern_match

  let pattern_match_pair t1 t2 ~f =
    A.pattern_match_pair t1 t2
      ~f:(fun my_closure body1 body2 ->
        Core_lambda.pattern_match_pair body1 body2
          ~f:(fun ~return_continuation ~exn_continuation params body1 body2 ->
            f ~return_continuation ~exn_continuation params ~body1 ~body2
              ~my_closure))
end

let lambda_to_handler (e : lambda_expr) : continuation_handler =
  Core_lambda.pattern_match e
    ~f:(fun {return_continuation=_;exn_continuation=_;params;my_region=_} e ->
      Core_continuation_handler.create params e)

(* Fixpoint combinator for core expressions *)
let let_fix (f : core_exp -> core_exp) {let_abst; expr_body} =
  Core_let.pattern_match {let_abst; expr_body}
    ~f:(fun ~x ~e1 ~e2 ->
      (Core_let.create
        ~x
        ~e1:(f e1)
        ~e2:(f e2)))

let let_cont_fix (f : core_exp -> core_exp) ({handler; body} : let_cont_expr) =
  let handler =
    Core_continuation_handler.pattern_match handler
      (fun param exp ->
          Core_continuation_handler.create param (f exp))
  in
  let body =
    Core_letcont_body.pattern_match body
      (fun cont exp ->
          Core_letcont_body.create cont (f exp))
  in
  Core_letcont.create handler ~body

let handler_fix (f : core_exp -> core_exp)
      (handler : continuation_handler) =
  (Core_continuation_handler.pattern_match handler
      (fun param exp -> Core_continuation_handler.create param (f exp)))
  |> Expr.create_handler

let apply_fix (f : core_exp -> core_exp)
      ({callee; continuation; exn_continuation; region; apply_args} : apply_expr) =
  Apply
    {callee = f callee;
     continuation = f continuation;
     exn_continuation = f exn_continuation;
     region = f region;
     apply_args = List.map f apply_args;}
  |> With_delayed_renaming.create

let apply_cont_fix (f : core_exp -> core_exp)
      ({k; args} : apply_cont_expr) =
  Expr.create_apply_cont
    {k = f k;
     args = List.map f args}

let lambda_fix (f : core_exp -> core_exp) (e : lambda_expr) =
  Core_lambda.pattern_match e
    ~f:(fun b e ->
      (Core_lambda.create b (f e)))
  |> Expr.create_lambda

let switch_fix (f : core_exp -> core_exp)
      ({scrutinee; arms} : switch_expr) =
  {scrutinee = f scrutinee;
    arms = Targetint_31_63.Map.map f arms}
  |> Expr.create_switch

let set_of_closures_fix
      (fix : core_exp -> core_exp) {function_decls; value_slots} =
  let function_decls = SlotMap.map fix function_decls in
  let value_slots =
    Value_slot.Map.map fix value_slots
  in
  {function_decls; value_slots}

let static_const_fix (fix : core_exp -> core_exp) (e : static_const) =
  match e with
  | Static_set_of_closures clo ->
    let {function_decls; value_slots} = set_of_closures_fix fix clo in
    Static_set_of_closures {function_decls; value_slots}
  | Block (tag, mut, list) ->
    let list = List.map fix list in
    Block (tag, mut, list)
  | ( Boxed_float _ | Boxed_int32 _ | Boxed_int64 _ | Boxed_nativeint _
    | Immutable_float_block _ | Immutable_float_array _ | Immutable_value_array _
    | Empty_array | Mutable_string _ | Immutable_string _ ) -> e

let static_const_or_code_fix (fix : core_exp -> core_exp)
  (e : static_const_or_code) =
  (match e with
  | Code {expr; anon}->
    Code
      {expr =
         Core_function_params_and_body.pattern_match expr
         ~f:(fun
              params body ->
              Core_function_params_and_body.create
                params
                (Core_lambda.pattern_match body
                   ~f:(fun bound body ->
                     Core_lambda.create bound (fix body))));
       anon}
  | Deleted_code -> e
  | Static_const const ->
    Static_const (static_const_fix fix const))

let static_const_group_fix (fix : core_exp -> core_exp)
       (e : static_const_group) =
  Named (Static_consts (List.map (static_const_or_code_fix fix) e))
  |> With_delayed_renaming.create

let prim_fix (fix : core_exp -> core_exp) (e : primitive) =
  (match e with
  | Nullary _ -> Named (Prim e)
  | Unary (p, e) ->
    Named (Prim (Unary (p, fix e)))
  | Binary (p, e1, e2) ->
    Named (Prim (Binary (p, fix e1, fix e2)))
  | Ternary (p, e1, e2, e3) ->
    Named (Prim (Ternary (p, fix e1, fix e2, fix e3)))
  | Variadic (p, list) ->
    Named (Prim (Variadic (p, List.map fix list))))
  |> With_delayed_renaming.create

let named_fix (fix : core_exp -> core_exp)
      (f : 'a -> literal -> core_exp) arg (e : named) =
  match e with
  | Literal l -> f arg l
  | Prim e -> prim_fix fix e
  | Closure_expr (phi, slot, clo) ->
    let {function_decls; value_slots} = set_of_closures_fix fix clo in
    Named (Closure_expr (phi, slot, {function_decls; value_slots}))
    |> With_delayed_renaming.create
  | Set_of_closures clo ->
    let {function_decls; value_slots} = set_of_closures_fix fix clo in
    Named (Set_of_closures {function_decls; value_slots})
    |> With_delayed_renaming.create
  | Static_consts group ->
    static_const_group_fix fix group
  | Rec_info _ ->
    Named e
    |> With_delayed_renaming.create

(* LATER: Make this first order? *)
let rec core_fmap
  (f : 'a -> literal -> core_exp) (arg : 'a) (e : core_exp) : core_exp =
  match descr e with
  | Named e ->
    named_fix (core_fmap f arg) f arg e
  | Let e -> let_fix (core_fmap f arg) e
  | Let_cont e -> let_cont_fix (core_fmap f arg) e
  | Apply e -> apply_fix (core_fmap f arg) e
  | Apply_cont e -> apply_cont_fix (core_fmap f arg) e
  | Lambda e -> lambda_fix (core_fmap f arg) e
  | Handler e -> handler_fix (core_fmap f arg) e
  | Switch e -> switch_fix (core_fmap f arg) e
  | Invalid _ -> e

let literal_contained (literal1 : literal) (literal2 : literal) : bool =
  match literal1, literal2 with
  | Simple simple1, Simple simple2 ->
    Simple.same simple1 simple2
  | (Cont cont1, Cont cont2
    | Res_cont (Return cont1), Res_cont (Return cont2))
    -> Continuation.equal cont1 cont2
  | Simple simple, Slot (phi, _) ->
    Simple.same (Simple.var phi) simple
  | Slot (_, Function_slot slot1), Slot (_, Function_slot slot2) ->
    Function_slot.equal slot1 slot2
  | Slot (_, Value_slot slot1), Slot (_, Value_slot slot2) ->
    Value_slot.equal slot1 slot2
  | Res_cont Never_returns, Res_cont Never_returns -> true
  | Code_id code1, Code_id code2 ->
    Code_id.name code1 == Code_id.name code2
  | (Simple _ | Cont _ | Slot (_, (Function_slot _ | Value_slot _))
    | Res_cont (Never_returns | Return _) | Code_id _), _ -> false

module Ast_folder : sig
  (* Open recursion on core_exps, similar to the compiler's
     ast_mapper/ast_iterator.
  *)
  type 'a folder = {
    core_exp : 'a folder -> 'a -> core_exp -> 'a;
    named : 'a folder -> 'a -> named -> 'a;
    let_expr : 'a folder -> 'a -> let_expr -> 'a;
    let_cont_expr : 'a folder -> 'a -> let_cont_expr -> 'a;
    apply_expr : 'a folder -> 'a -> apply_expr -> 'a;
    apply_cont_expr : 'a folder -> 'a -> apply_cont_expr -> 'a;
    lambda_expr : 'a folder -> 'a -> lambda_expr -> 'a;
    continuation_handler : 'a folder -> 'a -> continuation_handler -> 'a;
    switch_expr : 'a folder -> 'a -> switch_expr -> 'a;
    literal : 'a folder -> 'a -> literal -> 'a;
    primitive : 'a folder -> 'a -> primitive -> 'a;
    variable : 'a folder -> 'a -> Variable.t -> 'a;
    set_of_closures : 'a folder -> 'a -> set_of_closures -> 'a;
    static_const_group : 'a folder -> 'a -> static_const_group -> 'a;
    static_const_or_code : 'a folder -> 'a -> static_const_or_code -> 'a;
    static_const : 'a folder -> 'a -> static_const -> 'a;
    symbol : 'a folder -> 'a -> Symbol.t -> 'a;
    function_params_and_body : 'a folder -> 'a -> function_params_and_body -> 'a;
    rec_info : 'a folder -> 'a -> Rec_info_expr.t -> 'a;
    simple : 'a folder -> 'a -> Simple.t -> 'a;
    continuation : 'a folder -> 'a -> Continuation.t -> 'a;
    result_continuation :
      'a folder -> 'a -> Apply_expr.Result_continuation.t -> 'a;
    slot : 'a folder -> 'a -> slot -> 'a;
    function_slot : 'a folder -> 'a -> Function_slot.t -> 'a;
    value_slot : 'a folder -> 'a -> Value_slot.t -> 'a;
    code_id : 'a folder -> 'a -> Code_id.t -> 'a;
    function_declarations : 'a folder -> 'a -> function_declarations -> 'a;
  }

  val default_folder : 'a folder
  (* The identity folder. *)
end = struct
  type 'a folder = {
    core_exp : 'a folder -> 'a -> core_exp -> 'a;
    named : 'a folder -> 'a -> named -> 'a;
    let_expr : 'a folder -> 'a -> let_expr -> 'a;
    let_cont_expr : 'a folder -> 'a -> let_cont_expr -> 'a;
    apply_expr : 'a folder -> 'a -> apply_expr -> 'a;
    apply_cont_expr : 'a folder -> 'a -> apply_cont_expr -> 'a;
    lambda_expr : 'a folder -> 'a -> lambda_expr -> 'a;
    continuation_handler : 'a folder -> 'a -> continuation_handler -> 'a;
    switch_expr : 'a folder -> 'a -> switch_expr -> 'a;
    literal : 'a folder -> 'a -> literal -> 'a;
    primitive : 'a folder -> 'a -> primitive -> 'a;
    variable : 'a folder -> 'a -> Variable.t -> 'a;
    set_of_closures : 'a folder -> 'a -> set_of_closures -> 'a;
    static_const_group : 'a folder -> 'a -> static_const_group -> 'a;
    static_const_or_code : 'a folder -> 'a -> static_const_or_code -> 'a;
    static_const : 'a folder -> 'a -> static_const -> 'a;
    symbol : 'a folder -> 'a -> Symbol.t -> 'a;
    function_params_and_body : 'a folder -> 'a -> function_params_and_body -> 'a;
    rec_info : 'a folder -> 'a -> Rec_info_expr.t -> 'a;
    simple : 'a folder -> 'a -> Simple.t -> 'a;
    continuation : 'a folder -> 'a -> Continuation.t -> 'a;
    result_continuation :
      'a folder -> 'a -> Apply_expr.Result_continuation.t -> 'a;
    slot : 'a folder -> 'a -> slot -> 'a;
    function_slot : 'a folder -> 'a -> Function_slot.t -> 'a;
    value_slot : 'a folder -> 'a -> Value_slot.t -> 'a;
    code_id : 'a folder -> 'a -> Code_id.t -> 'a;
    function_declarations : 'a folder -> 'a -> function_declarations -> 'a;
  }

  let core_exp_list folder acc es =
    List.fold_left (folder.core_exp folder) acc es

  let or_variable_ignoring_const folder acc (e : 'a Or_variable.t) =
    match e with
    | Const _ -> acc
    | Var (v, _debuginfo) -> folder.variable folder acc v

  let or_variables_ignoring_const folder acc (es : 'a Or_variable.t list) =
    List.fold_left (or_variable_ignoring_const folder) acc es

  let core_exp folder acc e =
    match descr e with
    | Named e -> folder.named folder acc e
    | Let e -> folder.let_expr folder acc e
    | Let_cont e -> folder.let_cont_expr folder acc e
    | Apply e -> folder.apply_expr folder acc e
    | Apply_cont e -> folder.apply_cont_expr folder acc e
    | Lambda e -> folder.lambda_expr folder acc e
    | Handler e -> folder.continuation_handler folder acc e
    | Switch e -> folder.switch_expr folder acc e
    | Invalid _ -> acc

  and named folder acc e =
    match e with
    | Literal e -> folder.literal folder acc e
    | Prim e -> folder.primitive folder acc e
    | Closure_expr (phi, slot, closures) ->
      let acc = folder.variable folder acc phi in
      let acc = folder.function_slot folder acc slot in
      folder.set_of_closures folder acc closures
    | Set_of_closures e -> folder.set_of_closures folder acc e
    | Static_consts e -> folder.static_const_group folder acc e
    | Rec_info e -> folder.rec_info folder acc e

  and let_expr folder acc e =
    Core_let.pattern_match e ~f:(fun ~x:_ ~e1 ~e2 ->
      (* CR ccasinghino: could making binding available somehow. E.g., add
         "expr_with_bound_var" to the record.  Would be needed to do free
         vars with the folder. *)
      let acc = folder.core_exp folder acc e1 in
      folder.core_exp folder acc e2)

  and let_cont_expr folder acc { handler; body } =
    let acc = folder.continuation_handler folder acc handler in
    Core_letcont_body.pattern_match body (fun _ e ->
      (* CR ccasinghino: as above, could make the cont variable available
         somehow. *)
      folder.core_exp folder acc e)

  and apply_expr folder acc
        { callee; continuation; exn_continuation; region; apply_args } =
    core_exp_list folder acc
      (callee :: continuation :: exn_continuation :: region :: apply_args)

  and apply_cont_expr folder acc { k; args } =
    core_exp_list folder acc (k :: args)

  and lambda_expr folder acc e =
    Core_lambda.pattern_match e ~f:(fun _ e ->
      (* CR ccasinghino: bound var *)
      folder.core_exp folder acc e)

  and continuation_handler folder acc e =
    Core_continuation_handler.pattern_match e (fun _ e ->
      (* CR ccasinghino: bound var *)
      folder.core_exp folder acc e)

  and switch_expr folder acc { scrutinee; arms } =
    let acc = folder.core_exp folder acc scrutinee in
    Targetint_31_63.Map.fold
      (fun _key e acc -> folder.core_exp folder acc e)
      arms
      acc

  and literal folder acc e =
    match e with
    | Simple e -> folder.simple folder acc e
    | Cont e -> folder.continuation folder acc e
    | Res_cont e -> folder.result_continuation folder acc e
    | Slot (v, s) ->
      let acc = folder.variable folder acc v in
      folder.slot folder acc s
    | Code_id e -> folder.code_id folder acc e

  and primitive folder acc e =
    match e with
    | Nullary _ -> acc
    | Unary (_, e) -> folder.core_exp folder acc e
    | Binary (_, e1, e2) -> core_exp_list folder acc [e1;e2]
    | Ternary (_, e1, e2, e3) -> core_exp_list folder acc [e1;e2;e3]
    | Variadic (_, es) -> core_exp_list folder acc es

  and variable _folder acc _ = acc

  and slot folder acc e =
    match e with
    | Function_slot f -> folder.function_slot folder acc f
    | Value_slot f -> folder.value_slot folder acc f

  and function_slot _folder acc _ = acc
  and value_slot _folder acc _ = acc

  and set_of_closures folder acc { function_decls; value_slots } =
    let acc = folder.function_declarations folder acc function_decls in
    Value_slot.Map.fold (fun _key e acc -> folder.core_exp folder acc e)
      value_slots acc

  and static_const_group folder acc e =
    List.fold_left (folder.static_const_or_code folder) acc e

  and static_const_or_code folder acc e =
    match e with
    | Code e -> folder.function_params_and_body folder acc e
    | Deleted_code -> acc
    | Static_const e -> folder.static_const folder acc e

  and static_const folder acc e =
    (* CR ccasinghino: could add folders for the constants/strings *)
    match e with
    | Static_set_of_closures e -> folder.set_of_closures folder acc e
    | Block (_tag, _mutability, es) ->
      (* CR ccasinghino: could add folder for tags *)
      core_exp_list folder acc es
    | Boxed_float e -> or_variable_ignoring_const folder acc e
    | Boxed_int32 e -> or_variable_ignoring_const folder acc e
    | Boxed_int64 e -> or_variable_ignoring_const folder acc e
    | Boxed_nativeint e -> or_variable_ignoring_const folder acc e
    | Immutable_float_block es -> or_variables_ignoring_const folder acc es
    | Immutable_float_array es -> or_variables_ignoring_const folder acc es
    | Immutable_value_array es ->
      let field_of_static_block folder acc (e : Field_of_static_block.t) =
        match e with
        | Symbol s -> folder.symbol folder acc s
        | Tagged_immediate _ -> acc
        | Dynamically_computed (v, _debuginfo) -> folder.variable folder acc v
      in
      List.fold_left (field_of_static_block folder) acc es
    | Empty_array -> acc
    | Mutable_string _ -> acc
    | Immutable_string _ -> acc

  and symbol _folder acc _ = acc

  and function_params_and_body folder acc { expr; anon = _ } =
    Core_function_params_and_body.pattern_match expr ~f:(fun _ e ->
      (* CR ccasinghino: bound var *)
      folder.lambda_expr folder acc e)

  and rec_info folder acc (e : Rec_info_expr.t) =
    let rec on_var folder acc (e : Rec_info_expr.t) =
      match e with
      | Const _ -> acc
      | Var v -> folder.variable folder acc v
      | Succ t -> on_var folder acc t
      | Unroll_to (_, t) -> on_var folder acc t
    in
    on_var folder acc e

  and simple folder acc (e : Simple.t) =
    Simple.pattern_match' e
      ~var:(fun v ~coercion:_ -> folder.variable folder acc v)
      ~symbol:(fun v ~coercion:_ -> folder.symbol folder acc v)
      ~const:(fun _ -> acc)

  and continuation _folder acc _ = acc
  (* CR ccasinghino: ? *)

  and result_continuation folder acc (e : Apply_expr.Result_continuation.t) =
    match e with
    | Return e -> folder.continuation folder acc e
    | Never_returns -> acc

  and code_id _folder acc _ = acc

  and function_declarations folder acc e =
    SlotMap.fold (fun _ e acc -> folder.core_exp folder acc e) e acc

  let default_folder : 'a . 'a folder = {
    core_exp;
    named;
    let_expr;
    let_cont_expr;
    apply_expr;
    apply_cont_expr;
    lambda_expr;
    continuation_handler;
    switch_expr;
    literal;
    primitive;
    variable;
    slot;
    function_slot;
    value_slot;
    set_of_closures;
    static_const_group;
    static_const_or_code;
    static_const;
    symbol;
    function_params_and_body;
    rec_info;
    simple;
    continuation;
    result_continuation;
    code_id;
    function_declarations;
  }
end

module Effects = struct
  let effects_and_coeffects (p : primitive) =
    match p with
    | Nullary prim ->
      Flambda_primitive.effects_and_coeffects_of_nullary_primitive prim
    | Unary (prim, _) ->
      Flambda_primitive.effects_and_coeffects_of_unary_primitive prim
    | Binary (prim, _, _) ->
      Flambda_primitive.effects_and_coeffects_of_binary_primitive prim
    | Ternary (prim, _, _, _) ->
      Flambda_primitive.effects_and_coeffects_of_ternary_primitive prim
    | Variadic (prim, _) ->
      Flambda_primitive.effects_and_coeffects_of_variadic_primitive prim

  let no_effects (p : primitive) =
    match effects_and_coeffects p with
    | No_effects, _, _ -> true
    | ( (Only_generative_effects _ | Arbitrary_effects),
        (No_coeffects | Has_coeffects),
        _ ) ->
      false

  let no_effects (e : core_exp) : bool =
    match must_be_prim e with
    | None -> true
    | Some p -> no_effects p

  let no_effects_or_coeffects (p : primitive) =
    match effects_and_coeffects p with
    | No_effects, No_coeffects, _ -> true
    | ( (No_effects | Only_generative_effects _ | Arbitrary_effects),
        (No_coeffects | Has_coeffects),
        _ ) ->
      false

  let no_effects_or_coeffects (e : core_exp) : bool =
    match must_be_prim e with
    | None -> true
    | Some p -> no_effects_or_coeffects p

  type substitutability =
    | Can_duplicate
    (* Things with no co-effects and only generative effects can be substituted freely for
       our analysis.  Those for things with generative effects, it would be a bug for
       flambda2 itself to do so, as this may increase allocation. *)
    | Can_delete_if_unused
    (* Things with co-effects and only generative effects.  These can't be substituted,
       because their co-effects mean that reordering them is a change in behavior.  But if
       their result is not used they can be deleted because they don't have observable
       effects. *)
    | No_substitutions
    (* Things with real effects can't be moved or deleted at all. *)

  let can_substitute (p : primitive) =
    match effects_and_coeffects p with
    | (No_effects | Only_generative_effects _), No_coeffects, _ -> Can_duplicate
    | (No_effects | Only_generative_effects _), Has_coeffects, _ ->
      Can_delete_if_unused
    | Arbitrary_effects, (No_coeffects | Has_coeffects), _ -> No_substitutions

  (* If any part of an expression is not substitutable, the whole is. *)
  let combine_substitutability s1 s2 =
    match s1, s2 with
    | No_substitutions, _ | _, No_substitutions -> No_substitutions
    | Can_delete_if_unused, _ | _, Can_delete_if_unused -> Can_delete_if_unused
    | Can_duplicate, Can_duplicate -> Can_duplicate

  let can_substitute (e : core_exp) =
    (* We used to only count primitives themselves as effectful.  This was
       wrong.  Now we descend deeper, but are still careful not to go under
       closures (something that closes over an effect is not an effect). But
       we're still too generous here: an application of such a function is
       effectful, but we treat it as not.  This could be fixed.
    *)
    let folder =
      {Ast_folder.default_folder with
       lambda_expr = (fun _ _ _ -> Can_duplicate);
       continuation_handler = (fun _ _ _ -> Can_duplicate);
       function_declarations = (fun _ _ _ -> Can_duplicate);
       function_params_and_body = (fun _ _ _ -> Can_duplicate);
       primitive = fun self acc p ->
         let acc = combine_substitutability acc (can_substitute p) in
         Ast_folder.default_folder.primitive self acc p}
    in
    folder.core_exp folder Can_duplicate e
end

let returns_unit (p : primitive) : bool =
  match p with
  | Ternary _ -> true
  | (Nullary _ | Unary _ | Binary _ | Variadic _) -> false

let returns_unit (e : core_exp) : bool =
  match must_be_prim e with
  | None -> false
  | Some p -> returns_unit p
