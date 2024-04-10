module P = Flambda_primitive
let fprintf = Format.fprintf

(* ========================================================================== *)
(** Simplified core of [flambda2] terms **)

(* Notes
   (1) Simple.t -> core_exp for [Apply*] expressions
   (2) Ignore [Num_occurrences] (which is used for making inlining decisions)
   (3) Ignored traps for now *)

(* ========================================================================== *)

(** *Delayed renaming scheme **)

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

(* ========================================================================== *)
(** [Flambda2] core expressions. *)
(* Idealized lambda-calculus for [Flambda2] expressions. *)

type core_exp = exp_descr With_delayed_renaming.t

and exp_descr =
  | Var of variable
  (* Primitive operations *)
  | Prim of primitive
  (* Static constants, which include literal expressions and blocks *)
  | Const of constant
  (* Recursive binding TODO *)
  | Rec of core_exp list
  (* Application *)
  | App of apply_expr
  (* A lambda for code expressions and continuations. *)
  | Lam of lambda_expr
  (* LATER: Is this necessary? *)
  | Closure_expr of (Variable.t * Function_slot.t * closures)
  (* Closures *)
  | Closures of closures
  (* Switch expression. *)
  | Switch of switch_expr
  (* "Invalid" *)
  | Error of { message : string }

(* Variables. *)
and variable =
  | Simple of Simple.t
  | Slot of (Variable.t * slot)

(* Lambda expressions: captures all variants of lambdas in Flambda2, including
   - code bindings
   - lambda expressions
   - "continuation handler" expressions

   Lambda expressions are of the form : [ λ k_r k_e region args => e ]
   where [k_r] and [k_e] are the return and exceptional continuations, the [region]
   variable indicates the closure environments, and [args] are the formal arguments
   to the function. *)
and lambda_expr = (Bound_parameters.t, core_exp) Name_abstraction.t

(* Slots for functions and values in the environment *)
and slot =
  | Function_slot of Function_slot.t
  | Value_slot of Value_slot.t

(* Closures, which store function declarations and an environment for values. *)
and closures =
  { (* Function declarations (N.B. the map is ordered.) *)
    function_decls : core_exp SlotMap.t;
    (* Environment *)
    value_slots : core_exp Value_slot.Map.t}

(* Application. *)
and apply_expr =
  { callee: core_exp;
    apply_args: core_exp list; }

(* Switch. *)
and switch_expr =
  { scrutinee : core_exp;
    arms : core_exp Targetint_31_63.Map.t }

(* Primitive operands. *)
and primitive =
  | Nullary of P.nullary_primitive
  | Unary of P.unary_primitive * core_exp
  | Binary of P.binary_primitive * core_exp * core_exp
  | Ternary of P.ternary_primitive * core_exp * core_exp * core_exp
  | Variadic of P.variadic_primitive * core_exp list

(* Constants. *)
and constant =
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

(* (\* ========================================================================== *\) *)

(* type simple_type = *)
(*   | Var of Variable.t *)
(*   | Symbol of Symbol.t *)
(*   | Naked_immediate of Targetint_31_63.t *)
(*   | Tagged_immediate of Targetint_31_63.t *)
(*   | Naked_float of Numeric_types.Float_by_bit_pattern.t *)
(*   | Naked_int32 of Int32.t *)
(*   | Naked_int64 of Int64.t *)
(*   | Naked_nativeint of Targetint_32_64.t *)

(* let simple_with_type (s : Simple.t) : simple_type = *)
(*   Simple.pattern_match' s *)
(*     ~var:(fun v ~coercion:_ -> Var v) *)
(*     ~symbol:(fun s ~coercion:_ -> Symbol s) *)
(*     ~const:(fun x -> *)
(*       match Int_ids.Const.descr x with *)
(*       | Naked_immediate i -> Naked_immediate i *)
(*       | Tagged_immediate i -> Tagged_immediate i *)
(*       | Naked_float i -> Naked_float i *)
(*       | Naked_int32 i -> Naked_int32 i *)
(*       | Naked_int64 i -> Naked_int64 i *)
(*       | Naked_nativeint i -> Naked_nativeint i) *)

(* ========================================================================== *)

(** Nominal renaming for [core_exp] **)
let rec descr expr =
  With_delayed_renaming.descr expr
    ~apply_renaming_descr:apply_renaming_exp_descr

and apply_renaming = With_delayed_renaming.apply_renaming

and apply_renaming_exp_descr (t : exp_descr) renaming : exp_descr =
  match t with
  | Var var ->
    let var' = apply_renaming_variable var renaming in
    if var == var' then t else Var var
  | Prim prim ->
    let prim' = apply_renaming_prim prim renaming in
    if prim == prim' then t else Prim prim'
  | Consts consts ->
    let consts' = apply_renaming_consts consts renaming in
    if consts == consts' then t else Consts consts'
  | Closure_expr (var, slot, set) ->
    let var' = Renaming.apply_variable renaming var in
    let set' = apply_renaming_closures set renaming in
    if var == var' && set == set' then t else Closure_expr (var', slot, set')
  | Closures clos ->
    let clos' = apply_renaming_closures clos renaming in
    if clos == clos' then t else Closures clos'
  | App app ->
    let app' = apply_renaming_apply app renaming in
    if app == app' then t else App app'
  | Lam lam ->
    let lam' = apply_renaming_lambda lam renaming in
    if lam == lam' then t else Lam lam'
  | Switch switch ->
    let switch' = apply_renaming_switch switch renaming in
    if switch == switch' then t else Switch switch'
  | Error _ -> t

and apply_renaming_lambda t renaming : lambda_expr =
  Name_abstraction.apply_renaming (module Bound_parameters) t renaming
    ~apply_renaming_to_term:apply_renaming

and apply_renaming_variable (t : variable) renaming : variable =
  match t with
  | Simple simple ->
    let simple' = Simple.apply_renaming simple renaming in
    if simple == simple' then t else Simple simple'
  | Slot (var, slot) ->
    let var' = Renaming.apply_variable renaming var in
    if var == var' then t else Slot (var', slot)

and apply_renaming_function_declarations
      (funs : core_exp SlotMap.t) renaming =
  SlotMap.map (fun x -> apply_renaming x renaming) funs

and apply_renaming_closures
      ({ function_decls; value_slots } as t : closures)
      renaming : closures =
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

and apply_renaming_consts (t : constant list) renaming : constant list =
  Misc.Stdlib.List.map_sharing
    (fun const -> apply_renaming_const const renaming) t

and apply_renaming_const (t : constant) renaming : constant =
  if Renaming.is_empty renaming
  then t
  else
    match t with
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

(* renaming for [Apply] *)
and apply_renaming_apply
      ({ callee; apply_args} as t)
      renaming : apply_expr =
  let callee' = apply_renaming callee renaming in
  let apply_args' =
    Misc.Stdlib.List.map_sharing (fun x -> apply_renaming x renaming) apply_args
  in
  if callee == callee' && apply_args == apply_args' then t
  else
    { callee = callee';
      apply_args = apply_args'; }

(* renaming for [Switch] *)
and apply_renaming_switch ({scrutinee; arms} as t) renaming : switch_expr =
  let scrutinee' = apply_renaming scrutinee renaming in
  let arms' =
    Targetint_31_63.Map.map_sharing (fun x -> apply_renaming x renaming) arms
  in
  if scrutinee == scrutinee' && arms == arms'
  then t
  else { scrutinee = scrutinee'; arms = arms' }

(* ========================================================================== *)

(** Sexp-ish simple pretty-printer for [core_exp]s.
  Ignores name_stamp, compilation_unit, and debug_info for simplicity. **)
let rec print ppf e =
  match descr e with
   | Var t ->
     fprintf ppf "@[<hov 1>%a@]"
     print_var t
   | Prim prim -> print_prim ppf prim
   | Consts consts -> print_consts ppf consts
   | App t ->
     fprintf ppf "@[<hov 1>apply %a@]"
     print_apply t
   | Lam t ->
     fprintf ppf "@[<hov 1>λ@ %a@]"
     print_lambda t
   | Closure_expr (var, slot, clo) ->
     fprintf ppf "@[<hov 3>clo(%a,@ %a,@. %a)@]"
       Variable.print var
       Function_slot.print slot
       (fun ppf clo -> print_closures ppf clo) clo
   | Closures clo ->
     fprintf ppf "closures@. @[<hov 2>%a@]"
       print_closures clo
   | Switch t ->
     fprintf ppf "@[<hov 1>switch %a@]"
     print_switch t
   | Error { message } ->
     fprintf ppf "@[<hov 1>invalid %s@]" message

and print_lambda ppf t =
  Name_abstraction.pattern_match_for_printing
    (module Bound_parameters)
    t ~apply_renaming_to_term:apply_renaming
    ~f:(fun bound body ->
      fprintf ppf "%a ->@.   @[<hov 1>%a@]"
        Bound_parameters.print bound
        print body)

and print_var ppf (t : variable) =
  match t with
  | Simple simple ->
    fprintf ppf "simple %a"
      Simple.print simple
  | Slot (var, Function_slot slot) ->
    fprintf ppf "slot(%a, %a)"
      Variable.print var
      Function_slot.print slot
  | Slot (var, Value_slot slot) ->
    fprintf ppf "slot(%a, %a)"
      Variable.print var
      Value_slot.print slot

and print_closures ppf
      { function_decls;
        value_slots } =
  if Value_slot.Map.is_empty value_slots then
    Format.fprintf ppf "(%a)"
      print_function_declaration function_decls
  else
    Format.fprintf ppf "(%a@.)"
      print_function_declaration function_decls

and print_function_declaration ppf in_order =
  Format.fprintf ppf "@[<hov 1>{%a}@]"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space
       (fun ppf (key, datum) ->
          Format.fprintf ppf "@[<hov 1>(%a@ %a)@]"
            Function_slot.print key print
            datum)) (in_order |> SlotMap.bindings)

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

and print_consts ppf t =
  Format.pp_print_list ~pp_sep:Format.pp_print_space print_const ppf t

and print_const ppf (t : constant) : unit =
  match t with
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

and print_apply ppf
      ({callee; apply_args} : apply_expr) =
  fprintf ppf "(callee:@[<hov 2>%a@])@"
    print callee;
  fprintf ppf " (args:";
  Format.pp_print_list ~pp_sep:Format.pp_print_space print ppf apply_args;
  fprintf ppf ")"

and print_switch ppf ({scrutinee; arms} : switch_expr) =
  fprintf ppf "(%a) with @ @[<v 0>" print scrutinee;
  Targetint_31_63.Map.iter (print_arm ppf) arms;
  fprintf ppf "@]"

and print_arm ppf key arm =
  fprintf ppf "@[<hov 2>@[<hov 0>| %a -> @]%a@]@ "
    Targetint_31_63.print key
    print arm

(* ========================================================================== *)

(** [ids_for_export] is the set of bound variables for a given expression **)
let rec ids_for_export (t : core_exp) =
  match descr t with
  | Var t -> ids_for_export_var t
  | Prim t -> ids_for_export_prim t
  | Consts t -> ids_for_export_consts t
  | App t -> ids_for_export_apply t
  | Lam t -> ids_for_export_lambda t
  | Closure_expr t -> ids_for_export_closure_expr t
  | Closures t -> ids_for_export_closures t
  | Switch t -> ids_for_export_switch t
  | Error _ -> Ids_for_export.empty

and ids_for_export_var (t : variable) =
  match t with
  | Simple simple ->
    Ids_for_export.from_simple simple
  | Slot (var, _) ->
    Ids_for_export.singleton_variable var

and ids_for_export_closure_expr
    ((var, _, set) : Variable.t * Function_slot.t * closures) =
  Ids_for_export.add_variable (ids_for_export_closures set) var

(* and ids_for_export_named (t : named) = *)
(*   match t with *)
(*   | Literal literal -> ids_for_export_literal literal *)
(*   | Closure_expr (var, _, set) -> *)
(*     Ids_for_export.add_variable *)
(*     (ids_for_export_closures set) var *)
(*   | Prim prim -> ids_for_export_prim prim *)
(*   | closures set -> ids_for_export_closures set *)
(*   | Static_consts consts -> ids_for_export_static_const_group consts *)
(*   | Rec_info info -> Rec_info_expr.ids_for_export info *)

and ids_for_export_function_decls funs =
  SlotMap.fold
    (fun _function_slot fn_expr ids ->
       Ids_for_export.union (ids_for_export fn_expr) ids)
    funs Ids_for_export.empty

and ids_for_export_closures
      ({function_decls; value_slots} : closures) =
  let function_decls_ids =
    ids_for_export_function_decls function_decls
  in
  Value_slot.Map.fold
      (fun _value_slot value ids ->
          Ids_for_export.union ids (ids_for_export value))
      value_slots function_decls_ids

and ids_for_export_prim (t : primitive) =
  match t with
  | Nullary
      (Invalid _ | Optimised_out _ | Probe_is_enabled _ | Begin_region
      | Enter_inlined_apply _) ->
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

and ids_for_export_consts t =
  List.map ids_for_export_const t |> Ids_for_export.union_list

and ids_for_export_fields fields =
  List.fold_left
    (fun ids field ->
       Ids_for_export.union ids (Field_of_static_block.ids_for_export field))
    Ids_for_export.empty fields

and ids_for_export_const t =
  match t with
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

(* ids for [Apply] *)
and ids_for_export_apply
      { callee; apply_args } =
  let callee_ids = ids_for_export callee in
  List.fold_left
    (fun ids arg -> Ids_for_export.union ids (ids_for_export arg))
      callee_ids apply_args

(* ids for [Lambda] *)
and ids_for_export_lambda t =
   Name_abstraction.ids_for_export
     (module Bound_parameters) t ~ids_for_export_of_term:ids_for_export

and ids_for_export_switch { scrutinee; arms } =
  let scrutinee_ids = ids_for_export scrutinee in
  Targetint_31_63.Map.fold
    (fun _discr action ids ->
        Ids_for_export.union ids (ids_for_export action))
    arms scrutinee_ids

(* ========================================================================== *)
(* Module definitions for [Name_abstraction] *)

module Expr = struct
  type t = core_exp
  type descr = exp_descr
  let apply_renaming = apply_renaming
  let ids_for_export = ids_for_export
  let descr = descr
  let create = With_delayed_renaming.create

  let create_var var = create (Var var)
  let create_prim prim = create (Prim prim)
  let create_consts const = create (Consts const)
  let create_apply apply = create (App apply)
  let create_closure_expr e = create (Closure_expr e)
  let create_closures clos = create (Closures clos)
  let create_lambda lambda = create (Lam lambda)
  let create_switch switch = create (Switch switch)
  let create_invalid msg = create (Error {message = msg})
end

(* module Core_let = struct *)
(*   module A = Name_abstraction.Make (Bound_for_let) (Expr) *)
(*   type t = let_expr *)
(*   let create ~(x : Bound_for_let.t) ~(e1 : core_exp) ~(e2 : core_exp)  = *)
(*     Expr.create_let { let_abst = A.create x e2; expr_body = e1 } *)

(*   module Pattern_match_pair_error = struct *)
(*     type t = Mismatched_let_bindings *)
(*   end *)

(*   let pattern_match t ~(f : x:Bound_for_let.t -> e1:core_exp -> e2:core_exp -> 'a) : 'a = *)
(*     let open A in *)
(*     let<> x, e2 = t.let_abst in *)
(*     f ~x ~e1:t.expr_body ~e2 *)

(*   (\* Treat "dynamic binding" (statically scoped binding under lambda abstraction) *)
(*      and "static binding" (globally scoped mapping of statics) differently *\) *)
(*   let pattern_match_pair *)
(*         ({let_abst = let_abst1; expr_body = _}) *)
(*         ({let_abst = let_abst2; expr_body = _}) *)
(*         (dynamic : Bound_for_let.t -> core_exp -> core_exp -> 'a) *)
(*         (static : Bound_codelike.t -> Bound_codelike.t -> core_exp -> core_exp -> 'a): *)
(*     ('a, Pattern_match_pair_error.t) Result.t = *)
(*     A.pattern_match let_abst1 ~f:(fun let_bound1 expr_body1 -> *)
(*       A.pattern_match let_abst2 ~f:(fun let_bound2 expr_body2 -> *)
(*         let dynamic_case () = *)
(*           let ans = A.pattern_match_pair let_abst1 let_abst2 ~f:dynamic *)
(*           in Ok ans *)
(*         in *)
(*         match let_bound1, let_bound2 with *)
(*         | Bound_for_let.Singleton _, Bound_for_let.Singleton _ -> dynamic_case () *)
(*         | Static bound_static1, Static bound_static2 -> *)
(*           let patterns1 = bound_static1 |> Bound_codelike.to_list in *)
(*           let patterns2 = bound_static2 |> Bound_codelike.to_list in *)
(*           if List.compare_lengths patterns1 patterns2 = 0 *)
(*           then *)
(*             let ans = static bound_static1 bound_static2 expr_body1 expr_body2 in *)
(*             Ok ans *)
(*           else Error Pattern_match_pair_error.Mismatched_let_bindings *)
(*         | (Singleton _ | Static _), _ -> *)
(*             Error Pattern_match_pair_error.Mismatched_let_bindings *)
(*       ) *)
(*     ) *)
(* end *)

(* module Core_letcont_body = struct *)
(*   module A = Name_abstraction.Make (Bound_continuation) (Expr) *)
(*   type t = (Bound_continuation.t, core_exp) Name_abstraction.t *)
(*   let create = A.create *)
(*   let pattern_match (e : t) (f : Bound_continuation.t -> core_exp -> 'a) : 'a = *)
(*     A.pattern_match e ~f:(fun cont body -> f cont body) *)
(*   let pattern_match_pair (t1 : t) (t2 : t) *)
(*         (f : Bound_continuation.t -> core_exp -> core_exp -> 'a) : 'a = *)
(*     A.pattern_match_pair t1 t2 ~f:(fun cont body1 body2 -> *)
(*       f cont body1 body2) *)
(* end *)

(* module Core_letcont = struct *)
(*   type t = let_cont_expr *)

(*   let print = print_let_cont *)

(*   let create handler ~body = *)
(*     Expr.create_let_cont {handler; body} *)
(* end *)

module Core_lambda = struct
  module A = Name_abstraction.Make (Bound_parameters) (Expr)
  type t = lambda_expr

  let pattern_match x ~f =
    A.pattern_match x ~f:(fun b e -> f b e)

  let create = A.create

  let unary_create x e =
    A.create (Bound_parameters.create
      [Bound_parameter.create x Flambda_kind.With_subkind.any_value]) e

  (* let apply_renaming = apply_renaming_lambda *)
  (* let ids_for_export = ids_for_export_lambda *)

  let pattern_match_pair t1 t2 ~f =
    A.pattern_match_pair t1 t2
      ~f:(fun
           bound body1 body2
           -> f bound body1 body2)
end

(* module Core_function_params_and_body = struct *)
(*   module A = Name_abstraction.Make (Bound_var) (Core_lambda) *)
(*   type t = (Bound_var.t, Core_lambda.t) Name_abstraction.t *)

(*   let create = A.create *)

(*   let my_closure t = A.pattern_match t ~f:(fun param _ -> param) *)

(*   let lambda_expr t = A.pattern_match t ~f:(fun _ body -> body) *)

(*   let pattern_match = A.pattern_match *)

(*   let pattern_match_pair t1 t2 ~f = *)
(*     A.pattern_match_pair t1 t2 *)
(*       ~f:(fun my_closure body1 body2 -> *)
(*         Core_lambda.pattern_match_pair body1 body2 *)
(*           ~f:(fun params body1 body2 -> *)
(*             f params ~body1 ~body2 ~my_closure)) *)
(* end *)

(* (\* ========================================================================== *\) *)
(* (\** Fixpoint combinators for core expressions **\) *)

(* let let_fix (f : core_exp -> core_exp) {let_abst; expr_body} = *)
(*   Core_let.pattern_match {let_abst; expr_body} *)
(*     ~f:(fun ~x ~e1 ~e2 -> *)
(*       (Core_let.create *)
(*         ~x *)
(*         ~e1:(f e1) *)
(*         ~e2:(f e2))) *)

(* let let_cont_fix (f : core_exp -> core_exp) ({handler; body} : let_cont_expr) = *)
(*   let handler : lambda_expr = *)
(*     Core_lambda.pattern_match handler *)
(*       ~f:(fun param exp -> Core_lambda.create param (f exp)) *)
(*   in *)
(*   let body = *)
(*     Core_letcont_body.pattern_match body *)
(*       (fun cont exp -> *)
(*           Core_letcont_body.create cont (f exp)) *)
(*   in *)
(*   Core_letcont.create handler ~body *)

(* let apply_fix (f : core_exp -> core_exp) *)
(*       ({callee; ret_continuation; exn_continuation; region; apply_args} : apply_expr) = *)
(*   Apply *)
(*     {callee = f callee; *)
(*      ret_continuation = f ret_continuation; *)
(*      exn_continuation = f exn_continuation; *)
(*      region = f region; *)
(*      apply_args = List.map f apply_args;} *)
(*   |> With_delayed_renaming.create *)

(* let lambda_fix (f : core_exp -> core_exp) (e : lambda_expr) = *)
(*   Core_lambda.pattern_match e *)
(*     ~f:(fun b e -> *)
(*       (Core_lambda.create b (f e))) *)
(*   |> Expr.create_lambda *)

(* let switch_fix (f : core_exp -> core_exp) *)
(*       ({scrutinee; arms} : switch_expr) = *)
(*   {scrutinee = f scrutinee; *)
(*     arms = Targetint_31_63.Map.map f arms} *)
(*   |> Expr.create_switch *)

(* let closures_fix *)
(*       (fix : core_exp -> core_exp) {function_decls; value_slots} = *)
(*   let function_decls = SlotMap.map fix function_decls in *)
(*   let value_slots = *)
(*     Value_slot.Map.map (fun x -> fix x) value_slots *)
(*   in *)
(*   {function_decls; value_slots} *)

(* let static_const_fix (fix : core_exp -> core_exp) (e : static_const) = *)
(*   match e with *)
(*   | Static_closures clo -> *)
(*     let {function_decls; value_slots} = closures_fix fix clo in *)
(*     Static_closures {function_decls; value_slots} *)
(*   | Block (tag, mut, list) -> *)
(*     let list = List.map fix list in *)
(*     Block (tag, mut, list) *)
(*   | ( Boxed_float _ | Boxed_int32 _ | Boxed_int64 _ | Boxed_nativeint _ *)
(*     | Immutable_float_block _ | Immutable_float_array _ | Immutable_value_array _ *)
(*     | Empty_array | Mutable_string _ | Immutable_string _ ) -> e *)

(* let static_const_or_code_fix (fix : core_exp -> core_exp) *)
(*   (e : static_const_or_code) = *)
(*   (match e with *)
(*   | Code {expr; anon}-> *)
(*     Code *)
(*       {expr = *)
(*          Core_function_params_and_body.pattern_match expr *)
(*          ~f:(fun *)
(*               params body -> *)
(*               Core_function_params_and_body.create *)
(*                 params *)
(*                 (Core_lambda.pattern_match body *)
(*                    ~f:(fun bound body -> *)
(*                      Core_lambda.create bound (fix body)))); *)
(*        anon} *)
(*   | Deleted_code -> e *)
(*   | Static_const const -> *)
(*     Static_const (static_const_fix fix const)) *)

(* let static_const_group_fix (fix : core_exp -> core_exp) *)
(*        (e : static_const_group) = *)
(*   Named (Static_consts (List.map (static_const_or_code_fix fix) e)) *)
(*   |> With_delayed_renaming.create *)

(* let prim_fix (fix : core_exp -> core_exp) (e : primitive) = *)
(*   (match e with *)
(*   | Nullary _ -> Named (Prim e) *)
(*   | Unary (p, e) -> *)
(*     Named (Prim (Unary (p, fix e))) *)
(*   | Binary (p, e1, e2) -> *)
(*     Named (Prim (Binary (p, fix e1, fix e2))) *)
(*   | Ternary (p, e1, e2, e3) -> *)
(*     Named (Prim (Ternary (p, fix e1, fix e2, fix e3))) *)
(*   | Variadic (p, list) -> *)
(*     Named (Prim (Variadic (p, List.map fix list)))) *)
(*   |> With_delayed_renaming.create *)

(* let named_fix (fix : core_exp -> core_exp) *)
(*       (f : 'a -> literal -> core_exp) arg (e : named) = *)
(*   match e with *)
(*   | Literal l -> f arg l *)
(*   | Prim e -> prim_fix fix e *)
(*   | Closure_expr (phi, slot, clo) -> *)
(*     let {function_decls; value_slots} = closures_fix fix clo in *)
(*     Named (Closure_expr (phi, slot, {function_decls; value_slots})) *)
(*     |> With_delayed_renaming.create *)
(*   | closures clo -> *)
(*     let {function_decls; value_slots} = closures_fix fix clo in *)
(*     Named (closures {function_decls; value_slots}) *)
(*     |> With_delayed_renaming.create *)
(*   | Static_consts group -> *)
(*     static_const_group_fix fix group *)
(*   | Rec_info _ -> *)
(*     Named e *)
(*     |> With_delayed_renaming.create *)

(* (\* LATER: Make this first order? *\) *)
(* let rec core_fmap *)
(*   (f : 'a -> literal -> core_exp) (arg : 'a) (e : core_exp) : core_exp = *)
(*   match descr e with *)
(*   | Named e -> *)
(*     named_fix (core_fmap f arg) f arg e *)
(*   | Let e -> let_fix (core_fmap f arg) e *)
(*   | Let_cont e -> let_cont_fix (core_fmap f arg) e *)
(*   | Apply e -> apply_fix (core_fmap f arg) e *)
(*   | Lambda e -> lambda_fix (core_fmap f arg) e *)
(*   | Switch e -> switch_fix (core_fmap f arg) e *)
(*   | Invalid _ -> e *)

(* (\* ========================================================================== *\) *)
(* (\** Auxilary functions for core expressions *\) *)

(* let literal_contained (literal1 : literal) (literal2 : literal) : bool = *)
(*   match literal1, literal2 with *)
(*   | Simple simple1, Simple simple2 -> *)
(*     Simple.same simple1 simple2 *)
(*   | (Cont cont1, Cont cont2 *)
(*     | Res_cont (Return cont1), Res_cont (Return cont2)) *)
(*     -> Continuation.equal cont1 cont2 *)
(*   | Simple simple, Slot (phi, _) -> *)
(*     Simple.same (Simple.var phi) simple *)
(*   | Slot (_, Function_slot slot1), Slot (_, Function_slot slot2) -> *)
(*     Function_slot.equal slot1 slot2 *)
(*   | Slot (_, Value_slot slot1), Slot (_, Value_slot slot2) -> *)
(*     Value_slot.equal slot1 slot2 *)
(*   | Res_cont Never_returns, Res_cont Never_returns -> true *)
(*   | Code_id code1, Code_id code2 -> *)
(*     Code_id.name code1 == Code_id.name code2 *)
(*   | (Simple _ | Cont _ | Slot (_, (Function_slot _ | Value_slot _)) *)
(*     | Res_cont (Never_returns | Return _) | Code_id _), _ -> false *)

(* let effects_and_coeffects (p : primitive) = *)
(*   match p with *)
(*   | Nullary prim -> *)
(*     Flambda_primitive.effects_and_coeffects_of_nullary_primitive prim *)
(*   | Unary (prim, _) -> *)
(*     Flambda_primitive.effects_and_coeffects_of_unary_primitive prim *)
(*   | Binary (prim, _, _) -> *)
(*     Flambda_primitive.effects_and_coeffects_of_binary_primitive prim *)
(*   | Ternary (prim, _, _, _) -> *)
(*     Flambda_primitive.effects_and_coeffects_of_ternary_primitive prim *)
(*   | Variadic (prim, _) -> *)
(*     Flambda_primitive.effects_and_coeffects_of_variadic_primitive prim *)

(* let no_effects (p : primitive) = *)
(*   match effects_and_coeffects p with *)
(*   | No_effects, _, _ -> true *)
(*   | ( (Only_generative_effects _ | Arbitrary_effects), *)
(*       (No_coeffects | Has_coeffects), *)
(*       _ ) -> *)
(*     false *)

(* let no_effects (e : core_exp) : bool = *)
(*   match must_be_prim e with *)
(*   | None -> true *)
(*   | Some p -> no_effects p *)

(* let can_inline (p : primitive) = *)
(*   match effects_and_coeffects p with *)
(*   | No_effects, No_coeffects, _ -> true *)
(*   | Only_generative_effects _, No_coeffects, _ -> true *)
(*   | ( (No_effects | Only_generative_effects _ | Arbitrary_effects), *)
(*       (No_coeffects | Has_coeffects), *)
(*       _ ) -> *)
(*     false *)

(* let can_inline (e : core_exp) : bool = *)
(*   match must_be_prim e with *)
(*   | None -> true *)
(*   | Some p -> can_inline p *)

(* let no_effects_or_coeffects (p : primitive) = *)
(*   match effects_and_coeffects p with *)
(*   | No_effects, No_coeffects, _ -> true *)
(*   | ( (No_effects | Only_generative_effects _ | Arbitrary_effects), *)
(*       (No_coeffects | Has_coeffects), *)
(*       _ ) -> *)
(*     false *)

(* let no_effects_or_coeffects (e : core_exp) : bool = *)
(*   match must_be_prim e with *)
(*   | None -> true *)
(*   | Some p -> no_effects_or_coeffects p *)

(* let returns_unit (p : primitive) : bool = *)
(*   match p with *)
(*   | Ternary _ -> true *)
(*   | (Nullary _ | Unary _ | Binary _ | Variadic _) -> false *)

(* let returns_unit (e : core_exp) : bool = *)
(*   match must_be_prim e with *)
(*   | None -> false *)
(*   | Some p -> returns_unit p *)
