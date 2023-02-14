module P = Flambda_primitive
let fprintf = Format.fprintf

(** Simplified core of [flambda2] terms **)
(* (1) Simple.t -> core_exp for [Apply*] expressions
   (2) Ignore [Num_occurrences] (which is used for making inlining decisions)
   (3) Ignored traps for now *)

type core_exp =
  | Named of named
  | Let of let_expr
  | Let_cont of let_cont_expr
  | Apply of apply_expr
  | Apply_cont of apply_cont_expr
  | Switch of switch_expr
  | Invalid of { message : string }

(** Let expressions [let x = e1 in e2]

   [fun x -> e2] = let_abst
   [e1] = body **)
and let_expr =
  { let_abst : (Bound_pattern.t, core_exp) Name_abstraction.t;
    let_body : core_exp; }

and named =
  | Simple of Simple.t
  | Prim of primitive
  | Set_of_closures of set_of_closures
  | Static_consts of static_const_group
  | Rec_info of Rec_info_expr.t

and set_of_closures =
  { function_decls : function_declarations;
    value_slots : (Simple.t * Flambda_kind.With_subkind.t) Value_slot.Map.t;
    alloc_mode : Alloc_mode.For_allocations.t }

and function_declarations =
  { funs : function_expr Function_slot.Map.t;
    in_order : function_expr Function_slot.Lmap.t}

and function_expr =
  | Id of Code_id.t
  | Exp of core_exp

and primitive =
  | Nullary of P.nullary_primitive
  | Unary of P.unary_primitive * core_exp
  | Binary of P.binary_primitive * core_exp * core_exp
  | Ternary of P.ternary_primitive * core_exp * core_exp * core_exp
  | Variadic of P.variadic_primitive * core_exp list

and function_params_and_body =
  (Bound_for_function.t, core_exp) Name_abstraction.t

and static_const_or_code =
  | Code of function_params_and_body Code0.t
  | Deleted_code
  | Static_const of static_const

and static_const =
  | Static_set_of_closures of set_of_closures
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
  | Non_recursive of
    { handler : continuation_handler;
      body : (Bound_continuation.t, core_exp) Name_abstraction.t;}

  (* Recursive case, we have a set of (mutually recursive) continuations
     [let rec K x in e] where [K] is a map of continuations
     [x] is the set of invariant parameters
     bound variable [K] is in the scope of [e]

     [x] = invariant_params (Bound_parameters.t)
     [K] = continuation_map
     [e] = body *)
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
    apply_args: core_exp list;
    call_kind: Call_kind.t; }

and apply_cont_expr =
  { k : Continuation.t;
    args : core_exp list }

and switch_expr =
  { scrutinee : core_exp;
    arms : core_exp Targetint_31_63.Map.t }

(** Nominal renaming for [core_exp] **)
let rec apply_renaming t renaming : core_exp =
  match t with
  | Named t -> Named (apply_renaming_named t renaming)
  | Let t -> Let (apply_renaming_let t renaming)
  | Let_cont t -> Let_cont (apply_renaming_let_cont t renaming)
  | Apply t -> Apply (apply_renaming_apply t renaming)
  | Apply_cont t -> Apply_cont (apply_renaming_apply_cont t renaming)
  | Switch t -> Switch (apply_renaming_switch t renaming)
  | Invalid t -> Invalid t

(* renaming for [Let] *)
and apply_renaming_let { let_abst; let_body } renaming : let_expr =
  let let_abst' =
    Name_abstraction.apply_renaming
      (module Bound_pattern)
      let_abst renaming
      ~apply_renaming_to_term:apply_renaming
  in
  let defining_expr' = apply_renaming let_body renaming in
  { let_abst = let_abst'; let_body = defining_expr' }

and apply_renaming_named t renaming : named =
  match t with
  | Simple simple ->
    Simple (Simple.apply_renaming simple renaming)
  | Prim prim ->
    Prim (apply_renaming_prim prim renaming)
  | Set_of_closures set ->
    Set_of_closures (apply_renaming_set_of_closures set renaming)
  | Static_consts consts ->
    Static_consts (apply_renaming_static_const_group consts renaming)
  | Rec_info info ->
    Rec_info (Rec_info_expr.apply_renaming info renaming)

and apply_renaming_function_declarations
      ({ funs = _ ; in_order } : function_declarations) renaming :
  function_declarations =
  let in_order =
    Function_slot.Lmap.map_sharing
      (fun x ->
         match x with
         | Id code_id -> Id (Renaming.apply_code_id renaming code_id)
         | Exp e -> Exp (apply_renaming e renaming))
      in_order
  in
  { funs =
      Function_slot.Map.of_list (Function_slot.Lmap.bindings in_order);
    in_order}

and apply_renaming_set_of_closures
      ({ function_decls; value_slots; alloc_mode } as t : set_of_closures)
      renaming : set_of_closures =
  let alloc_mode' =
    Alloc_mode.For_allocations.apply_renaming alloc_mode renaming
  in
  let function_decls' =
    apply_renaming_function_declarations function_decls renaming
  in
  let changed = ref false in
  let value_slots' =
    Value_slot.Map.filter_map
      (fun var (simple, kind) ->
         if Renaming.value_slot_is_used renaming var
         then (
           let simple' = Simple.apply_renaming simple renaming in
           if not (simple == simple') then changed := true;
           Some (simple', kind))
         else (
           changed := true;
           None))
      value_slots
  in
  if alloc_mode == alloc_mode'
  && function_decls == function_decls'
  && not !changed
  then t
  else
    { function_decls = function_decls';
      value_slots = value_slots';
      alloc_mode = alloc_mode'
    }

and apply_renaming_prim t renaming : primitive =
  match t with
  | Nullary (Invalid _ | Optimised_out _ | Probe_is_enabled _ | Begin_region) ->
    t
  | Unary (prim, arg) ->
    let prim = P.apply_renaming_unary_primitive prim renaming in
    let arg = apply_renaming arg renaming in
    Unary (prim, arg)
  | Binary (prim, arg1, arg2) ->
    let prim = P.apply_renaming_binary_primitive prim renaming in
    let arg1 = apply_renaming arg1 renaming in
    let arg2 = apply_renaming arg2 renaming in
    Binary (prim, arg1, arg2)
  | Ternary (prim, arg1, arg2, arg3) ->
    let prim = P.apply_renaming_ternary_primitive prim renaming in
    let arg1 = apply_renaming arg1 renaming in
    let arg2 = apply_renaming arg2 renaming in
    let arg3 = apply_renaming arg3 renaming in
    Ternary (prim, arg1, arg2, arg3)
  | Variadic (prim, args) ->
    let prim = P.apply_renaming_variadic_primitive prim renaming in
    let args = List.map (fun x -> apply_renaming x renaming) args in
    Variadic (prim, args)

and apply_renaming_static_const_group t renaming : static_const_group =
  List.map (fun static_const ->
    apply_renaming_static_const_or_code static_const renaming) t

and apply_renaming_static_const_or_code t renaming : static_const_or_code =
  match t with
  | Code code ->
    Code (Code0.apply_renaming
            ~apply_renaming_function_params_and_body code renaming)
  | Deleted_code -> Deleted_code
  | Static_const const ->
    Static_const (apply_renaming_static_const const renaming)

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

and apply_renaming_function_params_and_body t renaming =
  Name_abstraction.apply_renaming
    (module Bound_for_function) t renaming ~apply_renaming_to_term:apply_renaming

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

and apply_renaming_recursive_let_expr {continuation_map; body} renaming
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
      { callee; continuation; exn_continuation; apply_args; call_kind}
      renaming:
  apply_expr =
  let continuation =
    Apply_expr.Result_continuation.apply_renaming continuation renaming in
  let exn_continuation =
    Renaming.apply_continuation renaming exn_continuation in
  let callee = apply_renaming callee renaming in
  let apply_args =
    List.map (fun x -> apply_renaming x renaming) apply_args in
  let call_kind = Call_kind.apply_renaming call_kind renaming in
  { callee = callee; continuation = continuation;
    exn_continuation = exn_continuation;
    apply_args = apply_args; call_kind = call_kind }

(* renaming for [Apply_cont] *)
and apply_renaming_apply_cont {k; args} renaming : apply_cont_expr =
  let k = Renaming.apply_continuation renaming k in
  let args = List.map (fun x -> apply_renaming x renaming) args in
  { k = k; args = args }

(* renaming for [Switch] *)
and apply_renaming_switch {scrutinee; arms} renaming : switch_expr =
  let scrutinee = apply_renaming scrutinee renaming in
  let arms = Targetint_31_63.Map.map (fun x -> apply_renaming x renaming) arms in
  { scrutinee = scrutinee; arms = arms }

(** Sexp-ish simple pretty-printer for [core_exp]s.
  Ignores name_stamp, compilation_unit, and debug_info for simplicity. **)
let rec print ppf e =
  fprintf ppf "(@[<hov 1>";
  (match e with
   | Named t ->
     fprintf ppf "named@ ";
     print_named ppf t;
   | Let t ->
     fprintf ppf "let@ ";
     print_let ppf t;
   | Let_cont t ->
     fprintf ppf "let_cont@ ";
     print_let_cont ppf t;
   | Apply t ->
     fprintf ppf "apply@ ";
     print_apply ppf t;
   | Apply_cont t ->
     fprintf ppf "apply_cont@ ";
     print_apply_cont ppf t;
   | Switch t ->
     fprintf ppf "switch@ ";
     print_switch ppf t;
   | Invalid { message } ->
     fprintf ppf "invalid %s" message);
  fprintf ppf "@])";

and print_let ppf ({let_abst; let_body} : let_expr) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_pattern)
    let_abst ~apply_renaming_to_term:apply_renaming
    ~f:(fun bound body ->
        fprintf ppf "(bound@ (%a),@ body@ (%a))@ in=%a"
        print_bound_pattern bound
        print let_body
        print body)

and print_bound_pattern ppf (t : Bound_pattern.t) =
  match t with
  | Singleton v ->
    fprintf ppf "singleton@ %a"
      Bound_var.print v
  | Set_of_closures v ->
    fprintf ppf "set_of_closures@ %a"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space
         Bound_var.print) v
  | Static v ->
    fprintf ppf "static@ %a"
      print_bound_static v

and print_bound_static ppf (t : Bound_static.t) =
  Format.fprintf ppf "@[<hov 0>%a@]"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space print_static_pattern)
    (t |> Bound_static.to_list)

and print_static_pattern ppf (t : Bound_static.Pattern.t) =
  match t with
  | Code v ->
    fprintf ppf "code@ %a" Code_id.print v
  | Set_of_closures v ->
    Format.fprintf ppf "set_of_closures@ %a"
      (Function_slot.Lmap.print Symbol.print) v
  | Block_like v ->
    Format.fprintf ppf "(block_like@ %a)" Symbol.print v

and print_named ppf (t : named) =
  match t with
  | Simple simple ->
    fprintf ppf "simple@ %a"
    Simple.print simple;
  | Prim prim ->
    fprintf ppf "prim@ %a"
    print_prim prim;
  | Set_of_closures clo ->
    fprintf ppf "set_of_closures@ %a"
    print_set_of_closures clo
  | Static_consts consts ->
    fprintf ppf "static_consts@ %a"
    print_static_const_group consts
  | Rec_info info ->
    fprintf ppf "rec_info@ %a"
    Rec_info_expr.print info

and print_set_of_closures ppf
      { function_decls;
        value_slots;
        alloc_mode; } =
  if Value_slot.Map.is_empty value_slots then
    Format.fprintf ppf "(%a@ \
                         %a)"
      Alloc_mode.For_allocations.print alloc_mode
      print_function_declaration function_decls
  else
    Format.fprintf ppf "(%a@ \
                        %a\
                        (env@ %a))"
      Alloc_mode.For_allocations.print alloc_mode
      print_function_declaration function_decls
      (Value_slot.Map.print print_value_slot) value_slots

and print_value_slot ppf (simple, kind) =
  Format.fprintf ppf "@[(%a @<1>\u{2237} %a)@]" Simple.print simple
    Flambda_kind.With_subkind.print kind

and print_function_declaration ppf { funs = _ ; in_order } =
  Format.fprintf ppf "(%a)"
    (Function_slot.Lmap.print
    (fun ppf x ->
       match x with
       | Id x -> Code_id.print ppf x
       | Exp x -> print ppf x))
    in_order

and print_prim ppf (t : primitive) =
  match t with
  | Nullary prim ->
    print_nullary_prim ppf prim
  | Unary (prim, arg) ->
    fprintf ppf "(%a, %a)"
     P.print_unary_primitive prim
     print arg
  | Binary (prim, arg1, arg2) ->
    fprintf ppf "(%a, %a, %a)"
    P.print_binary_primitive prim
    print arg1
    print arg2
  | Ternary (prim, arg1, arg2, arg3) ->
    fprintf ppf "(%a, %a, %a, %a)"
    P.print_ternary_primitive prim
    print arg1
    print arg2
    print arg3
  | Variadic (prim, args) ->
    fprintf ppf "(%a, %a)"
    P.print_variadic_primitive prim
    (Format.pp_print_list ~pp_sep: Format.pp_print_space print) args

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

and print_static_const_group ppf t =
  Format.pp_print_list ~pp_sep:Format.pp_print_space print_static_const_or_code ppf t

and print_static_const_or_code ppf t =
  match t with
  | Code code -> Code0.print ~print_function_params_and_body ppf code
  | Deleted_code -> fprintf ppf "deleted_code"
  | Static_const const -> print_static_const ppf const

and print_static_const ppf (t : static_const) : unit =
  match t with
  | Static_set_of_closures set ->
    fprintf ppf "(Set_of_closures %a)"
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

and print_function_params_and_body ppf (t:function_params_and_body) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_for_function) t
    ~apply_renaming_to_term:apply_renaming
    ~f:(fun bff expr ->
      fprintf ppf "ret: %a; exn: %a; %a"
        Continuation.print (Bound_for_function.return_continuation bff)
        Continuation.print (Bound_for_function.exn_continuation bff)
        print expr)

and print_let_cont ppf (t : let_cont_expr) =
  match t with
  | Non_recursive {handler; body} ->
    Name_abstraction.pattern_match_for_printing
      (module Bound_continuation) body
      ~apply_renaming_to_term:apply_renaming
      ~f:(fun cont body ->
        Name_abstraction.pattern_match_for_printing
          (module Bound_parameters) handler
          ~apply_renaming_to_term:apply_renaming
          ~f:(fun k let_body ->
            fprintf ppf "(cont@ %a,@ param@ %a,@ body@ %a)@ in=%a"
            print_cont cont
            print_params k
            print let_body
            print body))
  | Recursive t ->
    fprintf ppf "rec@ ";
    Name_abstraction.pattern_match_for_printing
      (module Bound_continuations) t
      ~apply_renaming_to_term:apply_renaming_recursive_let_expr
      ~f:(fun k body -> print_recursive_let_cont ppf k body)

and print_params ppf (k : Bound_parameters.t) =
  Format.fprintf ppf "@[<hov 0>%a@]"
    (Format.pp_print_list ~pp_sep:Format.pp_print_space print_param)
    (k |> Bound_parameters.to_list)

and print_param ppf (k : Bound_parameter.t) =
  fprintf ppf "%s" (Bound_parameter.var k |> Variable.name)

and print_cont ppf (k : Bound_continuation.t) =
  fprintf ppf "%s" (Continuation.name k)

and print_recursive_let_cont ppf (k : Bound_continuations.t)
      ({continuation_map; body} : recursive_let_expr) =
  fprintf ppf "[@ %a@ ] " Bound_continuations.print k;
  Name_abstraction.pattern_match_for_printing
    (module Bound_parameters) continuation_map
    ~apply_renaming_to_term:apply_renaming_cont_map
    ~f:(fun k body ->
      fprintf ppf "(%a)\n" Bound_parameters.print k;
      Continuation.Map.iter (print_continuation_handler ppf) body;
    );
  fprintf ppf "@ in\n %a" print body

and print_continuation_handler ppf key (t : continuation_handler) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_parameters) t
    ~apply_renaming_to_term:apply_renaming
    ~f:(fun k body ->
      fprintf ppf "%s: fun %a -> %a"
        (Continuation.name key)
        Bound_parameters.print k print body)

and print_apply ppf
      ({callee; continuation; exn_continuation; apply_args; _} : apply_expr) =
  fprintf ppf "%a %a %a "
    print callee
    Apply_expr.Result_continuation.print continuation
    Continuation.print exn_continuation;
  Format.pp_print_list ~pp_sep:Format.pp_print_space print ppf apply_args

and print_apply_cont ppf ({k ; args} : apply_cont_expr) =
  fprintf ppf "%a@ " print_cont k;
  Format.pp_print_list ~pp_sep:Format.pp_print_space print ppf args

and print_switch ppf ({scrutinee; arms} : switch_expr) =
  fprintf ppf "switch %a :" print scrutinee;
  Targetint_31_63.Map.iter (print_arm ppf) arms

and print_arm ppf key arm =
  fprintf ppf "| %a -> %a\n"
    Targetint_31_63.print key
    print arm

(** [ids_for_export] is the set of bound variables for a given expression **)
let rec ids_for_export (t : core_exp) =
  match t with
  | Named t -> ids_for_export_named t
  | Let t -> ids_for_export_let t
  | Let_cont t -> ids_for_export_let_cont t
  | Apply t -> ids_for_export_apply t
  | Apply_cont t -> ids_for_export_apply_cont t
  | Switch t -> ids_for_export_switch t
  | Invalid _ -> Ids_for_export.empty

(* ids for [Let_expr] *)
and ids_for_export_let { let_abst; let_body } =
  let body_ids = ids_for_export let_body in
  let let_abst_ids =
    Name_abstraction.ids_for_export
      (module Bound_pattern)
      let_abst ~ids_for_export_of_term:ids_for_export
  in
  Ids_for_export.union body_ids let_abst_ids

and ids_for_export_named (t : named) =
  match t with
  | Simple simple -> Ids_for_export.from_simple simple
  | Prim prim -> ids_for_export_prim prim
  | Set_of_closures set -> ids_for_export_set_of_closures set
  | Static_consts consts -> ids_for_export_static_const_group consts
  | Rec_info info -> Rec_info_expr.ids_for_export info

and ids_for_export_function_decls {funs ; in_order = _} =
  Function_slot.Map.fold
    (fun _function_slot fn_expr ids ->
       match fn_expr with
       | Id code_id -> Ids_for_export.add_code_id ids code_id
       | Exp exp -> Ids_for_export.union (ids_for_export exp) ids
    )
    funs Ids_for_export.empty

and ids_for_export_set_of_closures
      ({function_decls; value_slots; alloc_mode} : set_of_closures) =
  let function_decls_ids = ids_for_export_function_decls function_decls
  in
  Ids_for_export.union
    (Value_slot.Map.fold
       (fun _value_slot (simple, _kind) ids ->
          Ids_for_export.add_simple ids simple)
       value_slots function_decls_ids)
    (Alloc_mode.For_allocations.ids_for_export alloc_mode)

and ids_for_export_prim (t : primitive) =
  match t with
  | Nullary (Invalid _ | Optimised_out _ | Probe_is_enabled _ | Begin_region) ->
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
    Code0.ids_for_export ~ids_for_export_function_params_and_body code
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

and ids_for_export_function_params_and_body abst =
  Name_abstraction.ids_for_export
    (module Bound_for_function) abst
    ~ids_for_export_of_term:ids_for_export

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

and ids_for_export_recursive_let_expr ({continuation_map; body} : recursive_let_expr) =
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
      { callee; continuation; exn_continuation; apply_args; call_kind } =
  let callee_ids = ids_for_export callee in
  let callee_and_args_ids =
    List.fold_left
      (fun ids arg -> Ids_for_export.union ids (ids_for_export arg))
       callee_ids apply_args in
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
  type t = let_expr
  let create ~(x : Bound_pattern.t) ~(e1 : core_exp) ~(e2 : core_exp)  =
    Let { let_abst = A.create x e2; let_body = e1 }

  module Pattern_match_pair_error = struct
    type t = Mismatched_let_bindings
  end

  let pattern_match t ~(f : x:Bound_pattern.t -> e1:core_exp -> e2:core_exp -> 'a) : 'a =
    let open A in
    let<> x, e2 = t.let_abst in
    f ~x ~e1:t.let_body ~e2

  (* Treat "dynamic binding" (statically scoped binding under lambda abstraction)
     and "static binding" (globally scoped mapping of statics) differently *)
  let pattern_match_pair
        ({let_abst = let_abst1; let_body = _})
        ({let_abst = let_abst2; let_body = _})
        (dynamic : Bound_pattern.t -> core_exp -> core_exp -> 'a)
        (static : Bound_static.t -> Bound_static.t -> core_exp -> core_exp -> 'a):
    ('a, Pattern_match_pair_error.t) Result.t =
    A.pattern_match let_abst1 ~f:(fun let_bound1 let_body1 ->
      A.pattern_match let_abst2 ~f:(fun let_bound2 let_body2 ->
        let dynamic_case () =
          let ans = A.pattern_match_pair let_abst1 let_abst2 ~f:dynamic
          in Ok ans
        in
        match let_bound1, let_bound2 with
        | Bound_pattern.Singleton _, Bound_pattern.Singleton _ -> dynamic_case ()
        | Set_of_closures vars1, Set_of_closures vars2 ->
          if List.compare_lengths vars1 vars2 = 0
          then dynamic_case ()
          else Error Pattern_match_pair_error.Mismatched_let_bindings
        | Static bound_static1, Static bound_static2 ->
          let patterns1 = bound_static1 |> Bound_static.to_list in
          let patterns2 = bound_static2 |> Bound_static.to_list in
          if List.compare_lengths patterns1 patterns2 = 0
          then
            let ans = static bound_static1 bound_static2 let_body1 let_body2 in
            Ok ans
          else Error Pattern_match_pair_error.Mismatched_let_bindings
        | (Singleton _ | Set_of_closures _ | Static _), _ ->
            Error Pattern_match_pair_error.Mismatched_let_bindings
      )
    )
end

module Core_continuation_handler = struct
  module A = Name_abstraction.Make (Bound_parameters) (T0)
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
  module A = Name_abstraction.Make (Bound_continuation) (T0)
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
  let pattern_match_pair = A.pattern_match_pair
end

module Core_recursive = struct
  module A = Name_abstraction.Make (Bound_continuations) (RecursiveLetExpr)
  type t = (Bound_continuations.t, recursive_let_expr) Name_abstraction.t

  let create = A.create
  let pattern_match_pair (t1 : A.t) (t2 : A.t)
    (f : Bound_parameters.t ->
         core_exp ->
         core_exp -> continuation_handler_map -> continuation_handler_map -> 'a)
    = A.pattern_match_pair t1 t2
        ~f:(fun (_:Bound_continuations.t)
                (t1 : recursive_let_expr)
                (t2 : recursive_let_expr) ->
          let body1 = t1.body in
          let body2 = t2.body in
          Core_continuation_map.pattern_match_pair
            t1.continuation_map t2.continuation_map
            ~f:(fun params h1 h2 -> f params body1 body2 h1 h2))
end

module Core_function_params_and_body = struct
  module A = Name_abstraction.Make (Bound_for_function) (T0)
  type t = (Bound_for_function.t, T0.t) Name_abstraction.t
  let create = A.create

  let pattern_match_pair t1 t2 ~f =
    A.pattern_match_pair t1 t2
      ~f:(fun
           bound_for_function body1 body2
           -> f ~return_continuation:
                 (Bound_for_function.return_continuation bound_for_function)
                ~exn_continuation:
                  (Bound_for_function.exn_continuation bound_for_function)
                (Bound_for_function.params bound_for_function)
                ~body1 ~body2
                ~my_closure:(Bound_for_function.my_closure bound_for_function)
                ~my_region:(Bound_for_function.my_region bound_for_function)
                ~my_depth:(Bound_for_function.my_depth bound_for_function))
end

module Core_code = struct
  type t = function_params_and_body Code0.t

  let code_metadata = Code0.code_metadata

  let params_and_body = Code0.params_and_body

  module Metadata_view = struct
    type nonrec 'a t = t

    let metadata = code_metadata
  end

  include Code_metadata.Code_metadata_accessors [@inlined hint] (Metadata_view)

  let create_with_metadata =
    Code0.create_with_metadata
      ~print_function_params_and_body:print_function_params_and_body
end
