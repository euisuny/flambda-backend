module P = Flambda_primitive
let fprintf = Format.fprintf

(** Simplified core of [flambda2] terms **)
(* (1) Simple.t -> core_exp for [Apply*] expessions
   (2) Ignore [Num_occurrences] (which is used for making inlining decisions)
   (3) Ignored traps for now *)

module Slot = Slot.Make (struct let colour _ = () end)

type core_exp =
  | Base of base_exp
  | Lambda of lambda_exp
  | Let of let_exp
  | LetCont of let_cont_expr
  | Apply of apply_exp
  | ApplyCont of apply_cont_exp
  | Switch of switch_exp
  | Invalid of { message : string }

and base_exp =
  | Simple of Simple.t
  | Numeric of numeric
  | Slot of (Variable.t * Slot.t)
  | Closure_exp of (Variable.t * Slot.t * set_of_closures)
  | Const of const
  | Prim of primitive
  | Set_of_closures of set_of_closures
  | Rec_info of Rec_info_expr.t

and numeric =
  | Float of Numeric_types.Float_by_bit_pattern.t
  | Int32 of Int32.t
  | Int64 of Int64.t
  | NativeInt of Targetint_32_64.t
  | Immediate of Targetint_31_63.t

and set_of_closures =
  { function_decls : core_exp Slot.Lmap.t;
    value_slots : core_exp Slot.Lmap.t}

and primitive =
  | Nullary of P.nullary_primitive
  | Unary of P.unary_primitive * core_exp
  | Binary of P.binary_primitive * core_exp * core_exp
  | Ternary of P.ternary_primitive * core_exp * core_exp * core_exp
  | Variadic of P.variadic_primitive * core_exp list

and const =
  | Block of Tag.Scannable.t * Mutability.t * core_exp list
  | Boxed_float of core_exp
  | Boxed_int32 of core_exp
  | Boxed_int64 of core_exp
  | Boxed_nativeint of core_exp
  | Immutable_float_block of core_exp list
  | Immutable_float_array of core_exp list
  | Immutable_value_array of core_exp list
  | Empty_array
  | Mutable_string of { initial_value : string }
  | Immutable_string of string

(** Let expessions [let x = e1 in e2]

    [fun x -> e2] = let_abst
    [e1] = body **)
and let_exp =
  { let_abst : (Bound_parameters.t, core_exp) Name_abstraction.t;
    (* Can have multiple in the case of a recursive let binding *)
    exp_body : core_exp list; }

and lambda_exp = (Bound_parameters.t, core_exp) Name_abstraction.t

and let_cont_expr =
  (* Non-recursive case [e1 where k x = e2]
     [fun x -> e2] = handler
     bound variable [k] = Bound_continuation.t
     [e1] = body (has bound variable [k] in scope) *)
  | Non_recursive of
    { handler : lambda_exp;
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
  { handlers : lambda_exp Continuation.Map.t;
    body : core_exp; }

and apply_exp =
  { callee: core_exp;
    continuation: core_exp;
    exn_continuation: core_exp;
    apply_args: core_exp list; }

and apply_cont_exp =
  { k : core_exp;
    args : core_exp list }

and switch_exp =
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

let must_be_base_exp (e : core_exp) : base_exp option =
  match e with
  | Base n -> Some n
  | (Let _ | LetCont _ | Apply _ | ApplyCont _ | Lambda _ | Switch _) -> None

let must_be_prim (e : core_exp) : primitive option =
  match must_be_base_exp e with
  | Some e ->
    (match e with
     | Prim e -> Some e
     | (Simple _ | Closure_exp _ | Set_of_closures _ | Const _
       | Numeric _ | Slot _ | Rec_info _) -> None)
  | None -> None

let must_be_simple (e : core_exp) : Simple.t option =
  match e with
  | Base (Simple s) -> Some s
  | (Base (Slot _ | Prim _ | Closure_exp _ | Set_of_closures _ |
            Const _ | Rec_info _)
    | Let _ | Apply _ | ApplyCont _ | Lambda _ | Switch _) -> None

let must_be_lambda (e : core_exp) : lambda_exp option =
  match e with
  | Lambda e -> Some e
  | (Base _ | Let _ | Apply _ | ApplyCont _ | Switch _
    | Invalid _) -> None

let must_be_apply (e : core_exp) : apply_exp option =
  match e with
  | Apply e -> Some e
  | (Base _ | Let _ | Lambda _ | ApplyCont _ | Switch _
    | Invalid _) -> None

let must_be_simple_or_immediate (e : base_exp) : Simple.t option =
  match e with
  | Simple s -> Some s
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
     Slot _ | Closure_exp _
    | Set_of_closures _ | Const _ | Rec_info _) -> None

let must_be_simple_or_immediate (e : core_exp) : Simple.t option =
  match must_be_base_exp e with
  | Some n -> must_be_simple_or_immediate n
  | None -> None

let must_be_tagged_immediate (e : base_exp) : base_exp option =
  match e with
  | Prim (Unary (Tag_immediate, arg)) -> must_be_base_exp arg
  | Prim (Unary
            ((Untag_immediate | Duplicate_block _ | Duplicate_array _ | Is_int _
             | Get_tag | Array_length | Bigarray_length _ | String_length _
             | Int_as_pointer | Opaque_identity _ | Int_arith _ | Float_arith _
             | Num_conv _ | Boolean_not | Reinterpret_int64_as_float | Unbox_number _
             | Box_number _ | Project_function_slot _ | Project_value_slot _
             | Is_boxed_float | Is_flat_float_array | Begin_try_region | End_region
             | Obj_dup), _))
  | (Prim (Nullary _ | Binary  _ | Ternary _ | Variadic _) |
     Closure_exp _ | Set_of_closures _ | Const _
    | Rec_info _) -> None

let must_be_tagged_immediate (e : core_exp) : base_exp option =
  match must_be_base_exp e with
  | Some n -> must_be_tagged_immediate n
  | None -> None

let must_be_untagged_immediate (e : base_exp) : base_exp option =
  match e with
  | Prim (Unary (Untag_immediate, arg)) -> must_be_base_exp arg
  | Prim (Unary
            ((Tag_immediate | Duplicate_block _ | Duplicate_array _ | Is_int _
             | Get_tag | Array_length | Bigarray_length _ | String_length _
             | Int_as_pointer | Opaque_identity _ | Int_arith _ | Float_arith _
             | Num_conv _ | Boolean_not | Reinterpret_int64_as_float | Unbox_number _
             | Box_number _ | Project_function_slot _ | Project_value_slot _
             | Is_boxed_float | Is_flat_float_array | Begin_try_region | End_region
             | Obj_dup), _))
  | (Prim (Nullary _ | Binary  _ | Ternary _ | Variadic _)
    | Closure_exp _ | Set_of_closures _ | Const _
    | Rec_info _ ) -> None

let must_be_untagged_immediate (e : core_exp) : base_exp option =
  match must_be_base_exp e with
  | Some n -> must_be_untagged_immediate n
  | None -> None

let must_be_string_length (e : base_exp) : (Flambda_primitive.string_or_bytes * core_exp) option =
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
  | (Prim (Nullary _ | Binary  _ | Ternary _ | Variadic _)
    | Closure_exp _ | Set_of_closures _ | Const _ | Rec_info _) -> None

let must_be_string_length (e : core_exp) : (Flambda_primitive.string_or_bytes * core_exp) option =
  match must_be_base_exp e with
  | Some n -> must_be_string_length n
  | None -> None

let must_be_slot (e : core_exp) : (Variable.t * Slot.t) option =
  match must_be_base_exp e with
  | Some (Slot v) -> Some v
  | (Some (Simple _) | None) -> None

let must_be_slot_exp (e : base_exp) :
  (Variable.t * Slot.t) option =
  match e with
  | Slot (phi, slot) -> Some (phi, slot)
  | (Simple _) -> None

let must_be_slot_exp (e : core_exp) :
  (Variable.t * Slot.t) option =
  match must_be_base_exp e with
  | Some n -> must_be_slot_exp n
  | None -> None

let must_be_set_of_closures (e : base_exp) =
  match e with
  | Set_of_closures e -> Some e
  | (Prim _ | Closure_exp _ | Const _ | Rec_info _) ->
    None

let must_be_set_of_closures (e : core_exp) =
  match must_be_base_exp e with
  | Some n -> must_be_set_of_closures n
  | None -> None

let must_have_closure (e : base_exp) : set_of_closures option =
  match e with
  | (Closure_exp (_, _, clo) | Set_of_closures clo) -> Some clo
  | (Prim _ | Const _ | Rec_info _) -> None

let must_have_closure (e : core_exp) =
  match must_be_base_exp e with
  | Some n -> must_have_closure n
  | None -> None

(** Nominal renaming for [core_exp] **)
let rec apply_renaming t renaming : core_exp =
  match t with
  | Base t -> Base (apply_renaming_base_exp t renaming)
  | Let t -> Let (apply_renaming_let t renaming)
  | Apply t -> Apply (apply_renaming_apply t renaming)
  | ApplyCont t -> ApplyCont (apply_renaming_apply_cont t renaming)
  | Lambda t -> Lambda (apply_renaming_lambda t renaming)
  | Switch t -> Switch (apply_renaming_switch t renaming)
  | Invalid t -> Invalid t

and apply_renaming_lambda t renaming : lambda_exp =
  Name_abstraction.apply_renaming (module Bound_parameters) t renaming
    ~apply_renaming_to_term:apply_renaming

(* renaming for [Let] *)
and apply_renaming_let { let_abst; exp_body } renaming : let_exp =
  let let_abst' =
    Name_abstraction.apply_renaming
      (module Bound_parameters)
      let_abst renaming
      ~apply_renaming_to_term:apply_renaming
  in
  let defining_exp' =
    Misc.Stdlib.List.map_sharing
      (fun x -> apply_renaming x renaming) exp_body in
  { let_abst = let_abst'; exp_body = defining_exp' }

and apply_renaming_base_exp t renaming : base_exp =
  match t with
  | Simple simple ->
    Simple (Simple.apply_renaming simple renaming)
  | Slot (var, slot) ->
    Slot (Renaming.apply_variable renaming var, slot)
  | Prim prim ->
    Prim (apply_renaming_prim prim renaming)
  | Closure_exp (var, slot, set) ->
    Closure_exp
      (Renaming.apply_variable renaming var,
       slot, apply_renaming_set_of_closures set renaming)
  | Set_of_closures set ->
    Set_of_closures (apply_renaming_set_of_closures set renaming)
  | Const const ->
    Const (apply_renaming_const const renaming)
  | Rec_info info ->
    Rec_info (Rec_info_expr.apply_renaming info renaming)

and apply_renaming_set_of_closures
      ({ function_decls; value_slots } as t : set_of_closures)
      renaming : set_of_closures =
  let changed = ref false in
  let apply_renaming_slots slots =
    Slot.Lmap.filter_map
      (fun _ exp ->
        let simple' = apply_renaming exp renaming in
        if not (exp == simple') then changed := true;
        Some simple')
      slots
  in
  let function_decls = apply_renaming_slots function_decls in
  let value_slots = apply_renaming_slots value_slots in
  if not !changed
  then t
  else
    { function_decls; value_slots }

and apply_renaming_prim t renaming : primitive =
  match t with
  | Nullary (Invalid _ | Optimised_out _ | Probe_is_enabled _ | Begin_region
            | Enter_inlined_apply _) ->
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

and apply_renaming_const t renaming =
  if Renaming.is_empty renaming
  then t
  else
    match t with
    | Block (tag, mut, fields) ->
      Block (tag, mut,
             Misc.Stdlib.List.map_sharing
              (fun field -> apply_renaming field renaming)
              fields)
    | Boxed_float exp ->
      Boxed_float (apply_renaming exp renaming)
    | Boxed_int32 exp ->
      Boxed_int32 (apply_renaming exp renaming)
    | Boxed_int64 exp ->
      Boxed_int64 (apply_renaming exp renaming)
    | Boxed_nativeint exp ->
      Boxed_nativeint (apply_renaming exp renaming)
    | Mutable_string { initial_value = _ } | Immutable_string _ -> t
    | Immutable_float_block fields ->
      Immutable_float_block
        (Misc.Stdlib.List.map_sharing
          (fun exp -> apply_renaming exp renaming) fields)
    | Immutable_float_array fields ->
      Immutable_float_array
        (Misc.Stdlib.List.map_sharing
          (fun exp -> apply_renaming exp renaming) fields)
    | Immutable_value_array fields ->
      Immutable_value_array
        (Misc.Stdlib.List.map_sharing
           (fun exp -> apply_renaming exp renaming) fields)
    | Empty_array -> Empty_array

(* renaming for [Apply] *)
and apply_renaming_apply
      { callee; continuation; exn_continuation; apply_args}
      renaming:
  apply_exp =
  let continuation = apply_renaming continuation renaming in
  let exn_continuation = apply_renaming exn_continuation renaming in
  let callee = apply_renaming callee renaming in
  let apply_args =
    List.map (fun x -> apply_renaming x renaming) apply_args in
  { callee = callee; continuation = continuation;
    exn_continuation = exn_continuation;
    apply_args = apply_args }

(* renaming for [ApplyCont] *)
and apply_renaming_apply_cont {k; args} renaming : apply_cont_exp =
  let k = apply_renaming k renaming in
  let args = List.map (fun x -> apply_renaming x renaming) args in
  { k = k; args = args }

(* renaming for [Switch] *)
and apply_renaming_switch {scrutinee; arms} renaming : switch_exp =
  let scrutinee = apply_renaming scrutinee renaming in
  let arms = Targetint_31_63.Map.map (fun x -> apply_renaming x renaming) arms in
  { scrutinee = scrutinee; arms = arms }

(** Sexp-ish simple pretty-printer for [core_exp]s.
  Ignores name_stamp, compilation_unit, and debug_info for simplicity. **)
let rec print ppf e =
  match e with
   | Base t ->
     fprintf ppf "@[<hov 1>(BASE_EXP %a)@]"
     print_base_exp t
   | Let t -> print_let ppf t
   | Apply t ->
     fprintf ppf "@[<hov 1>apply %a@]"
     print_apply t
   | Lambda t ->
     fprintf ppf "@[<hov 1>λ@ %a@]"
     print_lambda t
   | ApplyCont t ->
     fprintf ppf "@[<hov 1>apply_cont %a@]"
       print_apply_cont t
   | Switch t ->
     fprintf ppf "@[<hov 1>switch %a@]"
     print_switch t
   | Invalid { message } ->
     fprintf ppf "@[<hov 1>invalid %s@]" message

and print_lambda ppf t =
  Name_abstraction.pattern_match_for_printing
    (module Bound_parameters)
    t ~apply_renaming_to_term:apply_renaming
    ~f:(fun bound body ->
      fprintf ppf "%a ->@.   @[<hov 1>%a@]"
        Bound_parameters.print bound
        print body)

and print_let ppf ({let_abst; exp_body} : let_exp) =
  Name_abstraction.pattern_match_for_printing
    (module Bound_parameters)
    let_abst ~apply_renaming_to_term:apply_renaming
    ~f:(fun bound body ->
      match exp_body with
      | [b] ->
        fprintf ppf
          "@[<v 0>@[<hov 1>let (%a) =@ %a@]@;%a@]"
          Bound_parameters.print bound
          print b
          print body
      | [] -> ()
      | _::_ ->
        let bindings =
          List.combine (Bound_parameters.to_list bound) exp_body
        in
        let (var, e) = List.hd bindings in
        let bindings = List.tl bindings in
        fprintf ppf "@[<v 0>@[<hov 1>let rec %a = @ %a@]@."
          Bound_parameter.print var
          print e;
        List.map (fun (var, e) ->
          fprintf ppf "@[<hov 1>and %a = %a@]"
            Bound_parameter.print var
            print e) bindings;
        fprintf ppf "%a@]" print body)

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

and print_base_exp ppf (t : base_exp) =
  match t with
  | Simple simple ->
    fprintf ppf "simple %a"
      Simple.print simple
  | Slot (var, slot) ->
    fprintf ppf "slot(%a, %a)"
      Variable.print var
      Slot.print slot
  | Prim prim -> print_prim ppf prim;
  | Closure_exp (var, slot, clo) ->
    fprintf ppf "@[<hov 3>clo(%a,@ %a,@. %a)@]"
      Variable.print var
      Slot.print slot
      (fun ppf clo ->
         print_base_exp ppf (Set_of_closures clo)) clo
  | Set_of_closures clo ->
    fprintf ppf "set_of_closures@. @[<hov 2>%a@]"
    print_set_of_closures clo
  | Const const ->
    fprintf ppf "@[<hov 0>%a@]" print_static_const const
  | Rec_info info ->
    fprintf ppf "rec_info %a"
      Rec_info_expr.print info

and print_set_of_closures ppf
      { function_decls;
        value_slots } =
  if Slot.Lmap.is_empty value_slots then
    Format.fprintf ppf "(%a)"
      print_function_declaration function_decls
  else
    Format.fprintf ppf "(%a@.(env %a))"
      print_function_declaration function_decls
      (Slot.Lmap.print print_value_slot) value_slots

and print_value_slot ppf value =
  Format.fprintf ppf "@[(%a)@]" print value

and print_function_declaration ppf in_order =
  Format.fprintf ppf "(%a)"
    (Slot.Lmap.print print) in_order

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

and print_static_const ppf (t : const) : unit =
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
  | Boxed_float exp ->
    fprintf ppf "(Boxed_float@ %a)" print exp
  | Boxed_int32 exp ->
    fprintf ppf "(Boxed_int32@ %a)" print exp
  | Boxed_int64 exp ->
    fprintf ppf "(Boxed_int64@ %a)" print exp
  | Boxed_nativeint exp ->
    fprintf ppf "(Boxed_nativeint@ %a)" print exp
  | Immutable_float_block fields ->
    fprintf ppf "(Immutable_float_block@ %a)"
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "@; ") print)
      fields
  | Immutable_float_array fields ->
    fprintf ppf "(Immutable_float_array@ [| %a |])"
      (Format.pp_print_list
        ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "@; ")
        print)
      fields
  | Immutable_value_array fields ->
    fprintf ppf "(Immutable_value_array@ (%a))"
      (Format.pp_print_list ~pp_sep:Format.pp_print_space
        print) fields
  | Empty_array ->
    fprintf ppf "Empty_array"
  | Mutable_string { initial_value = s; } ->
    fprintf ppf "(Mutable_string@ %S)"
      s
  | Immutable_string s ->
    fprintf ppf "(Immutable_string@ %S)"
      s

and print_apply ppf
      ({callee; continuation; exn_continuation; apply_args} : apply_exp) =
  fprintf ppf "(callee:@[<hov 2>%a@])@ (ret:%a)@ (exn:%a)@ "
    print callee
    print continuation
    print exn_continuation;
  fprintf ppf " (args:";
  Format.pp_print_list ~pp_sep:Format.pp_print_space print ppf apply_args;
  fprintf ppf ")"

and print_apply_cont ppf ({k ; args} : apply_cont_exp) =
  fprintf ppf "(%a)@ "
    print k;
    fprintf ppf " (args:";
    Format.pp_print_list ~pp_sep:Format.pp_print_space print ppf args;
  fprintf ppf ")"

and print_switch ppf ({scrutinee; arms} : switch_exp) =
  fprintf ppf "(%a) with @ @[<v 0>" print scrutinee;
  Targetint_31_63.Map.iter (print_arm ppf) arms;
  fprintf ppf "@]"

and print_arm ppf key arm =
  fprintf ppf "@[<hov 2>@[<hov 0>| %a -> @]%a@]@ "
    Targetint_31_63.print key
    print arm

(** [ids_for_export] is the set of bound variables for a given expession **)
let rec ids_for_export (t : core_exp) =
  match t with
  | Base t -> ids_for_export_base_exp t
  | Let t -> ids_for_export_let t
  | Apply t -> ids_for_export_apply t
  | ApplyCont t -> ids_for_export_apply_cont t
  | Lambda t -> ids_for_export_lambda t
  | Switch t -> ids_for_export_switch t
  | Invalid _ -> Ids_for_export.empty

(* ids for [Let_exp] *)
and ids_for_export_let { let_abst; exp_body } =
  let body_ids =
    (List.fold_left (fun acc x -> Ids_for_export.union (ids_for_export x) acc)
       Ids_for_export.empty exp_body) in
  let let_abst_ids =
    Name_abstraction.ids_for_export
      (module Bound_parameters)
      let_abst ~ids_for_export_of_term:ids_for_export
  in
  Ids_for_export.union body_ids let_abst_ids

and ids_for_export_base_exp (t : base_exp) =
  match t with
  | Simple simple ->
    Ids_for_export.from_simple simple
  | Slot (var, _) ->
    Ids_for_export.singleton_variable var
  | Closure_exp (var, _, set) ->
    Ids_for_export.add_variable
    (ids_for_export_set_of_closures set) var
  | Prim prim -> ids_for_export_prim prim
  | Set_of_closures set -> ids_for_export_set_of_closures set
  | Const const -> ids_for_export_const const
  | Rec_info info -> Rec_info_expr.ids_for_export info

and ids_for_export_function_decls funs =
  Slot.Lmap.fold
    (fun _function_slot fn_exp ids ->
       Ids_for_export.union (ids_for_export fn_exp) ids)
    funs Ids_for_export.empty

and ids_for_export_set_of_closures
      ({function_decls; value_slots} : set_of_closures) =
  let function_decls_ids =
    ids_for_export_function_decls function_decls
  in
  Slot.Lmap.fold
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
  | Boxed_float exp
  | Boxed_int32 exp
  | Boxed_int64 exp
  | Boxed_nativeint exp -> ids_for_export exp
  | Immutable_string _ -> Ids_for_export.empty
  | Immutable_float_block fields ->
    List.fold_left (fun acc x -> Ids_for_export.union (ids_for_export x) acc)
       Ids_for_export.empty fields
  | Immutable_float_array fields ->
    List.fold_left (fun acc x -> Ids_for_export.union (ids_for_export x) acc)
      Ids_for_export.empty fields
  | Immutable_value_array fields ->
    List.fold_left (fun acc x -> Ids_for_export.union (ids_for_export x) acc)
      Ids_for_export.empty fields
  | Empty_array -> Ids_for_export.empty

(* ids for [Apply] *)
and ids_for_export_apply
      { callee; continuation; exn_continuation; apply_args } =
  let callee_ids = ids_for_export callee in
  let callee_and_args_ids =
    List.fold_left
      (fun ids arg -> Ids_for_export.union ids (ids_for_export arg))
       callee_ids apply_args in
  let result_continuation_ids = ids_for_export continuation in
  let exn_continuation_ids = ids_for_export exn_continuation in
  (Ids_for_export.union
     callee_and_args_ids
    (Ids_for_export.union result_continuation_ids exn_continuation_ids))

(* ids for [ApplyCont] *)
and ids_for_export_apply_cont { k; args } =
  let continuation_ids = ids_for_export k in
  List.fold_left
    (fun ids arg -> Ids_for_export.union ids (ids_for_export arg))
    continuation_ids
    args

and ids_for_export_lambda t =
   Name_abstraction.ids_for_export
     (module Bound_parameters) t ~ids_for_export_of_term:ids_for_export

and ids_for_export_switch { scrutinee; arms } =
  let scrutinee_ids = ids_for_export scrutinee in
  Targetint_31_63.Map.fold
    (fun _discr action ids ->
        Ids_for_export.union ids (ids_for_export action))
    arms scrutinee_ids

(* Module definitions for [Name_abstraction]*)
module T0 = struct
  type t = core_exp list
  let apply_renaming (l : t) renaming =
    List.map (fun x -> apply_renaming x renaming) l
  let ids_for_export (l : t)  =
    List.fold_left (fun acc x -> Ids_for_export.union (ids_for_export x) acc)
      Ids_for_export.empty l
end

module Core_let = struct
  module A = Name_abstraction.Make (Bound_parameters) (T0)
  type t = let_exp
  let create ~(x : Bound_parameters.t) ~(e1 : core_exp) ~(e2 : core_exp list)  =
    Let { let_abst = A.create x e2; exp_body = e1 }

  module Pattern_match_pair_error = struct
    type t = Mismatched_let_bindings
  end

  let pattern_match t ~(f : x:Bound_parameters.t -> e1:core_exp -> e2:core_exp -> 'a) : 'a =
    let open A in
    let<> x, e2 = t.let_abst in
    f ~x ~e1:t.exp_body ~e2

  (* Treat "dynamic binding" (statically scoped binding under lambda abstraction)
     and "static binding" (globally scoped mapping of statics) differently *)
  let pattern_match_pair
        ({let_abst = let_abst1; exp_body = _})
        ({let_abst = let_abst2; exp_body = _})
        (dynamic : Bound_parameters.t -> core_exp -> core_exp -> 'a)
        (static : Bound_codelike.t -> Bound_codelike.t -> core_exp -> core_exp -> 'a):
    ('a, Pattern_match_pair_error.t) Result.t =
    A.pattern_match let_abst1 ~f:(fun let_bound1 exp_body1 ->
      A.pattern_match let_abst2 ~f:(fun let_bound2 exp_body2 ->
        let dynamic_case () =
          let ans = A.pattern_match_pair let_abst1 let_abst2 ~f:dynamic
          in Ok ans
        in
        match let_bound1, let_bound2 with
        | Bound_parameters.Singleton _, Bound_parameters.Singleton _ -> dynamic_case ()
        | Static bound_static1, Static bound_static2 ->
          let patterns1 = bound_static1 |> Bound_codelike.to_list in
          let patterns2 = bound_static2 |> Bound_codelike.to_list in
          if List.compare_lengths patterns1 patterns2 = 0
          then
            let ans = static bound_static1 bound_static2 exp_body1 exp_body2 in
            Ok ans
          else Error Pattern_match_pair_error.Mismatched_let_bindings
        | (Singleton _ | Static _), _ ->
            Error Pattern_match_pair_error.Mismatched_let_bindings
      )
    )
end

module Core_lambda = struct
  module A = Name_abstraction.Make (Bound_for_lambda) (T0)
  type t = lambda_exp

  let pattern_match x ~f =
    A.pattern_match x ~f:(fun b e -> f b e)

  let create = A.create

  let pattern_match_pair t1 t2 ~f =
    A.pattern_match_pair t1 t2
      ~f:(fun
           bound body1 body2
           -> f ~return_continuation:(bound.return_continuation)
                ~exn_continuation:(bound.exn_continuation)
                (bound.params) body1 body2)
end

(* Fixpoint combinator for core expessions *)
let let_fix (f : core_exp -> core_exp) {let_abst; exp_body} =
  Core_let.pattern_match {let_abst; exp_body}
    ~f:(fun ~x ~e1 ~e2 ->
      Core_let.create
        ~x
        ~e1:(f e1)
        ~e2:(f e2))

let apply_fix (f : core_exp -> core_exp)
      ({callee; continuation; exn_continuation; apply_args} : apply_exp) =
  Apply
    {callee = f callee;
     continuation = f continuation;
     exn_continuation = f exn_continuation;
     apply_args = List.map f apply_args;}

let apply_cont_fix (f : core_exp -> core_exp)
      ({k; args} : apply_cont_exp) =
  ApplyCont
    {k = f k;
     args = List.map f args}

let lambda_fix (f : core_exp -> core_exp) (e : lambda_exp) =
  Core_lambda.pattern_match e
    ~f:(fun b e ->
      Lambda (Core_lambda.create b (f e)))

let switch_fix (f : core_exp -> core_exp)
      ({scrutinee; arms} : switch_exp) =
  Switch
    {scrutinee = f scrutinee;
     arms = Targetint_31_63.Map.map f arms}

let set_of_closures_fix
      (fix : core_exp -> core_exp) {function_decls; value_slots} =
  let function_decls = Slot.Lmap.map fix function_decls in
  let value_slots = Slot.Lmap.map fix value_slots in
  {function_decls; value_slots}

let static_const_fix (fix : core_exp -> core_exp) (e : static_const) =
  match e with
  | Block (tag, mut, list) ->
    let list = List.map fix list in
    Block (tag, mut, list)
  | ( Boxed_float _ | Boxed_int32 _ | Boxed_int64 _ | Boxed_nativeint _
    | Immutable_float_block _ | Immutable_float_array _ | Immutable_value_array _
    | Empty_array | Mutable_string _ | Immutable_string _ ) -> e

let static_const_group_fix (fix : core_exp -> core_exp)
       (e : static_const_group) =
  Base (Const (List.map (static_const_fix fix) e))

let prim_fix (fix : core_exp -> core_exp) (e : primitive) =
  match e with
  | Nullary _ -> Base (Prim e)
  | Unary (p, e) ->
    Base (Prim (Unary (p, fix e)))
  | Binary (p, e1, e2) ->
    Base (Prim (Binary (p, fix e1, fix e2)))
  | Ternary (p, e1, e2, e3) ->
    Base (Prim (Ternary (p, fix e1, fix e2, fix e3)))
  | Variadic (p, list) ->
    Base (Prim (Variadic (p, List.map fix list)))

let base_exp_fix (fix : core_exp -> core_exp)
      (f : 'a -> base_exp -> core_exp) arg (e : base_exp) =
  match e with
  | Base l -> f arg l
  | Prim e -> prim_fix fix e
  | Closure_exp (phi, slot, clo) ->
    let {function_decls; value_slots} = set_of_closures_fix fix clo in
    Base (Closure_exp (phi, slot, {function_decls; value_slots}))
  | Set_of_closures clo ->
    let {function_decls; value_slots} = set_of_closures_fix fix clo in
    Base (Set_of_closures {function_decls; value_slots})
  | Const group ->
    static_const_group_fix fix group
  | Rec_info _ -> Base e

let rec core_fmap
  (f : 'a -> base_exp -> core_exp) (arg : 'a) (e : core_exp) : core_exp =
  match e with
  | Base e ->
    base_exp_fix (core_fmap f arg) f arg e
  | Let e ->
    let_fix (core_fmap f arg) e
  | Apply e ->
    apply_fix (core_fmap f arg) e
  | ApplyCont e ->
    apply_cont_fix (core_fmap f arg) e
  | Lambda e -> lambda_fix (core_fmap f arg) e
  | Switch e -> switch_fix (core_fmap f arg) e
  | Invalid _ -> e

let base_exp_contained (base1 : base_exp) (base2 : base_exp) : bool =
  match base1, base2 with
  | Simple simple1, Simple simple2 ->
    Simple.same simple1 simple2
  | Simple simple, Slot (phi, _) ->
    Simple.same (Simple.var phi) simple
  | Slot (_, slot1), Slot (_, slot2) ->
    Slot.equal slot1 slot2
  | (Slot (_, _)), _ -> false
