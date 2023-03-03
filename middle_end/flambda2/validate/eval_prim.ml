open! Flambda2_core
module P = Flambda_primitive
open! Translate

let eval_nullary (_v : P.nullary_primitive) : named =
  failwith "[Primitive eval] eval_nullary"

let eval_unary (v : P.unary_primitive) (arg : core_exp) : named =
  match v with
  | Untag_immediate ->
    (match arg with
     | Named (Prim (Unary (Tag_immediate, Named (Prim (Unary (Is_int a, e)))))) ->
       (Prim (Unary (Is_int a, e)))
     | _ -> (Prim (Unary (v, arg))))
  | (Get_tag | Array_length | Int_as_pointer | Boolean_not
    | Reinterpret_int64_as_float | Tag_immediate
    | Is_boxed_float | Is_flat_float_array | Begin_try_region
    | End_region | Obj_dup | Duplicate_block _ | Duplicate_array _
    | Is_int _ | Bigarray_length _ | String_length _
    | Opaque_identity _ | Int_arith (_,_) | Float_arith _
    | Num_conv _ | Unbox_number _ | Box_number (_, _)
    | Project_function_slot _ | Project_value_slot _) ->
    (Prim (Unary (v, arg)))

let simple_tagged_immediate ~(const : Simple.t) : Targetint_31_63.t option =
  let constant =
    Simple.pattern_match' const
    ~var:(fun _ ~coercion:_ -> Misc.fatal_error "No variables allowed")
    ~symbol:(fun _ ~coercion:_ -> Misc.fatal_error "No symbols allowed")
    ~const:(fun t -> t)
  in
  match Int_ids.Const.descr constant with
  | Tagged_immediate i -> Some i
  | _ -> None

let eval_binary
      (v : P.binary_primitive) (arg1 : core_exp) (arg2 : core_exp) : core_exp =
  match v with
  | Block_load (Values {tag = Known _; size = _; field_kind = _},
                (Immutable | Immutable_unique)) ->
    (* [arg1] is the block, and [arg2] is the index *)
    (match arg1, arg2 with
     | Named (Static_consts blocks), Named (Simple n) ->
       (* If we can inspect the index, then we can load from the immutable block *)
       if Simple.is_const n then
         (let index = simple_tagged_immediate ~const:n in
          match index with (* TODO: Match on the tags and size? *)
          | Some i -> (* IY: Doublecheck loading scheme from blocks *)
            (match List.nth blocks 0 with
             | Static_const (Block (_, _, l)) ->
               List.nth l (Targetint_31_63.to_int i)
             | _ -> failwith "[Primitive eval] Unimplemented_block_load")

          | None -> Named (Prim (Binary (v, arg1, arg2))))
       else
         Named (Prim (Binary (v, arg1, arg2)))
     | Named (Prim (Variadic (Make_block (_, Immutable, _), blocks))),
       Named (Simple n) ->
       if Simple.is_const n then
         (let index = simple_tagged_immediate ~const:n in
          match index with (* TODO: Match on the tags and size? *)
          | Some i ->
            (match List.nth blocks (Targetint_31_63.to_int i) with
             | Named n -> Named n
             | _ -> Misc.fatal_error "Non-name load")
          | None -> Named (Prim (Binary (v, arg1, arg2))))
       else
         Named (Prim (Binary (v, arg1, arg2)))
     | _, _ -> Named (Prim (Binary (v, arg1, arg2))))
  | Block_load (Naked_floats _, (Immutable | Immutable_unique))
  | Block_load (_, _)
  | Array_load (_,_)
  | String_or_bigstring_load (_,_)
  | Bigarray_load (_,_,_)
  | Phys_equal _
  | Int_arith (_,_)
  | Int_shift (_,_)
  | Int_comp (_,_)
  | Float_arith _
  | Float_comp _ -> Named (Prim (Binary (v, arg1, arg2)))

let eval_ternary (_v : P.ternary_primitive)
      (_arg1 : core_exp) (_arg2 : core_exp) (_arg3 : core_exp) : named =
  failwith "[Primitive eval] eval_ternary"

let eval_variadic (v : P.variadic_primitive) (args : core_exp list) : named =
  match v with
  | Make_block (Values (tag, [kind]), _mut, _alloc_mode) ->
    (match args with
    | [Named (Simple n)] ->
      (* Reduce make block to immutable block *)
      (* LATER : generalize for taking in a list of arguments *)
      (match Flambda_kind.With_subkind.kind kind with
      | Value ->
          let constant =
            Simple.pattern_match' n
              ~var:(fun _ ~coercion:_ -> Misc.fatal_error "No variables allowed")
              ~symbol:(fun _ ~coercion:_ -> Misc.fatal_error "No symbols allowed")
              ~const:(fun t -> t)
          in
          (match Int_ids.Const.descr constant with
            | Tagged_immediate i ->
              let block = (Block (tag, Immutable, [tagged_immediate_to_core i]))
              in
              Static_consts [(Static_const block)]
            | (Naked_immediate _ | Naked_float _
              | Naked_int32 _ | Naked_int64 _ | Naked_nativeint _) ->
              failwith "[Primitive eval] Unimplemented constant")
        | (Naked_number _ | Region | Rec_info) ->
          failwith "[Primitive eval] Unimplemented_eval: making block for non-value kind")
    | _ -> Prim (Variadic (v, args)))
  | Make_block _ ->
    Prim (Variadic (v, args))
  | Make_array _ ->
    Misc.fatal_error "[Primitive eval]: eval_variadic_make_array_unspported"

let eval (v : primitive) : core_exp =
  match v with
  | Nullary v -> Named (eval_nullary v)
  | Unary (v, arg) -> Named (eval_unary v arg)
  | Binary (v, arg1, arg2) -> eval_binary v arg1 arg2
  | Ternary (v, arg1, arg2, arg3) -> Named (eval_ternary v arg1 arg2 arg3)
  | Variadic (v, args) -> Named (eval_variadic v args)
