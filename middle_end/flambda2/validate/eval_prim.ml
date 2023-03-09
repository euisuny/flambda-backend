open! Flambda
open! Flambda2_core
module P = Flambda_primitive
open! Translate

module A = Number_adjuncts

let eval_nullary (v : P.nullary_primitive) : named =
  Prim (Nullary v)

let eval_unary (v : P.unary_primitive) (arg : core_exp) : named =
  match v with
  (* [Project_function_slot] and [Project_value_slot] is resolved during
     instantiating closures in the normalization process *)
  | Project_value_slot _ | Project_function_slot _ ->
    Prim (Unary (v, arg))
  | Int_arith _ -> failwith "Unimplemented int arith"
  | Untag_immediate ->
    (match arg with
     | Named (Prim (Unary (Tag_immediate, Named (Prim (Unary (Is_int a, e)))))) ->
       (Prim (Unary (Is_int a, e)))
     | _ -> (Prim (Unary (v, arg))))
  | ( Get_tag | Array_length | Int_as_pointer | Boolean_not
    | Reinterpret_int64_as_float | Tag_immediate
    | Is_boxed_float | Is_flat_float_array | Begin_try_region
    | End_region | Obj_dup | Duplicate_block _ | Duplicate_array _
    | Is_int _ | Bigarray_length _ | String_length _
    | Opaque_identity _ | Float_arith _
    | Num_conv _ | Unbox_number _ | Box_number (_, _)) ->
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

let eval_block_load v arg1 arg2 =
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

module K = Flambda_kind
module T = Flambda2_types

type 'a binary_arith_outcome_for_one_side_only =
  | Exactly of 'a
  | The_other_side
  | Negation_of_the_other_side
  (* | Float_negation_of_the_other_side *)
  | Cannot_simplify
  | Invalid

module type Binary_arith_like_sig = sig
  module Lhs : Container_types.S

  module Rhs : Container_types.S

  module Pair : Container_types.S with type t = Lhs.t * Rhs.t

  module Result : Container_types.S

  val cross_product : Lhs.Set.t -> Rhs.Set.t -> Pair.Set.t

  val arg_kind : K.Standard_int_or_float.t

  val result_kind : K.t

  val term : Result.t -> Flambda2_core.named

  val to_lhs_elem : Simple.t -> Lhs.t option

  val to_rhs_elem : Simple.t -> Rhs.t option

  val prover_lhs : T.Typing_env.t -> T.t -> Lhs.Set.t T.meet_shortcut

  val prover_rhs : T.Typing_env.t -> T.t -> Rhs.Set.t T.meet_shortcut

  type op

  val unknown : op -> T.t

  val these : Result.Set.t -> T.t

  val op : op -> Lhs.t -> Rhs.t -> Result.t option

  val op_lhs_unknown :
    op -> rhs:Rhs.t -> Result.t binary_arith_outcome_for_one_side_only

  val op_rhs_unknown :
    op -> lhs:Lhs.t -> Result.t binary_arith_outcome_for_one_side_only
end

module Int_ops_for_binary_arith (I : A.Int_number_kind) : sig
  include Binary_arith_like_sig with type op = P.binary_int_arith_op
end = struct
  module Lhs = I.Num
  module Rhs = I.Num
  module Result = I.Num

  type op = P.binary_int_arith_op

  (* There are never any restrictions on the constant propagation of integers,
     unlike for floats. *)
  let arg_kind = I.standard_int_or_float_kind

  let result_kind = K.Standard_int_or_float.to_kind arg_kind

  let to_lhs_elem = I.to_elem

  let to_rhs_elem = I.to_elem

  let prover_lhs = I.unboxed_prover

  let prover_rhs = I.unboxed_prover

  let unknown _ =
    match arg_kind with
    | Tagged_immediate -> T.any_tagged_immediate
    | Naked_immediate -> T.any_naked_immediate
    | Naked_float -> T.any_naked_float
    | Naked_int32 -> T.any_naked_int32
    | Naked_int64 -> T.any_naked_int64
    | Naked_nativeint -> T.any_naked_nativeint

  let these = I.these_unboxed

  let term = I.term_unboxed

  module Pair = I.Num.Pair

  let cross_product = I.Num.cross_product

  let op (op : P.binary_int_arith_op) n1 n2 =
    let always_some f = Some (f n1 n2) in
    match op with
    | Add -> always_some I.Num.add
    | Sub -> always_some I.Num.sub
    | Mul -> always_some I.Num.mul
    | Div -> I.Num.div n1 n2
    | Mod -> I.Num.mod_ n1 n2
    | And -> always_some I.Num.and_
    | Or -> always_some I.Num.or_
    | Xor -> always_some I.Num.xor

  type symmetric_op =
    | Add
    | Mul
    | And
    | Or
    | Xor

  module Num = I.Num

  let symmetric_op_one_side_unknown (op : symmetric_op) ~this_side :
      Num.t binary_arith_outcome_for_one_side_only =
    match op with
    | Add ->
      if Num.equal this_side Num.zero then The_other_side else Cannot_simplify
    | Mul ->
      if Num.equal this_side Num.zero
      then Exactly Num.zero
      else if Num.equal this_side Num.one
      then The_other_side
      else if Num.equal this_side Num.minus_one
      then Negation_of_the_other_side
      else Cannot_simplify
    | And ->
      if Num.equal this_side Num.minus_one
      then The_other_side
      else if Num.equal this_side Num.zero
      then Exactly Num.zero
      else Cannot_simplify
    | Or ->
      if Num.equal this_side Num.minus_one
      then Exactly Num.minus_one
      else if Num.equal this_side Num.zero
      then The_other_side
      else Cannot_simplify
    | Xor ->
      if Num.equal this_side Num.zero then The_other_side else Cannot_simplify

  let op_lhs_unknown (op : P.binary_int_arith_op) ~rhs :
      Num.t binary_arith_outcome_for_one_side_only =
    match op with
    | Add -> symmetric_op_one_side_unknown Add ~this_side:rhs
    | Mul -> symmetric_op_one_side_unknown Mul ~this_side:rhs
    | And -> symmetric_op_one_side_unknown And ~this_side:rhs
    | Or -> symmetric_op_one_side_unknown Or ~this_side:rhs
    | Xor -> symmetric_op_one_side_unknown Xor ~this_side:rhs
    | Sub -> if Num.equal rhs Num.zero then The_other_side else Cannot_simplify
    | Div ->
      (* Division ("safe" division, strictly speaking, in Lambda terminology) is
         translated to a conditional on the denominator followed by an unsafe
         division (the "Div" seen here) on the way into Flambda 2. So if the
         denominator turns out to be zero here, via the typing or whatever, then
         we're in unreachable code. *)
      (* CR-someday mshinwell: Should we expose unsafe division to the user? *)
      if Num.equal rhs Num.zero
      then Invalid
      else if Num.equal rhs Num.one
      then The_other_side
      else if Num.equal rhs Num.minus_one
      then
        Negation_of_the_other_side
        (* CR mshinwell: Add 0 / x = 0 when x <> 0 *)
      else Cannot_simplify
    | Mod ->
      (* CR mshinwell: We could be more clever for Mod and And *)
      if Num.equal rhs Num.zero
      then Invalid
      else if Num.equal rhs Num.one
      then Exactly Num.zero
      else if Num.equal rhs Num.minus_one
      then Exactly Num.zero
      else Cannot_simplify

  let op_rhs_unknown (op : P.binary_int_arith_op) ~lhs :
      Num.t binary_arith_outcome_for_one_side_only =
    match op with
    | Add -> symmetric_op_one_side_unknown Add ~this_side:lhs
    | Mul -> symmetric_op_one_side_unknown Mul ~this_side:lhs
    | And -> symmetric_op_one_side_unknown And ~this_side:lhs
    | Or -> symmetric_op_one_side_unknown Or ~this_side:lhs
    | Xor -> symmetric_op_one_side_unknown Xor ~this_side:lhs
    | Sub ->
      if Num.equal lhs Num.zero
      then Negation_of_the_other_side
      else Cannot_simplify
    | Div | Mod -> Cannot_simplify
end
[@@inline always]

module Binary_arith_like (N : Binary_arith_like_sig) : sig
  val simplify :
    N.op ->
    named ->
    arg1:Simple.t ->
    arg2:Simple.t ->
    Flambda2_core.named
end = struct
  module Possible_result = struct
    type t =
      | Simple of Simple.t
      | Prim of primitive
      | Exactly of N.Result.t

    (* This signature aims to constrain the size of the [Set] module block,
       since this is duplicated a lot via inlining in the rest of this file. *)
    module Set : sig
      type elt = t

      type t

      val empty : t

      val add : elt -> t -> t

      val cardinal : t -> int

      val get_singleton : t -> elt option

      val elements : t -> elt list
    end = Container_types.Make_set [@inlined hint] (struct
      type nonrec t = t

      let compare t1 t2 =
        match t1, t2 with
        | Simple simple1, Simple simple2 -> Simple.compare simple1 simple2
        | Prim prim1, Prim prim2 ->
          if Equiv.equiv_primitives (Equiv.Env.create ()) prim1 prim2 then 0
          else 1
        | Exactly i1, Exactly i2 -> N.Result.compare i1 i2
        | Simple _, (Prim _ | Exactly _) -> -1
        | Prim _, Simple _ -> 1
        | Prim _, Exactly _ -> -1
        | Exactly _, (Simple _ | Prim _) -> 1

      let print _ _ = Misc.fatal_error "Not implemented"
    end)
  end

  let simplify op original_term ~arg1 ~arg2 : Flambda2_core.named =
    let module PR = Possible_result in
    let kind = N.result_kind in
    let check_possible_results ~possible_results : Flambda2_core.named =
        let named : Flambda2_core.named =
          match PR.Set.get_singleton possible_results with
          | Some (Exactly i) -> N.term i
          | Some (Prim prim) -> (Flambda2_core.Prim prim)
          | Some (Simple simple) -> Flambda2_core.Simple simple
          | None -> original_term
        in
        let ty =
          let is =
            List.filter_map
              (fun (possible_result : PR.t) ->
                match possible_result with
                | Exactly i -> Some i
                | Prim _ | Simple _ -> None)
              (PR.Set.elements possible_results)
          in
          if List.length is = PR.Set.cardinal possible_results
          then N.these (N.Result.Set.of_list is)
          else
            match PR.Set.get_singleton possible_results with
            | Some (Simple simple) -> T.alias_type_of kind simple
            | Some (Exactly _) | Some (Prim _) | None -> N.unknown op
        in
        match T.get_alias_exn ty with
        | exception Not_found -> named
        | simple -> Flambda2_core.Simple simple
    in
    let only_one_side_known op nums ~folder ~other_side : Flambda2_core.named =
      let possible_results =
        folder
          (fun i possible_results ->
            match possible_results with
            | None -> None
            | Some possible_results -> (
              match op i with
              | Exactly result ->
                Some (PR.Set.add (Exactly result) possible_results)
              | The_other_side ->
                Some (PR.Set.add (Simple other_side) possible_results)
              | Negation_of_the_other_side ->
                let standard_int_kind : K.Standard_int.t =
                  match N.arg_kind with
                  | Tagged_immediate -> Tagged_immediate
                  | Naked_immediate -> Naked_immediate
                  | Naked_int32 -> Naked_int32
                  | Naked_int64 -> Naked_int64
                  | Naked_nativeint -> Naked_nativeint
                  | Naked_float ->
                    Misc.fatal_error
                      "Cannot use [Negation_of_the_other_side] with floats; \
                       use the float version instead"
                in
                let prim : P.t =
                  Unary (Int_arith (standard_int_kind, Neg), other_side)
                in
                Some (PR.Set.add (Prim (Translate.prim_to_core prim)) possible_results)
              (* | Float_negation_of_the_other_side ->
               *   let prim : P.t = Unary (Float_arith Neg, other_side) in
               *   Some (PR.Set.add (Prim (Translate.prim_to_core prim)) possible_results) *)
              | Cannot_simplify -> None
              | _ -> Some possible_results))
          nums (Some PR.Set.empty)
      in
      match possible_results with
      | Some results -> check_possible_results ~possible_results:results
      | None -> Misc.fatal_error "No possible results"
    in
    match N.to_lhs_elem arg1, N.to_rhs_elem arg2 with
    | Some arg1, Some arg2 ->
      let nums1 = N.Lhs.Set.singleton arg1 in
      let nums2 = N.Rhs.Set.singleton arg2 in
      let all_pairs = N.cross_product nums1 nums2 in
      let possible_results =
      N.Pair.Set.fold
        (fun (i1, i2) possible_results ->
          match N.op op i1 i2 with
          | None -> possible_results
          | Some result -> PR.Set.add (Exactly result) possible_results)
        all_pairs PR.Set.empty
      in
      check_possible_results ~possible_results
    | Some arg, None ->
      let nums1 = N.Lhs.Set.singleton arg in
      only_one_side_known
        (fun i -> N.op_rhs_unknown op ~lhs:i)
        nums1 ~folder:N.Lhs.Set.fold ~other_side:arg2
    | None, Some arg ->
      let nums2 = N.Rhs.Set.singleton arg in
      only_one_side_known
        (fun i -> N.op_lhs_unknown op ~rhs:i)
        nums2 ~folder:N.Rhs.Set.fold ~other_side:arg1
    | _, _ ->
      original_term
end
[@@inline always]

module Int_ops_for_binary_arith_tagged_immediate =
  Int_ops_for_binary_arith (A.For_tagged_immediates)
module Int_ops_for_binary_arith_naked_immediate =
  Int_ops_for_binary_arith (A.For_naked_immediates)
module Int_ops_for_binary_arith_int32 = Int_ops_for_binary_arith (A.For_int32s)
module Int_ops_for_binary_arith_int64 = Int_ops_for_binary_arith (A.For_int64s)
module Int_ops_for_binary_arith_nativeint =
  Int_ops_for_binary_arith (A.For_nativeints)
module Binary_int_arith_tagged_immediate =
  Binary_arith_like (Int_ops_for_binary_arith_tagged_immediate)
module Binary_int_arith_naked_immediate =
  Binary_arith_like (Int_ops_for_binary_arith_naked_immediate)
module Binary_int_arith_int32 =
  Binary_arith_like (Int_ops_for_binary_arith_int32)
module Binary_int_arith_int64 =
  Binary_arith_like (Int_ops_for_binary_arith_int64)
module Binary_int_arith_nativeint =
  Binary_arith_like (Int_ops_for_binary_arith_nativeint)

(* NOTE: Because the physical equality uses type information in a significant way,
   we might need to implement a similar downwards accumulator here *)
(* let eval_phys_equal x _ _ _ = x *)
      (* original_term *)
      (* (op: P.equality_comparison) ~arg1_ty ~arg2_ty = *)
  (* This primitive is only used for arguments of kind [Value]. *)
  (* Note: We don't compare the arguments themselves for equality. Instead, we
     know that [simplify_simple] always returns alias types, so we let the
     prover do the matching. *)
  (* match T.prove_physical_equality typing_env arg1_ty arg2_ty with
   * | Proved bool ->
   *   let result = match op with Eq -> bool | Neq -> not bool in
   *     Simple (Simple.untagged_const_bool result)
   * | Unknown -> original_term *)

(* Trying to see if we can get the evaluation without having information from
   the typing environment... *)
let eval_binary
      (v : P.binary_primitive) (arg1 : core_exp) (arg2 : core_exp) : core_exp =
  match v with
  | Int_arith (kind, op) ->
    (match arg1, arg2 with
     | Named (Simple s1), Named (Simple s2) ->
       (* let ty = to_flambda2_type kind
        * in *)
        Named ((match kind with
        | Tagged_immediate -> Binary_int_arith_tagged_immediate.simplify op
        | Naked_immediate -> Binary_int_arith_naked_immediate.simplify op
        | Naked_int32 -> Binary_int_arith_int32.simplify op
        | Naked_int64 -> Binary_int_arith_int64.simplify op
        | Naked_nativeint -> Binary_int_arith_nativeint.simplify op)
       (Prim (Binary (v, arg1, arg2))) ~arg1:s1 ~arg2:s2)
    | _, _ -> Named (Prim (Binary (v, arg1, arg2))))
  | Phys_equal _op ->
    (* (match arg1, arg2 with
     *  | Named (Simple s1), Named (Simple s2) ->
     *    let arg1_ty = s1 in
     *    let arg2_ty = s2 in
     *    let result =
     *      eval_phys_equal (Prim (Binary (v, arg1, arg2))) op ~arg1_ty ~arg2_ty
     *    in
     *    Named result
     *  | _, _ -> *)
    Named (Prim (Binary (v, arg1, arg2)))
  | Block_load (Values {tag = Known _; size = _; field_kind = _},
                (Immutable | Immutable_unique)) ->
    eval_block_load v arg1 arg2
  | Block_load (Naked_floats _, (Immutable | Immutable_unique))
  | Block_load (_, _)
  | Array_load (_,_)
  | String_or_bigstring_load (_,_)
  | Bigarray_load (_,_,_)
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
              Flambda2_core.Static_consts [(Static_const block)]
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

let rec eval (v : primitive) : core_exp =
  let f_arg arg =
    (match arg with
    | Named (Prim arg) -> eval arg
    | _ -> arg)
  in
  match v with
  | Nullary v -> Named (eval_nullary v)
  | Unary (v, arg) ->
    Named (eval_unary v (f_arg arg))
  | Binary (op, arg1, arg2) ->
    Format.fprintf Format.std_formatter "%a@. [simplified prim]%a@. @."
      print_prim v
      print (f_arg arg1)
    ;

    eval_binary op (f_arg arg1) (f_arg arg2)
  | Ternary (v, arg1, arg2, arg3) ->
    Named (eval_ternary v (f_arg arg1) (f_arg arg2) (f_arg arg3))
  | Variadic (v, args) ->
    let args =
      List.map f_arg args
    in
    Named (eval_variadic v args)
