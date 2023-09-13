type t =
  { return_continuation: Bound_continuation.t;
    exn_continuation: Bound_continuation.t;
    my_region: Variable.t;
    params: Bound_parameters.t }

let create ~return_continuation ~exn_continuation ~params ~my_region =
  Bound_parameters.check_no_duplicates params;
  { return_continuation;
    exn_continuation;
    my_region;
    params;
  }

let free_names
      { return_continuation;
        exn_continuation;
        my_region;
        params } =
  (* See [bound_continuations.ml] for why [add_traps] is [true]. *)
  let free_names =
    Name_occurrences.add_continuation Name_occurrences.empty return_continuation
      ~has_traps:true
  in
  let free_names =
    Name_occurrences.add_continuation free_names exn_continuation
      ~has_traps:true
  in
  let free_names =
    Name_occurrences.union free_names (Bound_parameters.free_names params)
  in
  let free_names =
    Name_occurrences.add_variable free_names my_region Name_mode.normal
  in
  free_names

let apply_renaming
      { return_continuation;
        exn_continuation;
        my_region;
        params } renaming =
  let return_continuation =
    Renaming.apply_continuation renaming return_continuation
  in
  let exn_continuation =
    Renaming.apply_continuation renaming exn_continuation
  in
  let params = Bound_parameters.apply_renaming params renaming in
  let my_region = Renaming.apply_variable renaming my_region in
  { return_continuation;
    exn_continuation;
    my_region;
    params;
  }

let ids_for_export
      { return_continuation;
        exn_continuation;
        my_region;
        params } =
  let ids =
    Ids_for_export.add_continuation Ids_for_export.empty return_continuation
  in
  let ids = Ids_for_export.add_continuation ids exn_continuation in
  let ids = Ids_for_export.add_variable ids my_region in
  Ids_for_export.union ids (Bound_parameters.ids_for_export params)

let[@ocamlformat "disable"] print ppf
     { return_continuation; exn_continuation; params; my_region } =
  Format.fprintf ppf "@[<v 0> (ret %a), (exn %a), (reg %a), (params %a)@]"
    Continuation.print return_continuation
    Continuation.print exn_continuation
    Variable.print my_region
    Bound_parameters.print params

let rename
      { return_continuation;
        exn_continuation;
        params;
        my_region
      } =
  { return_continuation = Continuation.rename return_continuation;
    exn_continuation = Continuation.rename exn_continuation;
    params = Bound_parameters.rename params;
    my_region = Variable.rename my_region;
  }

let renaming
    { return_continuation = return_continuation1;
      exn_continuation = exn_continuation1;
      params = params1;
      my_region = my_region1;
    }
    ~guaranteed_fresh:
    { return_continuation = return_continuation2;
      exn_continuation = exn_continuation2;
      params = params2;
      my_region = my_region2;
    } =
  let renaming =
    Renaming.add_fresh_continuation Renaming.empty return_continuation1
      ~guaranteed_fresh:return_continuation2
  in
  let renaming =
    Renaming.add_fresh_continuation renaming exn_continuation1
      ~guaranteed_fresh:exn_continuation2
  in
  let renaming =
    Renaming.add_fresh_variable renaming my_region1 ~guaranteed_fresh:my_region2
  in
  Renaming.compose
    ~second:(Bound_parameters.renaming params1 ~guaranteed_fresh:params2)
    ~first:renaming
