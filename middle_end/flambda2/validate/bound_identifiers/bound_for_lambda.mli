type t =
  { return_continuation: Bound_continuation.t;
    exn_continuation: Bound_continuation.t;
    my_region: Variable.t;
    params: Bound_parameters.t }

val create :
  return_continuation:Continuation.t ->
  exn_continuation:Continuation.t ->
  params:Bound_parameters.t ->
  my_region:Variable.t ->
  t

include Bindable.S with type t := t
