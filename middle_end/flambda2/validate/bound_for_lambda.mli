type t =
  { name: Code_id.t;
    return_continuation: Bound_continuation.t;
    exn_continuation: Bound_continuation.t;
    params: Bound_parameters.t }

val create :
  name:Code_id.t ->
  return_continuation:Continuation.t ->
  exn_continuation:Continuation.t ->
  params:Bound_parameters.t ->
  t

include Bindable.S with type t := t
