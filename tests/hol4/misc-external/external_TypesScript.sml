(** [external]: type definitions *)
open primitivesLib divDefLib

val _ = new_theory "external_Types"


val _ = new_type ("core_num_nonzero_non_zero_u32_t", 0)

(** The state type used in the state-error monad *)
val _ = new_type ("state", 0)

val _ = export_theory ()
