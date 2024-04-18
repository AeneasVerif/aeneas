(** [loops]: type definitions *)
open primitivesLib divDefLib

val _ = new_theory "loops_Types"


Datatype:
  (** [loops::List] *)
  list_t = | ListCons 't list_t | ListNil
End

val _ = export_theory ()
