(** [polonius_list] *)
open primitivesLib divDefLib

val _ = new_theory "poloniusList"


Datatype:
  (** [polonius_list::List] *)
  list_t = | ListCons 't list_t | ListNil
End

val [get_list_at_x_fwd_def] = DefineDiv ‘
  (** [polonius_list::get_list_at_x]: forward function *)
  get_list_at_x_fwd (ls : u32 list_t) (x : u32) : u32 list_t result =
    (case ls of
    | ListCons hd tl =>
      if hd = x then Return (ListCons hd tl) else get_list_at_x_fwd tl x
    | ListNil => Return ListNil)
’

val [get_list_at_x_back_def] = DefineDiv ‘
  (** [polonius_list::get_list_at_x]: backward function 0 *)
  get_list_at_x_back
    (ls : u32 list_t) (x : u32) (ret : u32 list_t) : u32 list_t result =
    (case ls of
    | ListCons hd tl =>
      if hd = x
      then Return ret
      else (do
            tl0 <- get_list_at_x_back tl x ret;
            Return (ListCons hd tl0)
            od)
    | ListNil => Return ret)
’

val _ = export_theory ()
