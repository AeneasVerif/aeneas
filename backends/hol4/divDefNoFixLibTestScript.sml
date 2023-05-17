open HolKernel
open divDefNoFixLib

val _ = new_theory "divDefNoFixLibTest"

val def_qt = ‘
  (even (i : int) : bool result =
    if i = 0 then Return T else odd (i - 1)) /\
  (odd (i : int) : bool result =
    if i = 0 then Return F else even (i - 1))
’

val even_def = DefineDiv def_qt

(* Complexifying the above definition, and overriding on purpose *)
val def_qt = ‘
  (even (i : int) : bool result =
    if i = 0 then
      do
        b <- Return T;
        Return b
      od
    else do
      b <- odd (i - 1);
      Return b
      od
    ) /\
  (odd (i : int) : bool result =
    if i = 0 then
      do
        b <- Return F;
        Return b
      od
    else do
      b <- even (i - 1);
      Return b
      od)
’

val even_def = DefineDiv def_qt

Datatype:
  list_t =
    ListCons 't list_t
  | ListNil
End

val def_qt = ‘
  nth_mut_fwd (ls : 't list_t) (i : u32) : 't result =
  case ls of
  | ListCons x tl =>
    if u32_to_int i = (0:int)
    then Return x
    else
      do
      i0 <- u32_sub i (int_to_u32 1);
      nth_mut_fwd tl i0
      od
  | ListNil =>
    Fail Failure
’

val nth_mut_fwd_def = DefineDiv def_qt

(* Complexifying the above definition, and overriding on purpose *)
val def_qt = ‘
  nth_mut_fwd (ls : 't list_t) (i : u32) : 't result =
  case ls of
  | ListCons x tl =>
    if u32_to_int i = (0:int)
    then Return x
    else
      do
      i0 <- u32_sub i (int_to_u32 1);
      x <- nth_mut_fwd tl i0;
      Return x
      od
  | ListNil => 
    Fail Failure
’

val nth_mut_fwd_def = DefineDiv def_qt

val _ = export_theory ()
