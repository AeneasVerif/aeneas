(* Examples which use divDefLib.DefineDiv *)

open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory stringTheory

open primitivesArithTheory primitivesBaseTacLib ilistTheory primitivesTheory
open primitivesLib
open divDefTheory divDefLib

val [even_def, odd_def] = DefineDiv ‘
  (even (i : int) : bool result = if i = 0 then Return T else odd (i - 1)) /\
  (odd (i : int) : bool result = if i = 0 then Return F else even (i - 1))
’

Datatype:
  list_t =
    ListCons 't list_t
  | ListNil
End

val [nth_def] = DefineDiv ‘
  nth (ls : 't list_t) (i : u32) : 't result =
    case ls of
    | ListCons x tl =>
      if u32_to_int i = (0:int)
      then (Return x)
      else
        do
        i0 <- u32_sub i (int_to_u32 1);
        nth tl i0
        od
    | ListNil => Fail Failure
’
