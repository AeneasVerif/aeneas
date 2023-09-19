open HolKernel boolLib bossLib intLib
open arithmeticTheory integerTheory
open listTheory stringTheory

val _ = new_theory "primitives"

(*** Result *)
Datatype:
  error = Failure
End

Datatype:
  result = Return 'a | Fail error | Diverge
End

Type M = ``: 'a result``

Definition bind_def:
  (bind : 'a M -> ('a -> 'b M) -> 'b M) x f =
    case x of
      Return y => f y
    | Fail e => Fail e
    | Diverge => Diverge
End

val bind_name = fst (dest_const “bind”)

Definition return_def:
  (return : 'a -> 'a M) x =
    Return x
End

Definition massert_def:
  massert b = if b then Return () else Fail Failure
End

Overload monad_bind = ``bind``
Overload monad_unitbind = ``\x y. bind x (\z. y)``
Overload monad_ignore_bind = ``\x y. bind x (\z. y)``

Definition is_diverge_def:
  is_diverge (r: 'a result) : bool = case r of Diverge => T | _ => F
End

(* Allow the use of monadic syntax *)
val _ = monadsyntax.enable_monadsyntax ()

(*** For the globals *)
Definition get_return_value_def:
  get_return_value (Return x) = x
End

(*** Misc *)
Type char = “:char”
Type string = “:string”

Definition mem_replace_fwd_def:
  mem_replace_fwd (x : 'a) (y :'a) : 'a = x
End

Definition mem_replace_back_def:
  mem_replace_back (x : 'a) (y :'a) : 'a = y
End

(*** Scalars *)
(* Remark: most of the following code was partially generated *)

(* The bounds for the isize/usize types are opaque, because they vary with
   the architecture *)
val _ = new_constant ("isize_min", “:int”)
val _ = new_constant ("isize_max", “:int”)
val _ = new_constant ("usize_max", “:int”)

val _ = new_type ("usize", 0)
val _ = new_type ("u8", 0)
val _ = new_type ("u16", 0)
val _ = new_type ("u32", 0)
val _ = new_type ("u64", 0)
val _ = new_type ("u128", 0)
val _ = new_type ("isize", 0)
val _ = new_type ("i8", 0)
val _ = new_type ("i16", 0)
val _ = new_type ("i32", 0)
val _ = new_type ("i64", 0)
val _ = new_type ("i128", 0)

val _ = new_constant ("isize_to_int", “:isize -> int”)
val _ = new_constant ("i8_to_int",    “:i8 -> int”)
val _ = new_constant ("i16_to_int",   “:i16 -> int”)
val _ = new_constant ("i32_to_int",   “:i32 -> int”)
val _ = new_constant ("i64_to_int",   “:i64 -> int”)
val _ = new_constant ("i128_to_int",  “:i128 -> int”)
val _ = new_constant ("usize_to_int", “:usize -> int”)
val _ = new_constant ("u8_to_int",    “:u8 -> int”)
val _ = new_constant ("u16_to_int",   “:u16 -> int”)
val _ = new_constant ("u32_to_int",   “:u32 -> int”)
val _ = new_constant ("u64_to_int",   “:u64 -> int”)
val _ = new_constant ("u128_to_int",  “:u128 -> int”)

(* The functions which convert integers to machine scalars don't fail.

   If we were to write a model of those functions, we would return an arbitrary
   element (or saturate) if the input integer is not in bounds.

   This design choice makes it a lot easier to manipulate those functions.
   Moreover, it allows to define and prove rewriting theorems and custom
   unfolding theorems which are necessary to evaluate terms (when doing
   unit tests). For instance, we can prove: “int_to_isize (isize_to_int i) = i”.
 *)
val _ = new_constant ("int_to_isize", “:int -> isize”)
val _ = new_constant ("int_to_i8", “:int -> i8”)
val _ = new_constant ("int_to_i16", “:int -> i16”)
val _ = new_constant ("int_to_i32", “:int -> i32”)
val _ = new_constant ("int_to_i64", “:int -> i64”)
val _ = new_constant ("int_to_i128", “:int -> i128”)
val _ = new_constant ("int_to_usize", “:int -> usize”)
val _ = new_constant ("int_to_u8", “:int -> u8”)
val _ = new_constant ("int_to_u16", “:int -> u16”)
val _ = new_constant ("int_to_u32", “:int -> u32”)
val _ = new_constant ("int_to_u64", “:int -> u64”)
val _ = new_constant ("int_to_u128", “:int -> u128”)

(* The bounds *)
val i8_min_def   = Define ‘i8_min   = (-128:int)’
val i8_max_def   = Define ‘i8_max   = (127:int)’
val i16_min_def  = Define ‘i16_min  = (-32768:int)’
val i16_max_def  = Define ‘i16_max  = (32767:int)’
val i32_min_def  = Define ‘i32_min  = (-2147483648:int)’
val i32_max_def  = Define ‘i32_max  = (2147483647:int)’
val i64_min_def  = Define ‘i64_min  = (-9223372036854775808:int)’
val i64_max_def  = Define ‘i64_max  = (9223372036854775807:int)’
val i128_min_def = Define ‘i128_min = (-170141183460469231731687303715884105728:int)’
val i128_max_def = Define ‘i128_max = (170141183460469231731687303715884105727:int)’
val u8_max_def   = Define ‘u8_max   = (255:int)’
val u16_max_def  = Define ‘u16_max  = (65535:int)’
val u32_max_def  = Define ‘u32_max  = (4294967295:int)’
val u64_max_def  = Define ‘u64_max  = (18446744073709551615:int)’
val u128_max_def = Define ‘u128_max = (340282366920938463463374607431768211455:int)’

(* The following bounds are valid for all architectures *)
val isize_bounds = new_axiom ("isize_bounds", “isize_min <= i16_min /\ i16_max <= isize_max”)
val usize_bounds = new_axiom ("usize_bounds", “u16_max <= usize_max”)

(* Conversion to and from int.

   Note that for isize and usize, we write the lemmas in such a way that the
   proofs are easily automatable for constants.
 *)
val isize_to_int_int_to_isize =
  new_axiom ("isize_to_int_int_to_isize",
    “!n. isize_min <= n /\ n <= isize_max ==> isize_to_int (int_to_isize n) = n”)

val i8_to_int_int_to_i8 =
  new_axiom ("i8_to_int_int_to_i8",
    “!n. i8_min <= n /\ n <= i8_max ==> i8_to_int (int_to_i8 n) = n”)

val i16_to_int_int_to_i16 =
  new_axiom ("i16_to_int_int_to_i16",
    “!n. i16_min <= n /\ n <= i16_max ==> i16_to_int (int_to_i16 n) = n”)

val i32_to_int_int_to_i32 =
  new_axiom ("i32_to_int_int_to_i32",
    “!n. i32_min <= n /\ n <= i32_max ==> i32_to_int (int_to_i32 n) = n”)

val i64_to_int_int_to_i64 =
  new_axiom ("i64_to_int_int_to_i64",
    “!n. i64_min <= n /\ n <= i64_max ==> i64_to_int (int_to_i64 n) = n”)

val i128_to_int_int_to_i128 =
  new_axiom ("i128_to_int_int_to_i128",
    “!n. i128_min <= n /\ n <= i128_max ==> i128_to_int (int_to_i128 n) = n”)

val usize_to_int_int_to_usize =
  new_axiom ("usize_to_int_int_to_usize",
    “!n. 0 <= n /\ n <= usize_max ==> usize_to_int (int_to_usize n) = n”)

val u8_to_int_int_to_u8 =
  new_axiom ("u8_to_int_int_to_u8",
    “!n. 0 <= n /\ n <= u8_max ==> u8_to_int (int_to_u8 n) = n”)

val u16_to_int_int_to_u16 =
  new_axiom ("u16_to_int_int_to_u16",
    “!n. 0 <= n /\ n <= u16_max ==> u16_to_int (int_to_u16 n) = n”)

val u32_to_int_int_to_u32 =
  new_axiom ("u32_to_int_int_to_u32",
    “!n. 0 <= n /\ n <= u32_max ==> u32_to_int (int_to_u32 n) = n”)

val u64_to_int_int_to_u64 =
  new_axiom ("u64_to_int_int_to_u64",
    “!n. 0 <= n /\ n <= u64_max ==> u64_to_int (int_to_u64 n) = n”)

val u128_to_int_int_to_u128 =
  new_axiom ("u128_to_int_int_to_u128",
    “!n. 0 <= n /\ n <= u128_max ==> u128_to_int (int_to_u128 n) = n”)

val int_to_i8_i8_to_int       = new_axiom ("int_to_i8_i8_to_int",       “∀i. int_to_i8 (i8_to_int i) = i”)
val int_to_i16_i16_to_int     = new_axiom ("int_to_i16_i16_to_int",     “∀i. int_to_i16 (i16_to_int i) = i”)
val int_to_i32_i32_to_int     = new_axiom ("int_to_i32_i32_to_int",     “∀i. int_to_i32 (i32_to_int i) = i”)
val int_to_i64_i64_to_int     = new_axiom ("int_to_i64_i64_to_int",     “∀i. int_to_i64 (i64_to_int i) = i”)
val int_to_i128_i128_to_int   = new_axiom ("int_to_i128_i128_to_int",   “∀i. int_to_i128 (i128_to_int i) = i”)
val int_to_isize_isize_to_int = new_axiom ("int_to_isize_isize_to_int", “∀i. int_to_isize (isize_to_int i) = i”)

val int_to_u8_u8_to_int       = new_axiom ("int_to_u8_u8_to_int",       “∀i. int_to_u8 (u8_to_int i) = i”)
val int_to_u16_u16_to_int     = new_axiom ("int_to_u16_u16_to_int",     “∀i. int_to_u16 (u16_to_int i) = i”)
val int_to_u32_u32_to_int     = new_axiom ("int_to_u32_u32_to_int",     “∀i. int_to_u32 (u32_to_int i) = i”)
val int_to_u64_u64_to_int     = new_axiom ("int_to_u64_u64_to_int",     “∀i. int_to_u64 (u64_to_int i) = i”)
val int_to_u128_u128_to_int   = new_axiom ("int_to_u128_u128_to_int",   “∀i. int_to_u128 (u128_to_int i) = i”)
val int_to_usize_usize_to_int = new_axiom ("int_to_usize_usize_to_int", “∀i. int_to_usize (usize_to_int i) = i”)

(** Utilities to define the arithmetic operations *)
val mk_isize_def = Define
  ‘mk_isize n =
    if isize_min <= n /\ n <= isize_max then Return (int_to_isize n)
    else Fail Failure’

val mk_i8_def = Define
  ‘mk_i8 n =
    if i8_min <= n /\ n <= i8_max then Return (int_to_i8 n)
    else Fail Failure’

val mk_i16_def = Define
  ‘mk_i16 n =
    if i16_min <= n /\ n <= i16_max then Return (int_to_i16 n)
    else Fail Failure’

val mk_i32_def = Define
  ‘mk_i32 n =
    if i32_min <= n /\ n <= i32_max then Return (int_to_i32 n)
    else Fail Failure’

val mk_i64_def = Define
  ‘mk_i64 n =
    if i64_min <= n /\ n <= i64_max then Return (int_to_i64 n)
    else Fail Failure’

val mk_i128_def = Define
  ‘mk_i128 n =
    if i128_min <= n /\ n <= i128_max then Return (int_to_i128 n)
    else Fail Failure’

val mk_usize_def = Define
  ‘mk_usize n =
    if 0 <= n /\ n <= usize_max then Return (int_to_usize n)
    else Fail Failure’

val mk_u8_def = Define
  ‘mk_u8 n =
    if 0 <= n /\ n <= u8_max then Return (int_to_u8 n)
    else Fail Failure’

val mk_u16_def = Define
  ‘mk_u16 n =
    if 0 <= n /\ n <= u16_max then Return (int_to_u16 n)
    else Fail Failure’

val mk_u32_def = Define
  ‘mk_u32 n =
    if 0 <= n /\ n <= u32_max then Return (int_to_u32 n)
    else Fail Failure’

val mk_u64_def = Define
  ‘mk_u64 n =
    if 0 <= n /\ n <= u64_max then Return (int_to_u64 n)
    else Fail Failure’

val mk_u128_def = Define
  ‘mk_u128 n =
    if 0 <= n /\ n <= u128_max then Return (int_to_u128 n)
    else Fail Failure’

(** Constants *)
val core_i8_min_def    = Define ‘core_i8_min     = int_to_i8 i8_min’
val core_i8_max_def    = Define ‘core_i8_max     = int_to_i8 i8_max’
val core_i16_min_def   = Define ‘core_i16_min    = int_to_i16 i16_min’
val core_i16_max_def   = Define ‘core_i16_max    = int_to_i16 i16_max’
val core_i32_min_def   = Define ‘core_i32_min    = int_to_i32 i32_min’
val core_i32_max_def   = Define ‘core_i32_max    = int_to_i32 i32_max’
val core_i64_min_def   = Define ‘core_i64_min    = int_to_i64 i64_min’
val core_i64_max_def   = Define ‘core_i64_max    = int_to_i64 i64_max’
val core_i128_min_def  = Define ‘core_i128_min   = int_to_i128 i128_min’
val core_i128_max_def  = Define ‘core_i128_max   = int_to_i128 i128_max’
val core_isize_min_def = Define ‘core_isize_min  = int_to_isize isize_min’
val core_isize_max_def = Define ‘core_isize_max  = int_to_isize isize_max’
val core_u8_min_def    = Define ‘core_u8_min     = int_to_u8 0’
val core_u8_max_def    = Define ‘core_u8_max     = int_to_u8 u8_max’
val core_u16_min_def   = Define ‘core_u16_min    = int_to_u16 0’
val core_u16_max_def   = Define ‘core_u16_max    = int_to_u16 u16_max’
val core_u32_min_def   = Define ‘core_u32_min    = int_to_u32 0’
val core_u32_max_def   = Define ‘core_u32_max    = int_to_u32 u32_max’
val core_u64_min_def   = Define ‘core_u64_min    = int_to_u64 0’
val core_u64_max_def   = Define ‘core_u64_max    = int_to_u64 u64_max’
val core_u128_min_def  = Define ‘core_u128_min   = int_to_u128 0’
val core_u128_max_def  = Define ‘core_u128_max   = int_to_u128 u128_max’
val core_usize_min_def = Define ‘core_usize_min  = int_to_usize 0’
val core_usize_max_def = Define ‘core_usize_max  = int_to_usize usize_max’

val isize_neg_def = Define ‘isize_neg x = mk_isize (- (isize_to_int x))’
val i8_neg_def    = Define ‘i8_neg x    = mk_i8 (- (i8_to_int x))’
val i16_neg_def   = Define ‘i16_neg x   = mk_i16 (- (i16_to_int x))’
val i32_neg_def   = Define ‘i32_neg x   = mk_i32 (- (i32_to_int x))’
val i64_neg_def   = Define ‘i64_neg x   = mk_i64 (- (i64_to_int x))’
val i128_neg_def  = Define ‘i128_neg x  = mk_i128 (- (i128_to_int x))’

val isize_add_def = Define ‘isize_add x y = mk_isize ((isize_to_int x) + (isize_to_int y))’
val i8_add_def    = Define ‘i8_add x y    = mk_i8 ((i8_to_int x) + (i8_to_int y))’
val i16_add_def   = Define ‘i16_add x y   = mk_i16 ((i16_to_int x) + (i16_to_int y))’
val i32_add_def   = Define ‘i32_add x y   = mk_i32 ((i32_to_int x) + (i32_to_int y))’
val i64_add_def   = Define ‘i64_add x y   = mk_i64 ((i64_to_int x) + (i64_to_int y))’
val i128_add_def  = Define ‘i128_add x y  = mk_i128 ((i128_to_int x) + (i128_to_int y))’
val usize_add_def = Define ‘usize_add x y = mk_usize ((usize_to_int x) + (usize_to_int y))’
val u8_add_def    = Define ‘u8_add x y    = mk_u8 ((u8_to_int x) + (u8_to_int y))’
val u16_add_def   = Define ‘u16_add x y   = mk_u16 ((u16_to_int x) + (u16_to_int y))’
val u32_add_def   = Define ‘u32_add x y   = mk_u32 ((u32_to_int x) + (u32_to_int y))’
val u64_add_def   = Define ‘u64_add x y   = mk_u64 ((u64_to_int x) + (u64_to_int y))’
val u128_add_def  = Define ‘u128_add x y  = mk_u128 ((u128_to_int x) + (u128_to_int y))’

val isize_sub_def = Define ‘isize_sub x y = mk_isize ((isize_to_int x) - (isize_to_int y))’
val i8_sub_def    = Define ‘i8_sub x y    = mk_i8 ((i8_to_int x) - (i8_to_int y))’
val i16_sub_def   = Define ‘i16_sub x y   = mk_i16 ((i16_to_int x) - (i16_to_int y))’
val i32_sub_def   = Define ‘i32_sub x y   = mk_i32 ((i32_to_int x) - (i32_to_int y))’
val i64_sub_def   = Define ‘i64_sub x y   = mk_i64 ((i64_to_int x) - (i64_to_int y))’
val i128_sub_def  = Define ‘i128_sub x y  = mk_i128 ((i128_to_int x) - (i128_to_int y))’
val usize_sub_def = Define ‘usize_sub x y = mk_usize ((usize_to_int x) - (usize_to_int y))’
val u8_sub_def    = Define ‘u8_sub x y    = mk_u8 ((u8_to_int x) - (u8_to_int y))’
val u16_sub_def   = Define ‘u16_sub x y   = mk_u16 ((u16_to_int x) - (u16_to_int y))’
val u32_sub_def   = Define ‘u32_sub x y   = mk_u32 ((u32_to_int x) - (u32_to_int y))’
val u64_sub_def   = Define ‘u64_sub x y   = mk_u64 ((u64_to_int x) - (u64_to_int y))’
val u128_sub_def  = Define ‘u128_sub x y  = mk_u128 ((u128_to_int x) - (u128_to_int y))’

val isize_mul_def = Define ‘isize_mul x y = mk_isize ((isize_to_int x) * (isize_to_int y))’
val i8_mul_def    = Define ‘i8_mul x y    = mk_i8 ((i8_to_int x) * (i8_to_int y))’
val i16_mul_def   = Define ‘i16_mul x y   = mk_i16 ((i16_to_int x) * (i16_to_int y))’
val i32_mul_def   = Define ‘i32_mul x y   = mk_i32 ((i32_to_int x) * (i32_to_int y))’
val i64_mul_def   = Define ‘i64_mul x y   = mk_i64 ((i64_to_int x) * (i64_to_int y))’
val i128_mul_def  = Define ‘i128_mul x y  = mk_i128 ((i128_to_int x) * (i128_to_int y))’
val usize_mul_def = Define ‘usize_mul x y = mk_usize ((usize_to_int x) * (usize_to_int y))’
val u8_mul_def    = Define ‘u8_mul x y    = mk_u8 ((u8_to_int x) * (u8_to_int y))’
val u16_mul_def   = Define ‘u16_mul x y   = mk_u16 ((u16_to_int x) * (u16_to_int y))’
val u32_mul_def   = Define ‘u32_mul x y   = mk_u32 ((u32_to_int x) * (u32_to_int y))’
val u64_mul_def   = Define ‘u64_mul x y   = mk_u64 ((u64_to_int x) * (u64_to_int y))’
val u128_mul_def  = Define ‘u128_mul x y  = mk_u128 ((u128_to_int x) * (u128_to_int y))’

val isize_div_def = Define ‘isize_div x y =
  if isize_to_int y = 0 then Fail Failure else mk_isize ((isize_to_int x) / (isize_to_int y))’
val i8_div_def = Define ‘i8_div x y =
  if i8_to_int y = 0 then Fail Failure else mk_i8 ((i8_to_int x) / (i8_to_int y))’
val i16_div_def = Define ‘i16_div x y =
  if i16_to_int y = 0 then Fail Failure else mk_i16 ((i16_to_int x) / (i16_to_int y))’
val i32_div_def = Define ‘i32_div x y =
  if i32_to_int y = 0 then Fail Failure else mk_i32 ((i32_to_int x) / (i32_to_int y))’
val i64_div_def = Define ‘i64_div x y =
  if i64_to_int y = 0 then Fail Failure else mk_i64 ((i64_to_int x) / (i64_to_int y))’
val i128_div_def = Define ‘i128_div x y =
  if i128_to_int y = 0 then Fail Failure else mk_i128 ((i128_to_int x) / (i128_to_int y))’
val usize_div_def = Define ‘usize_div x y =
  if usize_to_int y = 0 then Fail Failure else mk_usize ((usize_to_int x) / (usize_to_int y))’
val u8_div_def = Define ‘u8_div x y =
  if u8_to_int y = 0 then Fail Failure else mk_u8 ((u8_to_int x) / (u8_to_int y))’
val u16_div_def = Define ‘u16_div x y =
  if u16_to_int y = 0 then Fail Failure else mk_u16 ((u16_to_int x) / (u16_to_int y))’
val u32_div_def = Define ‘u32_div x y =
  if u32_to_int y = 0 then Fail Failure else mk_u32 ((u32_to_int x) / (u32_to_int y))’
val u64_div_def = Define ‘u64_div x y =
  if u64_to_int y = 0 then Fail Failure else mk_u64 ((u64_to_int x) / (u64_to_int y))’
val u128_div_def = Define ‘u128_div x y =
  if u128_to_int y = 0 then Fail Failure else mk_u128 ((u128_to_int x) / (u128_to_int y))’

(* The remainder operation is not a modulo.

   In Rust, the remainder has the sign of the dividend.
   In HOL4, it has the sign of the divisor.
 *)
val int_rem_def = Define ‘int_rem (x : int) (y : int) : int =
  if (0 ≤ x /\ 0 ≤ y) \/ (x < 0 /\ y < 0) then x % y else -(x % y)’

(* Checking consistency with Rust *)
val _ = prove(“int_rem 1 2 = 1”, EVAL_TAC)
val _ = prove(“int_rem (-1) 2 = -1”, EVAL_TAC)
val _ = prove(“int_rem 1 (-2) = 1”, EVAL_TAC)
val _ = prove(“int_rem (-1) (-2) = -1”, EVAL_TAC)

val isize_rem_def = Define ‘isize_rem x y =
  if isize_to_int y = 0 then Fail Failure else mk_isize (int_rem (isize_to_int x) (isize_to_int y))’
val i8_rem_def = Define ‘i8_rem x y =
  if i8_to_int y = 0 then Fail Failure else mk_i8 (int_rem (i8_to_int x) (i8_to_int y))’
val i16_rem_def = Define ‘i16_rem x y =
  if i16_to_int y = 0 then Fail Failure else mk_i16 (int_rem (i16_to_int x) (i16_to_int y))’
val i32_rem_def = Define ‘i32_rem x y =
  if i32_to_int y = 0 then Fail Failure else mk_i32 (int_rem (i32_to_int x) (i32_to_int y))’
val i64_rem_def = Define ‘i64_rem x y =
  if i64_to_int y = 0 then Fail Failure else mk_i64 (int_rem (i64_to_int x) (i64_to_int y))’
val i128_rem_def = Define ‘i128_rem x y =
  if i128_to_int y = 0 then Fail Failure else mk_i128 (int_rem (i128_to_int x) (i128_to_int y))’
val usize_rem_def = Define ‘usize_rem x y =
  if usize_to_int y = 0 then Fail Failure else mk_usize (int_rem (usize_to_int x) (usize_to_int y))’
val u8_rem_def = Define ‘u8_rem x y =
  if u8_to_int y = 0 then Fail Failure else mk_u8 (int_rem (u8_to_int x) (u8_to_int y))’
val u16_rem_def = Define ‘u16_rem x y =
  if u16_to_int y = 0 then Fail Failure else mk_u16 (int_rem (u16_to_int x) (u16_to_int y))’
val u32_rem_def = Define ‘u32_rem x y =
  if u32_to_int y = 0 then Fail Failure else mk_u32 (int_rem (u32_to_int x) (u32_to_int y))’
val u64_rem_def = Define ‘u64_rem x y =
  if u64_to_int y = 0 then Fail Failure else mk_u64 (int_rem (u64_to_int x) (u64_to_int y))’
val u128_rem_def = Define ‘u128_rem x y =
  if u128_to_int y = 0 then Fail Failure else mk_u128 (int_rem (u128_to_int x) (u128_to_int y))’

Definition u8_lt_def:
  u8_lt x y = (u8_to_int x < u8_to_int y)
End

Definition u16_lt_def:
  u16_lt x y = (u16_to_int x < u16_to_int y)
End

Definition u32_lt_def:
  u32_lt x y = (u32_to_int x < u32_to_int y)
End

Definition u64_lt_def:
  u64_lt x y = (u64_to_int x < u64_to_int y)
End

Definition u128_lt_def:
  u128_lt x y = (u128_to_int x < u128_to_int y)
End

Definition usize_lt_def:
  usize_lt x y = (usize_to_int x < usize_to_int y)
End

Definition i8_lt_def:
  i8_lt x y = (i8_to_int x < i8_to_int y)
End

Definition i16_lt_def:
  i16_lt x y = (i16_to_int x < i16_to_int y)
End

Definition i32_lt_def:
  i32_lt x y = (i32_to_int x < i32_to_int y)
End

Definition i64_lt_def:
  i64_lt x y = (i64_to_int x < i64_to_int y)
End

Definition i128_lt_def:
  i128_lt x y = (i128_to_int x < i128_to_int y)
End

Definition isize_lt_def:
  isize_lt x y = (isize_to_int x < isize_to_int y)
End

Definition u8_le_def:
  u8_le x y = (u8_to_int x ≤ u8_to_int y)
End

Definition u16_le_def:
  u16_le x y = (u16_to_int x ≤ u16_to_int y)
End

Definition u32_le_def:
  u32_le x y = (u32_to_int x ≤ u32_to_int y)
End

Definition u64_le_def:
  u64_le x y = (u64_to_int x ≤ u64_to_int y)
End

Definition u128_le_def:
  u128_le x y = (u128_to_int x ≤ u128_to_int y)
End

Definition usize_le_def:
  usize_le x y = (usize_to_int x ≤ usize_to_int y)
End

Definition i8_le_def:
  i8_le x y = (i8_to_int x ≤ i8_to_int y)
End

Definition i16_le_def:
  i16_le x y = (i16_to_int x ≤ i16_to_int y)
End

Definition i32_le_def:
  i32_le x y = (i32_to_int x ≤ i32_to_int y)
End

Definition i64_le_def:
  i64_le x y = (i64_to_int x ≤ i64_to_int y)
End

Definition i128_le_def:
  i128_le x y = (i128_to_int x ≤ i128_to_int y)
End

Definition isize_le_def:
  isize_le x y = (isize_to_int x ≤ isize_to_int y)
End

Definition u8_gt_def:
  u8_gt x y = (u8_to_int x > u8_to_int y)
End

Definition u16_gt_def:
  u16_gt x y = (u16_to_int x > u16_to_int y)
End

Definition u32_gt_def:
  u32_gt x y = (u32_to_int x > u32_to_int y)
End

Definition u64_gt_def:
  u64_gt x y = (u64_to_int x > u64_to_int y)
End

Definition u128_gt_def:
  u128_gt x y = (u128_to_int x > u128_to_int y)
End

Definition usize_gt_def:
  usize_gt x y = (usize_to_int x > usize_to_int y)
End

Definition i8_gt_def:
  i8_gt x y = (i8_to_int x > i8_to_int y)
End

Definition i16_gt_def:
  i16_gt x y = (i16_to_int x > i16_to_int y)
End

Definition i32_gt_def:
  i32_gt x y = (i32_to_int x > i32_to_int y)
End

Definition i64_gt_def:
  i64_gt x y = (i64_to_int x > i64_to_int y)
End

Definition i128_gt_def:
  i128_gt x y = (i128_to_int x > i128_to_int y)
End

Definition isize_gt_def:
  isize_gt x y = (isize_to_int x > isize_to_int y)
End

Definition u8_ge_def:
  u8_ge x y = (u8_to_int x >= u8_to_int y)
End

Definition u16_ge_def:
  u16_ge x y = (u16_to_int x >= u16_to_int y)
End

Definition u32_ge_def:
  u32_ge x y = (u32_to_int x >= u32_to_int y)
End

Definition u64_ge_def:
  u64_ge x y = (u64_to_int x >= u64_to_int y)
End

Definition u128_ge_def:
  u128_ge x y = (u128_to_int x >= u128_to_int y)
End

Definition usize_ge_def:
  usize_ge x y = (usize_to_int x >= usize_to_int y)
End

Definition i8_ge_def:
  i8_ge x y = (i8_to_int x >= i8_to_int y)
End

Definition i16_ge_def:
  i16_ge x y = (i16_to_int x >= i16_to_int y)
End

Definition i32_ge_def:
  i32_ge x y = (i32_to_int x >= i32_to_int y)
End

Definition i64_ge_def:
  i64_ge x y = (i64_to_int x >= i64_to_int y)
End

Definition i128_ge_def:
  i128_ge x y = (i128_to_int x >= i128_to_int y)
End

Definition isize_ge_def:
  isize_ge x y = (isize_to_int x >= isize_to_int y)
End

(***
 * Vectors
 *)

val _ = new_type ("vec", 1)
val _ = new_constant ("vec_to_list", “:'a vec -> 'a list”)

(* Similarly to the "int_to_scalar" functions, the “mk_vec” function always
   succeeds (it must however make sure vectors have a length which is at most
   usize_max). In case the input list is too long, a model could return
   an arbitrary vector (a truncated vector for instance).

   Once again, this design choice makes it a lot easier to manipulate vectors,
   and allows to define and prove simpler rewriting and unfolding theorems.
 *)
val _ = new_constant ("mk_vec", “:'a list -> 'a vec”)

val vec_to_list_num_bounds =
  new_axiom ("vec_to_list_num_bounds",
    “!v. (0:num) <= LENGTH (vec_to_list v) /\ LENGTH (vec_to_list v) <= Num usize_max”)

(* This comes from ilistScript.sml.

   "ilist" stands for "integer lists". I noticed that in practice proofs which
   mix integers and natural numbers are very tedious to do. For this reason,
   I redefined many functions (like ‘LENGTH’) to use integers (I *do* see
   a drastic benefit when doing the proofs).

   Remark: did you have similar issues with Cogent? Are you aware of similar
   issues that the Sel4 people had to deal with?
 *)
val len_def = Define ‘
  len [] : int = 0 /\
  len (x :: ls) : int = 1 + len ls
’

val mk_vec_axiom = new_axiom ("mk_vec_axiom",
  “∀l. len l ≤ usize_max ⇒ vec_to_list (mk_vec l) = l”)

val vec_len_def = Define ‘vec_len v = int_to_usize (len (vec_to_list v))’

Definition vec_new_def:
  vec_new = mk_vec []
End

(* Same as ‘len’: comes from ilist

   Return the ith element of a list.

   Remark: we initially added the following case, so that we wouldn't need the
   premise [i < len ls] is [index_eq_EL]:
   “index (i : int) [] = EL (Num i) []”

   TODO: this can be simplified. See the Lean backend.
 *)
val index_def = Define ‘
  index (i : int) (x :: ls) = if i = 0 then x else (if 0 < i then index (i - 1) ls else ARB)
’

(* Helper *)
Definition vec_index_def:
  vec_index v i = index (usize_to_int i) (vec_to_list v)
End

(* Same as ‘len’: comes from ilist.

  TODO: this can be simplified. See the Lean backend. *)
val update_def = Define ‘
  update ([] : 'a list) (i : int) (y : 'a) : 'a list = [] ∧

  update (x :: ls) (i : int) y =
    if i = 0 then y :: ls else (if 0 < i then x :: update ls (i - 1) y else x :: ls)
’

(* Helper *)
Definition vec_update_def:
  vec_update v i x = mk_vec (update (vec_to_list v) (usize_to_int i) x)
End

Definition vec_index_fwd_def:
  vec_index_fwd v i =
    if usize_to_int i ≤ usize_to_int (vec_len v)
    then Return (vec_index v i)
    else Fail Failure
End

Definition vec_index_back_def:
  vec_index_back v i =
    if usize_to_int i < usize_to_int (vec_len v) then Return () else Fail Failure
End

Definition vec_index_mut_fwd_def:
  vec_index_mut_fwd v i =
    if usize_to_int i ≤ usize_to_int (vec_len v)
    then Return (vec_index v i)
    else Fail Failure
End

Definition vec_index_mut_back_def:
  vec_index_mut_back v i x =
    if usize_to_int i ≤ usize_to_int (vec_len v)
    then Return (vec_update v i x)
    else Fail Failure
End

val _ = export_theory ()
