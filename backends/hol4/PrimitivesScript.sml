open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory stringTheory

val primitives_theory_name = "Primitives"
val _ = new_theory primitives_theory_name

(*** Result *)
Datatype:
  error = Failure
End

Datatype:
  result = Return 'a | Fail error | Loop
End

Type M = ``: 'a result``

val bind_def = Define `
  (bind : 'a M -> ('a -> 'b M) -> 'b M) x f =
    case x of
      Return y => f y
    | Fail e => Fail e
    | Loop => Loop`;

val bind_name = fst (dest_const “bind”)

val return_def = Define `
  (return : 'a -> 'a M) x =
    Return x`;

val massert_def = Define ‘massert b = if b then Return () else Fail Failure’

Overload monad_bind = ``bind``
Overload monad_unitbind = ``\x y. bind x (\z. y)``
Overload monad_ignore_bind = ``\x y. bind x (\z. y)``

(* Allow the use of monadic syntax *)
val _ = monadsyntax.enable_monadsyntax ()

(*** Misc *)
Type char = “:char”
Type string = “:string”

val mem_replace_fwd_def = Define ‘mem_replace_fwd (x : 'a) (y :'a) : 'a = x’
val mem_replace_back_def = Define ‘mem_replace_back (x : 'a) (y :'a) : 'a = y’

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

val all_bound_defs = [
  i8_min_def,   i8_max_def,
  i16_min_def,  i16_max_def,
  i32_min_def,  i32_max_def,
  i64_min_def,  i64_max_def,
  i128_min_def, i128_max_def,
  u8_max_def,
  u16_max_def,
  u32_max_def,
  u64_max_def,
  u128_max_def
]

(* The following bounds are valid for all architectures *)
val isize_bounds = new_axiom ("isize_bounds", “isize_min <= i16_min /\ isize_max >= i16_max”)
val usize_bounds = new_axiom ("usize_bounds", “usize_max >= u16_max”)

(* Conversion bounds *)
val isize_to_int_bounds = new_axiom ("isize_to_int_bounds",
  “!n. isize_min <= isize_to_int n /\ isize_to_int n <= isize_max”)

val i8_to_int_bounds = new_axiom ("i8_to_int_bounds",
  “!n. i8_min <= i8_to_int n /\ i8_to_int n <= i8_max”)

val i16_to_int_bounds = new_axiom ("i16_to_int_bounds",
  “!n. i16_min <= i16_to_int n /\ i16_to_int n <= i16_max”)

val i32_to_int_bounds = new_axiom ("i32_to_int_bounds",
  “!n. i32_min <= i32_to_int n /\ i32_to_int n <= i32_max”)

val i64_to_int_bounds = new_axiom ("i64_to_int_bounds",
  “!n. i64_min <= i64_to_int n /\ i64_to_int n <= i64_max”)

val i128_to_int_bounds = new_axiom ("i128_to_int_bounds",
  “!n. i128_min <= i128_to_int n /\ i128_to_int n <= i128_max”)

val usize_to_int_bounds = new_axiom ("usize_to_int_bounds",
  “!n. 0 <= usize_to_int n /\ usize_to_int n <= usize_max”)

val u8_to_int_bounds = new_axiom ("u8_to_int_bounds",
  “!n. 0 <= u8_to_int n /\ u8_to_int n <= u8_max”)

val u16_to_int_bounds = new_axiom ("u16_to_int_bounds",
  “!n. 0 <= u16_to_int n /\ u16_to_int n <= u16_max”)

val u32_to_int_bounds = new_axiom ("u32_to_int_bounds",
  “!n. 0 <= u32_to_int n /\ u32_to_int n <= u32_max”)

val u64_to_int_bounds = new_axiom ("u64_to_int_bounds",
  “!n. 0 <= u64_to_int n /\ u64_to_int n <= u64_max”)

val u128_to_int_bounds = new_axiom ("u128_to_int_bounds",
  “!n. 0 <= u128_to_int n /\ u128_to_int n <= u128_max”)

val all_to_int_bounds_lemmas = [
  isize_to_int_bounds,
  i8_to_int_bounds,
  i16_to_int_bounds,
  i32_to_int_bounds,
  i64_to_int_bounds,
  i128_to_int_bounds,
  usize_to_int_bounds,
  u8_to_int_bounds,
  u16_to_int_bounds,
  u32_to_int_bounds,
  u64_to_int_bounds,
  u128_to_int_bounds
]

(* Conversion to and from int.

   Note that for isize and usize, we write the lemmas in such a way that the
   proofs are easily automatable for constants.
 *)
val int_to_isize_id =
  new_axiom ("int_to_isize_id",
    “!n. (i16_min <= n \/ isize_min <= n) /\ (n <= i16_max \/ n <= isize_max) ==>
         isize_to_int (int_to_isize n) = n”)

val int_to_usize_id =
  new_axiom ("int_to_usize_id",
    “!n. 0 <= n /\ (n <= u16_max \/ n <= usize_max) ==> usize_to_int (int_to_usize n) = n”)

val int_to_i8_id =
  new_axiom ("int_to_i8_id",
    “!n. i8_min <= n /\ n <= i8_max ==> i8_to_int (int_to_i8 n) = n”)

val int_to_i16_id =
  new_axiom ("int_to_i16_id",
    “!n. i16_min <= n /\ n <= i16_max ==> i16_to_int (int_to_i16 n) = n”)

val int_to_i32_id =
  new_axiom ("int_to_i32_id",
    “!n. i32_min <= n /\ n <= i32_max ==> i32_to_int (int_to_i32 n) = n”)

val int_to_i64_id =
  new_axiom ("int_to_i64_id",
    “!n. i64_min <= n /\ n <= i64_max ==> i64_to_int (int_to_i64 n) = n”)

val int_to_i128_id =
  new_axiom ("int_to_i128_id",
    “!n. i128_min <= n /\ n <= i128_max ==> i128_to_int (int_to_i128 n) = n”)

val int_to_u8_id =
  new_axiom ("int_to_u8_id",
    “!n. 0 <= n /\ n <= u8_max ==> u8_to_int (int_to_u8 n) = n”)

val int_to_u16_id =
  new_axiom ("int_to_u16_id",
    “!n. 0 <= n /\ n <= u16_max ==> u16_to_int (int_to_u16 n) = n”)

val int_to_u32_id =
  new_axiom ("int_to_u32_id",
    “!n. 0 <= n /\ n <= u32_max ==> u32_to_int (int_to_u32 n) = n”)

val int_to_u64_id =
  new_axiom ("int_to_u64_id",
    “!n. 0 <= n /\ n <= u64_max ==> u64_to_int (int_to_u64 n) = n”)

val int_to_u128_id =
  new_axiom ("int_to_u128_id",
    “!n. 0 <= n /\ n <= u128_max ==> u128_to_int (int_to_u128 n) = n”)

val all_conversion_id_lemmas = [
  int_to_isize_id,
  int_to_i8_id,
  int_to_i16_id,
  int_to_i32_id,
  int_to_i64_id,
  int_to_i128_id,
  int_to_usize_id,
  int_to_u8_id,
  int_to_u16_id,
  int_to_u32_id,
  int_to_u64_id,
  int_to_u128_id
]

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

val all_mk_int_defs = [
  mk_isize_def,
  mk_i8_def,
  mk_i16_def,
  mk_i32_def,
  mk_i64_def,
  mk_i128_def,
  mk_usize_def,
  mk_u8_def,
  mk_u16_def,
  mk_u32_def,
  mk_u64_def,
  mk_u128_def
]


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

val all_add_defs = [
  isize_add_def,
  i8_add_def,
  i16_add_def,
  i32_add_def,
  i64_add_def,
  i128_add_def,
  usize_add_def,
  u8_add_def,
  u16_add_def,
  u32_add_def,
  u64_add_def,
  u128_add_def
]

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

val all_sub_defs = [
  isize_sub_def,
  i8_sub_def,
  i16_sub_def,
  i32_sub_def,
  i64_sub_def,
  i128_sub_def,
  usize_sub_def,
  u8_sub_def,
  u16_sub_def,
  u32_sub_def,
  u64_sub_def,
  u128_sub_def
]

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

val all_mul_defs = [
  isize_mul_def,
  i8_mul_def,
  i16_mul_def,
  i32_mul_def,
  i64_mul_def,
  i128_mul_def,
  usize_mul_def,
  u8_mul_def,
  u16_mul_def,
  u32_mul_def,
  u64_mul_def,
  u128_mul_def
]

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

val all_div_defs = [
  isize_div_def,
  i8_div_def,
  i16_div_def,
  i32_div_def,
  i64_div_def,
  i128_div_def,
  usize_div_def,
  u8_div_def,
  u16_div_def,
  u32_div_def,
  u64_div_def,
  u128_div_def
]

(* The remainder operation is not a modulo.

   In Rust, the remainder has the sign of the dividend.
   In HOL4, it has the sign of the divisor.
 *)
val int_rem_def = Define ‘int_rem (x : int) (y : int) : int =
  if (x >= 0 /\ y >= 0) \/ (x < 0 /\ y < 0) then x % y else -(x % y)’

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

val all_rem_defs = [
  isize_rem_def,
  i8_rem_def,
  i16_rem_def,
  i32_rem_def,
  i64_rem_def,
  i128_rem_def,
  usize_rem_def,
  u8_rem_def,
  u16_rem_def,
  u32_rem_def,
  u64_rem_def,
  u128_rem_def
]

(* Ignore a theorem.

   To be used in conjunction with {!pop_assum} for instance.
 *)
fun IGNORE_TAC (_ : thm) : tactic = ALL_TAC

val POP_IGNORE_TAC = POP_ASSUM IGNORE_TAC

(* TODO: we need a better library of lemmas about arithmetic *)

(* TODO: add those as rewriting tactics by default *)
val NOT_LE_EQ_GT = store_thm("NOT_LE_EQ_GT", “!(x y: int). ~(x <= y) <=> x > y”, COOPER_TAC)
val NOT_LT_EQ_GE = store_thm("NOT_LT_EQ_GE", “!(x y: int). ~(x < y) <=> x >= y”, COOPER_TAC)
val NOT_GE_EQ_LT = store_thm("NOT_GE_EQ_LT", “!(x y: int). ~(x >= y) <=> x < y”, COOPER_TAC)
val NOT_GT_EQ_LE = store_thm("NOT_GT_EQ_LE", “!(x y: int). ~(x > y) <=> x <= y”, COOPER_TAC)

Theorem POS_MUL_POS_IS_POS:
  !(x y : int). 0 <= x ==> 0 <= y ==> 0 <= x * y
Proof
  rpt strip_tac >>
  sg ‘0 <= &(Num x) * &(Num y)’ >- (rw [INT_MUL_CALCULATE] >> COOPER_TAC) >>
  sg ‘&(Num x) = x’ >- (irule EQ_SYM >> rw [INT_OF_NUM] >> COOPER_TAC) >>
  sg ‘&(Num y) = y’ >- (irule EQ_SYM >> rw [INT_OF_NUM] >> COOPER_TAC) >>
  metis_tac[]
QED

val GE_EQ_LE = store_thm("GE_EQ_LE", “!(x y : int). x >= y <=> y <= x”, COOPER_TAC)
val LE_EQ_GE = store_thm("LE_EQ_GE", “!(x y : int). x <= y <=> y >= x”, COOPER_TAC)
val GT_EQ_LT = store_thm("GT_EQ_LT", “!(x y : int). x > y <=> y < x”, COOPER_TAC)
val LT_EQ_GT = store_thm("LT_EQ_GT", “!(x y : int). x < y <=> y > x”, COOPER_TAC)

Theorem POS_DIV_POS_IS_POS:
  !(x y : int). 0 <= x ==> 0 < y ==> 0 <= x / y
Proof
  rpt strip_tac >>
  rw [LE_EQ_GE] >>  
  sg ‘y <> 0’ >- COOPER_TAC >>
  qspecl_then [‘\x. x >= 0’, ‘x’, ‘y’] ASSUME_TAC INT_DIV_FORALL_P >>
  fs [] >> POP_IGNORE_TAC >> rw [] >- COOPER_TAC >>
  fs [NOT_LT_EQ_GE] >>
  (* Proof by contradiction: assume k < 0 *)
  spose_not_then ASSUME_TAC >>
  fs [NOT_GE_EQ_LT] >>
  sg ‘k * y = (k + 1) * y + - y’ >- (fs [INT_RDISTRIB] >> COOPER_TAC) >>
  sg ‘0 <= (-(k + 1)) * y’ >- (irule POS_MUL_POS_IS_POS >> COOPER_TAC) >>
  COOPER_TAC
QED

Theorem POS_DIV_POS_LE:
  !(x y d : int). 0 <= x ==> 0 <= y ==> 0 < d ==> x <= y ==> x / d <= y / d
Proof
  rpt strip_tac >>
  sg ‘d <> 0’ >- COOPER_TAC >>
  qspecl_then [‘\k. k = x / d’, ‘x’, ‘d’] ASSUME_TAC INT_DIV_P >>
  qspecl_then [‘\k. k = y / d’, ‘y’, ‘d’] ASSUME_TAC INT_DIV_P >>
  rfs [NOT_LT_EQ_GE] >> TRY COOPER_TAC >>
  sg ‘y = (x / d) * d + (r' + y - x)’ >- COOPER_TAC >>
  qspecl_then [‘(x / d) * d’, ‘r' + y - x’, ‘d’] ASSUME_TAC INT_ADD_DIV >>
  rfs [] >>
  Cases_on ‘x = y’ >- fs [] >>
  sg ‘r' + y ≠ x’ >- COOPER_TAC >> fs [] >>
  sg ‘((x / d) * d) / d = x / d’ >- (irule INT_DIV_RMUL >> COOPER_TAC) >>
  fs [] >>
  sg ‘0 <= (r' + y − x) / d’ >- (irule POS_DIV_POS_IS_POS >> COOPER_TAC) >>
  metis_tac [INT_LE_ADDR]
QED

Theorem POS_DIV_POS_LE_INIT:
  !(x y : int). 0 <= x ==> 0 < y ==> x / y <= x
Proof
  rpt strip_tac >>
  sg ‘y <> 0’ >- COOPER_TAC >>
  qspecl_then [‘\k. k = x / y’, ‘x’, ‘y’] ASSUME_TAC INT_DIV_P >>
  rfs [NOT_LT_EQ_GE] >- COOPER_TAC >>
  sg ‘y = (y - 1) + 1’ >- rw [] >>
  sg ‘x = x / y + ((x / y) * (y - 1) + r)’ >-(
    qspecl_then [‘1’, ‘y-1’, ‘x / y’] ASSUME_TAC INT_LDISTRIB >>
    rfs [] >>
    COOPER_TAC
  ) >>
  sg ‘!a b c. 0 <= c ==> a = b + c ==> b <= a’ >- (COOPER_TAC) >>
  pop_assum irule >>
  exists_tac “x / y * (y − 1) + r” >>
  sg ‘0 <= x / y’ >- (irule POS_DIV_POS_IS_POS >> COOPER_TAC) >>
  sg ‘0 <= (x / y) * (y - 1)’ >- (irule POS_MUL_POS_IS_POS >> COOPER_TAC) >>
  COOPER_TAC
QED

Theorem POS_MOD_POS_IS_POS:
  !(x y : int). 0 <= x ==> 0 < y ==> 0 <= x % y
Proof
  rpt strip_tac >>
  sg ‘y <> 0’ >- COOPER_TAC >>
  imp_res_tac INT_DIVISION >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  sg ‘~(y < 0)’ >- COOPER_TAC >> fs []
QED

Theorem POS_MOD_POS_LE_INIT:
  !(x y : int). 0 <= x ==> 0 < y ==> x % y <= x
Proof
  rpt strip_tac >>
  sg ‘y <> 0’ >- COOPER_TAC >>
  imp_res_tac INT_DIVISION >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  first_x_assum (qspec_then ‘x’ assume_tac) >>
  sg ‘~(y < 0)’ >- COOPER_TAC >> fs [] >>
  sg ‘0 <= x % y’ >- (irule POS_MOD_POS_IS_POS >> COOPER_TAC) >>
  sg ‘0 <= x / y’ >- (irule POS_DIV_POS_IS_POS >> COOPER_TAC) >>
  sg ‘0 <= (x / y) * y’ >- (irule POS_MUL_POS_IS_POS >> COOPER_TAC) >>
  COOPER_TAC
QED

(*
val (asms,g) = top_goal ()
*)

fun prove_arith_op_eq (asms, g) =
  let
    val (_, t) = (dest_exists o snd o strip_imp o snd o strip_forall) g;
    val (x_to_int, y_to_int) =
      case (snd o strip_comb o rhs o snd o dest_conj) t of
        [x, y] => (x,y)
      | _ => failwith "Unexpected"
    val x = (snd o dest_comb) x_to_int;
    val y = (snd o dest_comb) y_to_int;
    fun inst_first_lem arg lems =
      MAP_FIRST (fn th => (ASSUME_TAC (SPEC arg th) handle HOL_ERR _ => FAIL_TAC "")) lems;
  in
    (rpt gen_tac >>
     rpt DISCH_TAC >>
     ASSUME_TAC usize_bounds >> (* Only useful for usize of course *)
     ASSUME_TAC isize_bounds >> (* Only useful for isize of course *)
     rw (int_rem_def :: List.concat [all_rem_defs, all_add_defs, all_sub_defs, all_mul_defs, all_div_defs, all_mk_int_defs, all_to_int_bounds_lemmas, all_conversion_id_lemmas]) >>
     fs (int_rem_def :: List.concat [all_rem_defs, all_add_defs, all_sub_defs, all_mul_defs, all_div_defs, all_mk_int_defs, all_to_int_bounds_lemmas, all_conversion_id_lemmas]) >>
     inst_first_lem x all_to_int_bounds_lemmas >>
     inst_first_lem y all_to_int_bounds_lemmas >>
     gs [NOT_LE_EQ_GT, NOT_LT_EQ_GE, NOT_GE_EQ_LT, NOT_GT_EQ_LE, GE_EQ_LE, GT_EQ_LT] >>
     TRY COOPER_TAC >>
     FIRST [
       (* For division *)
       qspecl_then [‘^x_to_int’, ‘^y_to_int’] ASSUME_TAC POS_DIV_POS_IS_POS >>
       qspecl_then [‘^x_to_int’, ‘^y_to_int’] ASSUME_TAC POS_DIV_POS_LE_INIT >>
       COOPER_TAC,
       (* For remainder *)
       dep_rewrite.DEP_PURE_ONCE_REWRITE_TAC all_conversion_id_lemmas >> fs [] >>
       qspecl_then [‘^x_to_int’, ‘^y_to_int’] ASSUME_TAC POS_MOD_POS_IS_POS >>
       qspecl_then [‘^x_to_int’, ‘^y_to_int’] ASSUME_TAC POS_MOD_POS_LE_INIT >>
       COOPER_TAC,
       dep_rewrite.DEP_PURE_ONCE_REWRITE_TAC all_conversion_id_lemmas >> fs []
     ]) (asms, g)
  end

Theorem U8_ADD_EQ:
  !x y.
    u8_to_int x + u8_to_int y <= u8_max ==>
    ?z. u8_add x y = Return z /\ u8_to_int z = u8_to_int x + u8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U16_ADD_EQ:
  !(x y).
    u16_to_int x + u16_to_int y <= u16_max ==>
    ?(z). u16_add x y = Return z /\ u16_to_int z = u16_to_int x + u16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U32_ADD_EQ:
  !x y.
    u32_to_int x + u32_to_int y <= u32_max ==>
    ?z. u32_add x y = Return z /\ u32_to_int z = u32_to_int x + u32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U64_ADD_EQ:
  !x y.
    u64_to_int x + u64_to_int y <= u64_max ==>
    ?z. u64_add x y = Return z /\ u64_to_int z = u64_to_int x + u64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U128_ADD_EQ:
  !x y.
    u128_to_int x + u128_to_int y <= u128_max ==>
    ?z. u128_add x y = Return z /\ u128_to_int z = u128_to_int x + u128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem USIZE_ADD_EQ:
  !x y.
    (usize_to_int x + usize_to_int y <= u16_max) \/ (usize_to_int x + usize_to_int y <= usize_max) ==>
    ?z. usize_add x y = Return z /\ usize_to_int z = usize_to_int x + usize_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I8_ADD_EQ:
  !x y.
    i8_min <= i8_to_int x + i8_to_int y ==>
    i8_to_int x + i8_to_int y <= i8_max ==>
    ?z. i8_add x y = Return z /\ i8_to_int z = i8_to_int x + i8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I16_ADD_EQ:
  !x y.
    i16_min <= i16_to_int x + i16_to_int y ==>
    i16_to_int x + i16_to_int y <= i16_max ==>
    ?z. i16_add x y = Return z /\ i16_to_int z = i16_to_int x + i16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I32_ADD_EQ:
  !x y.
    i32_min <= i32_to_int x + i32_to_int y ==>
    i32_to_int x + i32_to_int y <= i32_max ==>
    ?z. i32_add x y = Return z /\ i32_to_int z = i32_to_int x + i32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I64_ADD_EQ:
  !x y.
    i64_min <= i64_to_int x + i64_to_int y ==>
    i64_to_int x + i64_to_int y <= i64_max ==>
    ?z. i64_add x y = Return z /\ i64_to_int z = i64_to_int x + i64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I128_ADD_EQ:
  !x y.
    i128_min <= i128_to_int x + i128_to_int y ==>
    i128_to_int x + i128_to_int y <= i128_max ==>
    ?z. i128_add x y = Return z /\ i128_to_int z = i128_to_int x + i128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem ISIZE_ADD_EQ:
  !x y.
    (i16_min <= isize_to_int x + isize_to_int y \/ isize_min <= isize_to_int x + isize_to_int y) ==>
    (isize_to_int x + isize_to_int y <= i16_max \/ isize_to_int x + isize_to_int y <= isize_max) ==>
    ?z. isize_add x y = Return z /\ isize_to_int z = isize_to_int x + isize_to_int y
Proof
  prove_arith_op_eq
QED

val all_add_eqs = [
  ISIZE_ADD_EQ,
  I8_ADD_EQ,
  I16_ADD_EQ,
  I32_ADD_EQ,
  I64_ADD_EQ,
  I128_ADD_EQ,
  USIZE_ADD_EQ,
  U8_ADD_EQ,
  U16_ADD_EQ,
  U32_ADD_EQ,
  U64_ADD_EQ,
  U128_ADD_EQ
]
      
Theorem U8_SUB_EQ:
  !x y.
    0 <= u8_to_int x - u8_to_int y ==>
    ?z. u8_sub x y = Return z /\ u8_to_int z = u8_to_int x - u8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U16_SUB_EQ:
  !x y.
    0 <= u16_to_int x - u16_to_int y ==>
    ?z. u16_sub x y = Return z /\ u16_to_int z = u16_to_int x - u16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U32_SUB_EQ:
  !x y.
    0 <= u32_to_int x - u32_to_int y ==>
    ?z. u32_sub x y = Return z /\ u32_to_int z = u32_to_int x - u32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U64_SUB_EQ:
  !x y.
    0 <= u64_to_int x - u64_to_int y ==>
    ?z. u64_sub x y = Return z /\ u64_to_int z = u64_to_int x - u64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U128_SUB_EQ:
  !x y.
    0 <= u128_to_int x - u128_to_int y ==>
    ?z. u128_sub x y = Return z /\ u128_to_int z = u128_to_int x - u128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem USIZE_SUB_EQ:
  !x y.
    0 <= usize_to_int x - usize_to_int y ==>
    ?z. usize_sub x y = Return z /\ usize_to_int z = usize_to_int x - usize_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I8_SUB_EQ:
  !x y.
    i8_min <= i8_to_int x - i8_to_int y ==>
    i8_to_int x - i8_to_int y <= i8_max ==>
    ?z. i8_sub x y = Return z /\ i8_to_int z = i8_to_int x - i8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I16_SUB_EQ:
  !x y.
    i16_min <= i16_to_int x - i16_to_int y ==>
    i16_to_int x - i16_to_int y <= i16_max ==>
    ?z. i16_sub x y = Return z /\ i16_to_int z = i16_to_int x - i16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I32_SUB_EQ:
  !x y.
    i32_min <= i32_to_int x - i32_to_int y ==>
    i32_to_int x - i32_to_int y <= i32_max ==>
    ?z. i32_sub x y = Return z /\ i32_to_int z = i32_to_int x - i32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I64_SUB_EQ:
  !x y.
    i64_min <= i64_to_int x - i64_to_int y ==>
    i64_to_int x - i64_to_int y <= i64_max ==>
    ?z. i64_sub x y = Return z /\ i64_to_int z = i64_to_int x - i64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I128_SUB_EQ:
  !x y.
    i128_min <= i128_to_int x - i128_to_int y ==>
    i128_to_int x - i128_to_int y <= i128_max ==>
    ?z. i128_sub x y = Return z /\ i128_to_int z = i128_to_int x - i128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem ISIZE_SUB_EQ:
  !x y.
    (i16_min <= isize_to_int x - isize_to_int y \/ isize_min <= isize_to_int x - isize_to_int y) ==>
    (isize_to_int x - isize_to_int y <= i16_max \/ isize_to_int x - isize_to_int y <= isize_max) ==>
    ?z. isize_sub x y = Return z /\ isize_to_int z = isize_to_int x - isize_to_int y
Proof
  prove_arith_op_eq
QED

val all_sub_eqs = [
  ISIZE_SUB_EQ,
  I8_SUB_EQ,
  I16_SUB_EQ,
  I32_SUB_EQ,
  I64_SUB_EQ,
  I128_SUB_EQ,
  USIZE_SUB_EQ,
  U8_SUB_EQ,
  U16_SUB_EQ,
  U32_SUB_EQ,
  U64_SUB_EQ,
  U128_SUB_EQ
]

Theorem U8_MUL_EQ:
  !x y.
    u8_to_int x * u8_to_int y <= u8_max ==>
    ?z. u8_mul x y = Return z /\ u8_to_int z = u8_to_int x * u8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U16_MUL_EQ:
  !x y.
    u16_to_int x * u16_to_int y <= u16_max ==>
    ?z. u16_mul x y = Return z /\ u16_to_int z = u16_to_int x * u16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U32_MUL_EQ:
  !x y.
    u32_to_int x * u32_to_int y <= u32_max ==>
    ?z. u32_mul x y = Return z /\ u32_to_int z = u32_to_int x * u32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U64_MUL_EQ:
  !x y.
    u64_to_int x * u64_to_int y <= u64_max ==>
    ?z. u64_mul x y = Return z /\ u64_to_int z = u64_to_int x * u64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U128_MUL_EQ:
  !x y.
    u128_to_int x * u128_to_int y <= u128_max ==>
    ?z. u128_mul x y = Return z /\ u128_to_int z = u128_to_int x * u128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem USIZE_MUL_EQ:
  !x y.
    (usize_to_int x * usize_to_int y <= u16_max) \/ (usize_to_int x * usize_to_int y <= usize_max) ==>
    ?z. usize_mul x y = Return z /\ usize_to_int z = usize_to_int x * usize_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I8_MUL_EQ:
  !x y.
    i8_min <= i8_to_int x * i8_to_int y ==>
    i8_to_int x * i8_to_int y <= i8_max ==>
    ?z. i8_mul x y = Return z /\ i8_to_int z = i8_to_int x * i8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I16_MUL_EQ:
  !x y.
    i16_min <= i16_to_int x * i16_to_int y ==>
    i16_to_int x * i16_to_int y <= i16_max ==>
    ?z. i16_mul x y = Return z /\ i16_to_int z = i16_to_int x * i16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I32_MUL_EQ:
  !x y.
    i32_min <= i32_to_int x * i32_to_int y ==>
    i32_to_int x * i32_to_int y <= i32_max ==>
    ?z. i32_mul x y = Return z /\ i32_to_int z = i32_to_int x * i32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I64_MUL_EQ:
  !x y.
    i64_min <= i64_to_int x * i64_to_int y ==>
    i64_to_int x * i64_to_int y <= i64_max ==>
    ?z. i64_mul x y = Return z /\ i64_to_int z = i64_to_int x * i64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I128_MUL_EQ:
  !x y.
    i128_min <= i128_to_int x * i128_to_int y ==>
    i128_to_int x * i128_to_int y <= i128_max ==>
    ?z. i128_mul x y = Return z /\ i128_to_int z = i128_to_int x * i128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem ISIZE_MUL_EQ:
  !x y.
    (i16_min <= isize_to_int x * isize_to_int y \/ isize_min <= isize_to_int x * isize_to_int y) ==>
    (isize_to_int x * isize_to_int y <= i16_max \/ isize_to_int x * isize_to_int y <= isize_max) ==>
    ?z. isize_mul x y = Return z /\ isize_to_int z = isize_to_int x * isize_to_int y
Proof
  prove_arith_op_eq
QED

val all_mul_eqs = [
  ISIZE_MUL_EQ,
  I8_MUL_EQ,
  I16_MUL_EQ,
  I32_MUL_EQ,
  I64_MUL_EQ,
  I128_MUL_EQ,
  USIZE_MUL_EQ,
  U8_MUL_EQ,
  U16_MUL_EQ,
  U32_MUL_EQ,
  U64_MUL_EQ,
  U128_MUL_EQ
]

Theorem U8_DIV_EQ:
  !x y.
    u8_to_int y <> 0 ==>
    ?z. u8_div x y = Return z /\ u8_to_int z = u8_to_int x / u8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U16_DIV_EQ:
  !x y.
    u16_to_int y <> 0 ==>
    ?z. u16_div x y = Return z /\ u16_to_int z = u16_to_int x / u16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U32_DIV_EQ:
  !x y.
    u32_to_int y <> 0 ==>
    ?z. u32_div x y = Return z /\ u32_to_int z = u32_to_int x / u32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U64_DIV_EQ:
  !x y.
    u64_to_int y <> 0 ==>
    ?z. u64_div x y = Return z /\ u64_to_int z = u64_to_int x / u64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U128_DIV_EQ:
  !x y.
    u128_to_int y <> 0 ==>
    ?z. u128_div x y = Return z /\ u128_to_int z = u128_to_int x / u128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem USIZE_DIV_EQ:
  !x y.
    usize_to_int y <> 0 ==>
    ?z. usize_div x y = Return z /\ usize_to_int z = usize_to_int x / usize_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I8_DIV_EQ:
  !x y.
    i8_to_int y <> 0 ==>
    i8_min <= i8_to_int x / i8_to_int y ==>
    i8_to_int x / i8_to_int y <= i8_max ==>
    ?z. i8_div x y = Return z /\ i8_to_int z = i8_to_int x / i8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I16_DIV_EQ:
  !x y.
    i16_to_int y <> 0 ==>
    i16_min <= i16_to_int x / i16_to_int y ==>
    i16_to_int x / i16_to_int y <= i16_max ==>
    ?z. i16_div x y = Return z /\ i16_to_int z = i16_to_int x / i16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I32_DIV_EQ:
  !x y.
    i32_to_int y <> 0 ==>
    i32_min <= i32_to_int x / i32_to_int y ==>
    i32_to_int x / i32_to_int y <= i32_max ==>
    ?z. i32_div x y = Return z /\ i32_to_int z = i32_to_int x / i32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I64_DIV_EQ:
  !x y.
    i64_to_int y <> 0 ==>
    i64_min <= i64_to_int x / i64_to_int y ==>
    i64_to_int x / i64_to_int y <= i64_max ==>
    ?z. i64_div x y = Return z /\ i64_to_int z = i64_to_int x / i64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I128_DIV_EQ:
  !x y.
    i128_to_int y <> 0 ==>
    i128_min <= i128_to_int x / i128_to_int y ==>
    i128_to_int x / i128_to_int y <= i128_max ==>
    ?z. i128_div x y = Return z /\ i128_to_int z = i128_to_int x / i128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem ISIZE_DIV_EQ:
  !x y.
    isize_to_int y <> 0 ==>
    (i16_min <= isize_to_int x / isize_to_int y \/ isize_min <= isize_to_int x / isize_to_int y) ==>
    (isize_to_int x / isize_to_int y <= i16_max \/ isize_to_int x / isize_to_int y <= isize_max) ==>
    ?z. isize_div x y = Return z /\ isize_to_int z = isize_to_int x / isize_to_int y
Proof
  prove_arith_op_eq
QED

val all_div_eqs = [
  ISIZE_DIV_EQ,
  I8_DIV_EQ,
  I16_DIV_EQ,
  I32_DIV_EQ,
  I64_DIV_EQ,
  I128_DIV_EQ,
  USIZE_DIV_EQ,
  U8_DIV_EQ,
  U16_DIV_EQ,
  U32_DIV_EQ,
  U64_DIV_EQ,
  U128_DIV_EQ
]

Theorem U8_REM_EQ:
  !x y.
    u8_to_int y <> 0 ==>
    ?z. u8_rem x y = Return z /\ u8_to_int z = int_rem (u8_to_int x) (u8_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem U16_REM_EQ:
  !x y.
    u16_to_int y <> 0 ==>
    ?z. u16_rem x y = Return z /\ u16_to_int z = int_rem (u16_to_int x) (u16_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem U32_REM_EQ:
  !x y.
    u32_to_int y <> 0 ==>
    ?z. u32_rem x y = Return z /\ u32_to_int z = int_rem (u32_to_int x) (u32_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem U64_REM_EQ:
  !x y.
    u64_to_int y <> 0 ==>
    ?z. u64_rem x y = Return z /\ u64_to_int z = int_rem (u64_to_int x) (u64_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem U128_REM_EQ:
  !x y.
    u128_to_int y <> 0 ==>
    ?z. u128_rem x y = Return z /\ u128_to_int z = int_rem (u128_to_int x) (u128_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem USIZE_REM_EQ:
  !x y.
    usize_to_int y <> 0 ==>
    ?z. usize_rem x y = Return z /\ usize_to_int z = int_rem (usize_to_int x) (usize_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem I8_REM_EQ:
  !x y.
    i8_to_int y <> 0 ==>
    i8_min <= int_rem (i8_to_int x) (i8_to_int y) ==>
    int_rem (i8_to_int x) (i8_to_int y) <= i8_max ==>
    ?z. i8_rem x y = Return z /\ i8_to_int z = int_rem (i8_to_int x) (i8_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem I16_REM_EQ:
  !x y.
    i16_to_int y <> 0 ==>
    i16_min <= int_rem (i16_to_int x) (i16_to_int y) ==>
    int_rem (i16_to_int x) (i16_to_int y) <= i16_max ==>
    ?z. i16_rem x y = Return z /\ i16_to_int z = int_rem (i16_to_int x) (i16_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem I32_REM_EQ:
  !x y.
    i32_to_int y <> 0 ==>
    i32_min <= int_rem (i32_to_int x) (i32_to_int y) ==>
    int_rem (i32_to_int x) (i32_to_int y) <= i32_max ==>
    ?z. i32_rem x y = Return z /\ i32_to_int z = int_rem (i32_to_int x) (i32_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem I64_REM_EQ:
  !x y.
    i64_to_int y <> 0 ==>
    i64_min <= int_rem (i64_to_int x) (i64_to_int y) ==>
    int_rem (i64_to_int x) (i64_to_int y) <= i64_max ==>
    ?z. i64_rem x y = Return z /\ i64_to_int z = int_rem (i64_to_int x) (i64_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem I8_REM_EQ:
  !x y.
    i8_to_int y <> 0 ==>
    i8_min <= int_rem (i8_to_int x) (i8_to_int y) ==>
    int_rem (i8_to_int x) (i8_to_int y) <= i8_max ==>
    ?z. i8_rem x y = Return z /\ i8_to_int z = int_rem (i8_to_int x) (i8_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem I8_REM_EQ:
  !x y.
    i8_to_int y <> 0 ==>
    i8_min <= int_rem (i8_to_int x) (i8_to_int y) ==>
    int_rem (i8_to_int x) (i8_to_int y) <= i8_max ==>
    ?z. i8_rem x y = Return z /\ i8_to_int z = int_rem (i8_to_int x) (i8_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem U16_DIV_EQ:
  !x y.
    u16_to_int y <> 0 ==>
    ?z. u16_div x y = Return z /\ u16_to_int z = u16_to_int x / u16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U32_DIV_EQ:
  !x y.
    u32_to_int y <> 0 ==>
    ?z. u32_div x y = Return z /\ u32_to_int z = u32_to_int x / u32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U64_DIV_EQ:
  !x y.
    u64_to_int y <> 0 ==>
    ?z. u64_div x y = Return z /\ u64_to_int z = u64_to_int x / u64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem U128_DIV_EQ:
  !x y.
    u128_to_int y <> 0 ==>
    ?z. u128_div x y = Return z /\ u128_to_int z = u128_to_int x / u128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem USIZE_DIV_EQ:
  !x y.
    usize_to_int y <> 0 ==>
    ?z. usize_div x y = Return z /\ usize_to_int z = usize_to_int x / usize_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I8_DIV_EQ:
  !x y.
    i8_to_int y <> 0 ==>
    i8_min <= i8_to_int x / i8_to_int y ==>
    i8_to_int x / i8_to_int y <= i8_max ==>
    ?z. i8_div x y = Return z /\ i8_to_int z = i8_to_int x / i8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I16_DIV_EQ:
  !x y.
    i16_to_int y <> 0 ==>
    i16_min <= i16_to_int x / i16_to_int y ==>
    i16_to_int x / i16_to_int y <= i16_max ==>
    ?z. i16_div x y = Return z /\ i16_to_int z = i16_to_int x / i16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I32_DIV_EQ:
  !x y.
    i32_to_int y <> 0 ==>
    i32_min <= i32_to_int x / i32_to_int y ==>
    i32_to_int x / i32_to_int y <= i32_max ==>
    ?z. i32_div x y = Return z /\ i32_to_int z = i32_to_int x / i32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I64_DIV_EQ:
  !x y.
    i64_to_int y <> 0 ==>
    i64_min <= i64_to_int x / i64_to_int y ==>
    i64_to_int x / i64_to_int y <= i64_max ==>
    ?z. i64_div x y = Return z /\ i64_to_int z = i64_to_int x / i64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem I128_DIV_EQ:
  !x y.
    i128_to_int y <> 0 ==>
    i128_min <= i128_to_int x / i128_to_int y ==>
    i128_to_int x / i128_to_int y <= i128_max ==>
    ?z. i128_div x y = Return z /\ i128_to_int z = i128_to_int x / i128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem ISIZE_DIV_EQ:
  !x y.
    isize_to_int y <> 0 ==>
    (i16_min <= isize_to_int x / isize_to_int y \/ isize_min <= isize_to_int x / isize_to_int y) ==>
    (isize_to_int x / isize_to_int y <= i16_max \/ isize_to_int x / isize_to_int y <= isize_max) ==>
    ?z. isize_div x y = Return z /\ isize_to_int z = isize_to_int x / isize_to_int y
Proof
  prove_arith_op_eq
QED

val all_div_eqs = [
  ISIZE_DIV_EQ,
  I8_DIV_EQ,
  I16_DIV_EQ,
  I32_DIV_EQ,
  I64_DIV_EQ,
  I128_DIV_EQ,
  USIZE_DIV_EQ,
  U8_DIV_EQ,
  U16_DIV_EQ,
  U32_DIV_EQ,
  U64_DIV_EQ,
  U128_DIV_EQ
]

val _ = export_theory ()
