open HolKernel boolLib bossLib Parse
open boolTheory arithmeticTheory integerTheory intLib listTheory stringTheory

val primitives_theory_name = "Primitives"
val _ = new_theory primitives_theory_name

(* TODO: val _ = export_theory(); *)

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

val isize_mod_def = Define ‘isize_mod x y =
  if isize_to_int y = 0 then Fail Failure else mk_isize ((isize_to_int x) % (isize_to_int y))’
val i8_mod_def = Define ‘i8_mod x y =
  if i8_to_int y = 0 then Fail Failure else mk_i8 ((i8_to_int x) % (i8_to_int y))’
val i16_mod_def = Define ‘i16_mod x y =
  if i16_to_int y = 0 then Fail Failure else mk_i16 ((i16_to_int x) % (i16_to_int y))’
val i32_mod_def = Define ‘i32_mod x y =
  if i32_to_int y = 0 then Fail Failure else mk_i32 ((i32_to_int x) % (i32_to_int y))’
val i64_mod_def = Define ‘i64_mod x y =
  if i64_to_int y = 0 then Fail Failure else mk_i64 ((i64_to_int x) % (i64_to_int y))’
val i128_mod_def = Define ‘i128_mod x y =
  if i128_to_int y = 0 then Fail Failure else mk_i128 ((i128_to_int x) % (i128_to_int y))’
val usize_mod_def = Define ‘usize_mod x y =
  if usize_to_int y = 0 then Fail Failure else mk_usize ((usize_to_int x) % (usize_to_int y))’
val u8_mod_def = Define ‘u8_mod x y =
  if u8_to_int y = 0 then Fail Failure else mk_u8 ((u8_to_int x) % (u8_to_int y))’
val u16_mod_def = Define ‘u16_mod x y =
  if u16_to_int y = 0 then Fail Failure else mk_u16 ((u16_to_int x) % (u16_to_int y))’
val u32_mod_def = Define ‘u32_mod x y =
  if u32_to_int y = 0 then Fail Failure else mk_u32 ((u32_to_int x) % (u32_to_int y))’
val u64_mod_def = Define ‘u64_mod x y =
  if u64_to_int y = 0 then Fail Failure else mk_u64 ((u64_to_int x) % (u64_to_int y))’
val u128_mod_def = Define ‘u128_mod x y =
  if u128_to_int y = 0 then Fail Failure else mk_u128 ((u128_to_int x) % (u128_to_int y))’
