open stringTheory
open primitivesArithTheory primitivesBaseTacLib ilistTheory

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

Theorem bind_return_fail_div_eq:
  (bind (Return x) f = f x) ∧ (bind (Fail e) f = Fail e) ∧ (bind Diverge f = Diverge)
Proof
  fs [bind_def]
QED
val _ = BasicProvers.export_rewrites ["bind_return_fail_div_eq"]

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
val isize_bounds = new_axiom ("isize_bounds", “isize_min <= i16_min /\ i16_max <= isize_max”)
val usize_bounds = new_axiom ("usize_bounds", “u16_max <= usize_max”)

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

val all_int_to_scalar_to_int_lemmas = [
  isize_to_int_int_to_isize,
  i8_to_int_int_to_i8,
  i16_to_int_int_to_i16,
  i32_to_int_int_to_i32,
  i64_to_int_int_to_i64,
  i128_to_int_int_to_i128,
  usize_to_int_int_to_usize,
  u8_to_int_int_to_u8,
  u16_to_int_int_to_u16,
  u32_to_int_int_to_u32,
  u64_to_int_int_to_u64,
  u128_to_int_int_to_u128
]

(* Additional conversion lemmas  for isize/usize *)
Theorem isize_to_int_int_to_isize_i16_bounds:
  !n. i16_min <= n /\ n <= i16_max ==> isize_to_int (int_to_isize n) = n
Proof
  rw [] >> irule isize_to_int_int_to_isize >>
  assume_tac isize_bounds >>
  int_tac
QED

Theorem usize_to_int_int_to_usize_u16_bounds:
  !n. 0 <= n /\ n <= u16_max ==> usize_to_int (int_to_usize n) = n
Proof
  rw [] >> irule usize_to_int_int_to_usize >>
  assume_tac usize_bounds >>
  int_tac
QED

val prove_int_to_scalar_to_int_unfold_tac =
  assume_tac isize_bounds >> (* Only useful for isize of course *)
  assume_tac usize_bounds >> (* Only useful for usize of course *)
  rw [] >> MAP_FIRST irule all_int_to_scalar_to_int_lemmas >> int_tac

(* Custom unfolding lemmas for the purpose of evaluation *)

(* For isize, we don't use isize_{min,max} (which are opaque) but i16_{min,max} *)
Theorem isize_to_int_int_to_isize_unfold:
  ∀n. isize_to_int (int_to_isize n) = if i16_min <= n /\ n <= i16_max then n else isize_to_int (int_to_isize n)
Proof
  prove_int_to_scalar_to_int_unfold_tac
QED

Theorem i8_to_int_int_to_i8_unfold:
  ∀n. i8_to_int (int_to_i8 n) = if i8_min <= n /\ n <= i8_max then n else i8_to_int (int_to_i8 n)
Proof
  prove_int_to_scalar_to_int_unfold_tac
QED

Theorem i16_to_int_int_to_i16_unfold:
  ∀n. i16_to_int (int_to_i16 n) = if i16_min <= n /\ n <= i16_max then n else i16_to_int (int_to_i16 n)
Proof
  prove_int_to_scalar_to_int_unfold_tac
QED

Theorem i32_to_int_int_to_i32_unfold:
  ∀n. i32_to_int (int_to_i32 n) = if i32_min <= n /\ n <= i32_max then n else i32_to_int (int_to_i32 n)
Proof
  prove_int_to_scalar_to_int_unfold_tac
QED

Theorem i64_to_int_int_to_i64_unfold:
  ∀n. i64_to_int (int_to_i64 n) = if i64_min <= n /\ n <= i64_max then n else i64_to_int (int_to_i64 n)
Proof
  prove_int_to_scalar_to_int_unfold_tac
QED

Theorem i128_to_int_int_to_i128_unfold:
  ∀n. i128_to_int (int_to_i128 n) = if i128_min <= n /\ n <= i128_max then n else i128_to_int (int_to_i128 n)
Proof
  prove_int_to_scalar_to_int_unfold_tac
QED

(* For usize, we don't use isize_{min,max} (which are opaque) but u16_{min,max} *)
Theorem usize_to_int_int_to_usize_unfold:
  ∀n. usize_to_int (int_to_usize n) = if 0 ≤ n ∧ n <= u16_max then n else usize_to_int (int_to_usize n)
Proof
  prove_int_to_scalar_to_int_unfold_tac
QED

Theorem u8_to_int_int_to_u8_unfold:
  ∀n. u8_to_int (int_to_u8 n) = if 0 <= n /\ n <= u8_max then n else u8_to_int (int_to_u8 n)
Proof
  prove_int_to_scalar_to_int_unfold_tac
QED

Theorem u16_to_int_int_to_u16_unfold:
  ∀n. u16_to_int (int_to_u16 n) = if 0 <= n /\ n <= u16_max then n else u16_to_int (int_to_u16 n)
Proof
  prove_int_to_scalar_to_int_unfold_tac
QED

Theorem u32_to_int_int_to_u32_unfold:
  ∀n. u32_to_int (int_to_u32 n) = if 0 <= n /\ n <= u32_max then n else u32_to_int (int_to_u32 n)
Proof
  prove_int_to_scalar_to_int_unfold_tac
QED

Theorem u64_to_int_int_to_u64_unfold:
  ∀n. u64_to_int (int_to_u64 n) = if 0 <= n /\ n <= u64_max then n else u64_to_int (int_to_u64 n)
Proof
  prove_int_to_scalar_to_int_unfold_tac
QED

Theorem u128_to_int_int_to_u128_unfold:
  ∀n. u128_to_int (int_to_u128 n) = if 0 <= n /\ n <= u128_max then n else u128_to_int (int_to_u128 n)
Proof
  prove_int_to_scalar_to_int_unfold_tac
QED

val all_int_to_scalar_to_int_unfold_lemmas = [
  isize_to_int_int_to_isize_unfold,
  i8_to_int_int_to_i8_unfold,
  i16_to_int_int_to_i16_unfold,
  i32_to_int_int_to_i32_unfold,
  i64_to_int_int_to_i64_unfold,
  i128_to_int_int_to_i128_unfold,
  usize_to_int_int_to_usize_unfold,
  u8_to_int_int_to_u8_unfold,
  u16_to_int_int_to_u16_unfold,
  u32_to_int_int_to_u32_unfold,
  u64_to_int_int_to_u64_unfold,
  u128_to_int_int_to_u128_unfold
]

val _ = evalLib.add_unfold_thms [
  "isize_to_int_int_to_isize_unfold",
  "i8_to_int_int_to_i8_unfold",
  "i16_to_int_int_to_i16_unfold",
  "i32_to_int_int_to_i32_unfold",
  "i64_to_int_int_to_i64_unfold",
  "i128_to_int_int_to_i128_unfold",
  "usize_to_int_int_to_usize_unfold",
  "u8_to_int_int_to_u8_unfold",
  "u16_to_int_int_to_u16_unfold",
  "u32_to_int_int_to_u32_unfold",
  "u64_to_int_int_to_u64_unfold",
  "u128_to_int_int_to_u128_unfold"
]

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

val all_scalar_to_int_to_scalar_lemmas = [
  int_to_i8_i8_to_int,
  int_to_i16_i16_to_int,
  int_to_i32_i32_to_int,
  int_to_i64_i64_to_int,
  int_to_i128_i128_to_int,
  int_to_isize_isize_to_int,
  int_to_u8_u8_to_int,
  int_to_u16_u16_to_int,
  int_to_u32_u32_to_int,
  int_to_u64_u64_to_int,
  int_to_u128_u128_to_int,
  int_to_usize_usize_to_int
]

val _ = BasicProvers.export_rewrites [
  "int_to_i8_i8_to_int",
  "int_to_i16_i16_to_int",
  "int_to_i32_i32_to_int",
  "int_to_i64_i64_to_int",
  "int_to_i128_i128_to_int",
  "int_to_isize_isize_to_int",
  "int_to_u8_u8_to_int",
  "int_to_u16_u16_to_int",
  "int_to_u32_u32_to_int",
  "int_to_u64_u64_to_int",
  "int_to_u128_u128_to_int",
  "int_to_usize_usize_to_int"
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

(* Unfolding theorems for “mk_usize” and “mk_isize”: we need specific unfolding
   theorems because the isize/usize bounds are opaque, and may make the evaluation
   get stuck in the unit tests *)
Theorem mk_usize_unfold:
  ∀ n. mk_usize n =
    if 0 ≤ n ∧ (n ≤ u16_max ∨ n ≤ usize_max) then Return (int_to_usize n)
    else Fail Failure
Proof
  rw [mk_usize_def] >> fs [] >>
  assume_tac usize_bounds >>
  int_tac
QED
val _ = evalLib.add_unfold_thm "mk_usize_unfold"

Theorem mk_isize_unfold:
  ∀ n. mk_isize n =
    if (i16_min ≤ n ∨ isize_min ≤ n) ∧
       (n ≤ i16_max ∨ n ≤ isize_max)
    then Return (int_to_isize n)
    else Fail Failure
Proof
  rw [mk_isize_def] >> fs [] >>
  assume_tac isize_bounds >>
  int_tac
QED
val _ = evalLib.add_unfold_thm "mk_isize_unfold"

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

val all_neg_defs = [
  isize_neg_def,
  i8_neg_def,
  i16_neg_def,
  i32_neg_def,
  i64_neg_def,
  i128_neg_def
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
  if (0 ≤ x /\ 0 ≤ y) \/ (x < 0 /\ y < 0) then x % y else -(x % y)’

(* Checking consistency with Rust *)
val _ = prove(“int_rem 1 2 = 1”, EVAL_TAC)
val _ = prove(“int_rem (-1) 2 = -1”, EVAL_TAC)
val _ = prove(“int_rem 1 (-2) = 1”, EVAL_TAC)
val _ = prove(“int_rem (-1) (-2) = -1”, EVAL_TAC)

Theorem pos_rem_pos_ineqs:
  ∀x y. 0 ≤ x ⇒ 0 < y ⇒ 0 ≤ int_rem x y ∧ int_rem x y < y
Proof
  rw [int_rem_def] >> metis_tac [pos_mod_pos_ineqs]
QED

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

(*
val (asms,g) = top_goal ()
*)

fun prove_arith_unop_eq (asms, g) =
  let
    val rw_thms = List.concat [all_neg_defs, all_mk_int_defs, all_int_to_scalar_to_int_lemmas]
  in
    (rpt gen_tac >>
     rpt disch_tac >>
     assume_tac isize_bounds >> (* Only useful for isize of course *)
     rw rw_thms) (asms, g)
  end

Theorem isize_neg_eq:
  !x y.
    isize_min ≤ - isize_to_int x ⇒
    - isize_to_int x ≤ isize_max ⇒
    ?y. isize_neg x = Return y /\ isize_to_int y = - isize_to_int x
Proof
  prove_arith_unop_eq
QED

Theorem i8_neg_eq:
  !x y.
    i8_min ≤ - i8_to_int x ⇒
    - i8_to_int x ≤ i8_max ⇒
    ?y. i8_neg x = Return y /\ i8_to_int y = - i8_to_int x
Proof
  prove_arith_unop_eq
QED

Theorem i16_neg_eq:
  !x y.
    i16_min ≤ - i16_to_int x ⇒
    - i16_to_int x ≤ i16_max ⇒
    ?y. i16_neg x = Return y /\ i16_to_int y = - i16_to_int x
Proof
  prove_arith_unop_eq
QED

Theorem i32_neg_eq:
  !x y.
    i32_min ≤ - i32_to_int x ⇒
    - i32_to_int x ≤ i32_max ⇒
    ?y. i32_neg x = Return y /\ i32_to_int y = - i32_to_int x
Proof
  prove_arith_unop_eq
QED

Theorem i64_neg_eq:
  !x y.
    i64_min ≤ - i64_to_int x ⇒
    - i64_to_int x ≤ i64_max ⇒
    ?y. i64_neg x = Return y /\ i64_to_int y = - i64_to_int x
Proof
  prove_arith_unop_eq
QED

Theorem i128_neg_eq:
  !x y.
    i128_min ≤ - i128_to_int x ⇒
    - i128_to_int x ≤ i128_max ⇒
    ?y. i128_neg x = Return y /\ i128_to_int y = - i128_to_int x
Proof
  prove_arith_unop_eq
QED


fun prove_arith_op_eq (asms, g) =
  let
    val (_, t) = (dest_exists o snd o strip_imp o snd o strip_forall) g;
    val (x_to_int, y_to_int) =
      case (snd o strip_comb o rhs o snd o dest_conj) t of
        [x, y] => (x,y)
      | _ => failwith "Unexpected"
    val x = (snd o dest_comb) x_to_int;
    val y = (snd o dest_comb) y_to_int;
    val rw_thms = int_rem_def :: List.concat [all_rem_defs, all_add_defs, all_sub_defs, all_mul_defs, all_div_defs, all_mk_int_defs, all_to_int_bounds_lemmas, all_int_to_scalar_to_int_lemmas];
    fun inst_first_lem arg lems =
      map_first_tac (fn th => (assume_tac (SPEC arg th) handle HOL_ERR _ => fail_tac "")) lems;
  in
    (rpt gen_tac >>
     rpt disch_tac >>
     assume_tac usize_bounds >> (* Only useful for usize of course *)
     assume_tac isize_bounds >> (* Only useful for isize of course *)
     rw rw_thms >>
     fs rw_thms >>
     inst_first_lem x all_to_int_bounds_lemmas >>
     inst_first_lem y all_to_int_bounds_lemmas >>
     gs [not_le_eq_gt, not_lt_eq_ge, not_ge_eq_lt, not_gt_eq_le, ge_eq_le, gt_eq_lt] >>
     try_tac cooper_tac >>
     first_tac [
       (* For division *)
       qspecl_assume [‘^x_to_int’, ‘^y_to_int’] pos_div_pos_is_pos >>
       qspecl_assume [‘^x_to_int’, ‘^y_to_int’] pos_div_pos_le_init >>
       cooper_tac,
       (* For remainder *)
       dep_rewrite.DEP_PURE_ONCE_REWRITE_TAC all_int_to_scalar_to_int_lemmas >> fs [] >>
       qspecl_assume [‘^x_to_int’, ‘^y_to_int’] pos_mod_pos_is_pos >>
       qspecl_assume [‘^x_to_int’, ‘^y_to_int’] pos_mod_pos_le_init >>
       cooper_tac,
       dep_rewrite.DEP_PURE_ONCE_REWRITE_TAC all_int_to_scalar_to_int_lemmas >> fs []
     ]) (asms, g)
  end

Theorem u8_add_eq:
  !x y.
    u8_to_int x + u8_to_int y <= u8_max ⇒
    ?z. u8_add x y = Return z /\ u8_to_int z = u8_to_int x + u8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u16_add_eq:
  !(x y).
    u16_to_int x + u16_to_int y <= u16_max ⇒
    ?(z). u16_add x y = Return z /\ u16_to_int z = u16_to_int x + u16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u32_add_eq:
  !x y.
    u32_to_int x + u32_to_int y <= u32_max ⇒
    ?z. u32_add x y = Return z /\ u32_to_int z = u32_to_int x + u32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u64_add_eq:
  !x y.
    u64_to_int x + u64_to_int y <= u64_max ⇒
    ?z. u64_add x y = Return z /\ u64_to_int z = u64_to_int x + u64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u128_add_eq:
  !x y.
    u128_to_int x + u128_to_int y <= u128_max ⇒
    ?z. u128_add x y = Return z /\ u128_to_int z = u128_to_int x + u128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem usize_add_eq:
  !x y.
    (usize_to_int x + usize_to_int y <= u16_max) \/ (usize_to_int x + usize_to_int y <= usize_max) ⇒
    ?z. usize_add x y = Return z /\ usize_to_int z = usize_to_int x + usize_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i8_add_eq:
  !x y.
    i8_min <= i8_to_int x + i8_to_int y ⇒
    i8_to_int x + i8_to_int y <= i8_max ⇒
    ?z. i8_add x y = Return z /\ i8_to_int z = i8_to_int x + i8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i16_add_eq:
  !x y.
    i16_min <= i16_to_int x + i16_to_int y ⇒
    i16_to_int x + i16_to_int y <= i16_max ⇒
    ?z. i16_add x y = Return z /\ i16_to_int z = i16_to_int x + i16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i32_add_eq:
  !x y.
    i32_min <= i32_to_int x + i32_to_int y ⇒
    i32_to_int x + i32_to_int y <= i32_max ⇒
    ?z. i32_add x y = Return z /\ i32_to_int z = i32_to_int x + i32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i64_add_eq:
  !x y.
    i64_min <= i64_to_int x + i64_to_int y ⇒
    i64_to_int x + i64_to_int y <= i64_max ⇒
    ?z. i64_add x y = Return z /\ i64_to_int z = i64_to_int x + i64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i128_add_eq:
  !x y.
    i128_min <= i128_to_int x + i128_to_int y ⇒
    i128_to_int x + i128_to_int y <= i128_max ⇒
    ?z. i128_add x y = Return z /\ i128_to_int z = i128_to_int x + i128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem isize_add_eq:
  !x y.
    (i16_min <= isize_to_int x + isize_to_int y \/ isize_min <= isize_to_int x + isize_to_int y) ⇒
    (isize_to_int x + isize_to_int y <= i16_max \/ isize_to_int x + isize_to_int y <= isize_max) ⇒
    ?z. isize_add x y = Return z /\ isize_to_int z = isize_to_int x + isize_to_int y
Proof
  prove_arith_op_eq
QED
      
Theorem u8_sub_eq:
  !x y.
    0 <= u8_to_int x - u8_to_int y ⇒
    ?z. u8_sub x y = Return z /\ u8_to_int z = u8_to_int x - u8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u16_sub_eq:
  !x y.
    0 <= u16_to_int x - u16_to_int y ⇒
    ?z. u16_sub x y = Return z /\ u16_to_int z = u16_to_int x - u16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u32_sub_eq:
  !x y.
    0 <= u32_to_int x - u32_to_int y ⇒
    ?z. u32_sub x y = Return z /\ u32_to_int z = u32_to_int x - u32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u64_sub_eq:
  !x y.
    0 <= u64_to_int x - u64_to_int y ⇒
    ?z. u64_sub x y = Return z /\ u64_to_int z = u64_to_int x - u64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u128_sub_eq:
  !x y.
    0 <= u128_to_int x - u128_to_int y ⇒
    ?z. u128_sub x y = Return z /\ u128_to_int z = u128_to_int x - u128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem usize_sub_eq:
  !x y.
    0 <= usize_to_int x - usize_to_int y ⇒
    ?z. usize_sub x y = Return z /\ usize_to_int z = usize_to_int x - usize_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i8_sub_eq:
  !x y.
    i8_min <= i8_to_int x - i8_to_int y ⇒
    i8_to_int x - i8_to_int y <= i8_max ⇒
    ?z. i8_sub x y = Return z /\ i8_to_int z = i8_to_int x - i8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i16_sub_eq:
  !x y.
    i16_min <= i16_to_int x - i16_to_int y ⇒
    i16_to_int x - i16_to_int y <= i16_max ⇒
    ?z. i16_sub x y = Return z /\ i16_to_int z = i16_to_int x - i16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i32_sub_eq:
  !x y.
    i32_min <= i32_to_int x - i32_to_int y ⇒
    i32_to_int x - i32_to_int y <= i32_max ⇒
    ?z. i32_sub x y = Return z /\ i32_to_int z = i32_to_int x - i32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i64_sub_eq:
  !x y.
    i64_min <= i64_to_int x - i64_to_int y ⇒
    i64_to_int x - i64_to_int y <= i64_max ⇒
    ?z. i64_sub x y = Return z /\ i64_to_int z = i64_to_int x - i64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i128_sub_eq:
  !x y.
    i128_min <= i128_to_int x - i128_to_int y ⇒
    i128_to_int x - i128_to_int y <= i128_max ⇒
    ?z. i128_sub x y = Return z /\ i128_to_int z = i128_to_int x - i128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem isize_sub_eq:
  !x y.
    (i16_min <= isize_to_int x - isize_to_int y \/ isize_min <= isize_to_int x - isize_to_int y) ⇒
    (isize_to_int x - isize_to_int y <= i16_max \/ isize_to_int x - isize_to_int y <= isize_max) ⇒
    ?z. isize_sub x y = Return z /\ isize_to_int z = isize_to_int x - isize_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u8_mul_eq:
  !x y.
    u8_to_int x * u8_to_int y <= u8_max ⇒
    ?z. u8_mul x y = Return z /\ u8_to_int z = u8_to_int x * u8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u16_mul_eq:
  !x y.
    u16_to_int x * u16_to_int y <= u16_max ⇒
    ?z. u16_mul x y = Return z /\ u16_to_int z = u16_to_int x * u16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u32_mul_eq:
  !x y.
    u32_to_int x * u32_to_int y <= u32_max ⇒
    ?z. u32_mul x y = Return z /\ u32_to_int z = u32_to_int x * u32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u64_mul_eq:
  !x y.
    u64_to_int x * u64_to_int y <= u64_max ⇒
    ?z. u64_mul x y = Return z /\ u64_to_int z = u64_to_int x * u64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u128_mul_eq:
  !x y.
    u128_to_int x * u128_to_int y <= u128_max ⇒
    ?z. u128_mul x y = Return z /\ u128_to_int z = u128_to_int x * u128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem usize_mul_eq:
  !x y.
    (usize_to_int x * usize_to_int y <= u16_max) \/ (usize_to_int x * usize_to_int y <= usize_max) ⇒
    ?z. usize_mul x y = Return z /\ usize_to_int z = usize_to_int x * usize_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i8_mul_eq:
  !x y.
    i8_min <= i8_to_int x * i8_to_int y ⇒
    i8_to_int x * i8_to_int y <= i8_max ⇒
    ?z. i8_mul x y = Return z /\ i8_to_int z = i8_to_int x * i8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i16_mul_eq:
  !x y.
    i16_min <= i16_to_int x * i16_to_int y ⇒
    i16_to_int x * i16_to_int y <= i16_max ⇒
    ?z. i16_mul x y = Return z /\ i16_to_int z = i16_to_int x * i16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i32_mul_eq:
  !x y.
    i32_min <= i32_to_int x * i32_to_int y ⇒
    i32_to_int x * i32_to_int y <= i32_max ⇒
    ?z. i32_mul x y = Return z /\ i32_to_int z = i32_to_int x * i32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i64_mul_eq:
  !x y.
    i64_min <= i64_to_int x * i64_to_int y ⇒
    i64_to_int x * i64_to_int y <= i64_max ⇒
    ?z. i64_mul x y = Return z /\ i64_to_int z = i64_to_int x * i64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i128_mul_eq:
  !x y.
    i128_min <= i128_to_int x * i128_to_int y ⇒
    i128_to_int x * i128_to_int y <= i128_max ⇒
    ?z. i128_mul x y = Return z /\ i128_to_int z = i128_to_int x * i128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem isize_mul_eq:
  !x y.
    (i16_min <= isize_to_int x * isize_to_int y \/ isize_min <= isize_to_int x * isize_to_int y) ⇒
    (isize_to_int x * isize_to_int y <= i16_max \/ isize_to_int x * isize_to_int y <= isize_max) ⇒
    ?z. isize_mul x y = Return z /\ isize_to_int z = isize_to_int x * isize_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u8_div_eq:
  !x y.
    u8_to_int y <> 0 ⇒
    ?z. u8_div x y = Return z /\ u8_to_int z = u8_to_int x / u8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u16_div_eq:
  !x y.
    u16_to_int y <> 0 ⇒
    ?z. u16_div x y = Return z /\ u16_to_int z = u16_to_int x / u16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u32_div_eq:
  !x y.
    u32_to_int y <> 0 ⇒
    ?z. u32_div x y = Return z /\ u32_to_int z = u32_to_int x / u32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u64_div_eq:
  !x y.
    u64_to_int y <> 0 ⇒
    ?z. u64_div x y = Return z /\ u64_to_int z = u64_to_int x / u64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u128_div_eq:
  !x y.
    u128_to_int y <> 0 ⇒
    ?z. u128_div x y = Return z /\ u128_to_int z = u128_to_int x / u128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem usize_div_eq:
  !x y.
    usize_to_int y <> 0 ⇒
    ?z. usize_div x y = Return z /\ usize_to_int z = usize_to_int x / usize_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i8_div_eq:
  !x y.
    i8_to_int y <> 0 ⇒
    i8_min <= i8_to_int x / i8_to_int y ⇒
    i8_to_int x / i8_to_int y <= i8_max ⇒
    ?z. i8_div x y = Return z /\ i8_to_int z = i8_to_int x / i8_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i16_div_eq:
  !x y.
    i16_to_int y <> 0 ⇒
    i16_min <= i16_to_int x / i16_to_int y ⇒
    i16_to_int x / i16_to_int y <= i16_max ⇒
    ?z. i16_div x y = Return z /\ i16_to_int z = i16_to_int x / i16_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i32_div_eq:
  !x y.
    i32_to_int y <> 0 ⇒
    i32_min <= i32_to_int x / i32_to_int y ⇒
    i32_to_int x / i32_to_int y <= i32_max ⇒
    ?z. i32_div x y = Return z /\ i32_to_int z = i32_to_int x / i32_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i64_div_eq:
  !x y.
    i64_to_int y <> 0 ⇒
    i64_min <= i64_to_int x / i64_to_int y ⇒
    i64_to_int x / i64_to_int y <= i64_max ⇒
    ?z. i64_div x y = Return z /\ i64_to_int z = i64_to_int x / i64_to_int y
Proof
  prove_arith_op_eq
QED

Theorem i128_div_eq:
  !x y.
    i128_to_int y <> 0 ⇒
    i128_min <= i128_to_int x / i128_to_int y ⇒
    i128_to_int x / i128_to_int y <= i128_max ⇒
    ?z. i128_div x y = Return z /\ i128_to_int z = i128_to_int x / i128_to_int y
Proof
  prove_arith_op_eq
QED

Theorem isize_div_eq:
  !x y.
    isize_to_int y <> 0 ⇒
    (i16_min <= isize_to_int x / isize_to_int y \/ isize_min <= isize_to_int x / isize_to_int y) ⇒
    (isize_to_int x / isize_to_int y <= i16_max \/ isize_to_int x / isize_to_int y <= isize_max) ⇒
    ?z. isize_div x y = Return z /\ isize_to_int z = isize_to_int x / isize_to_int y
Proof
  prove_arith_op_eq
QED

Theorem u8_rem_eq:
  !x y.
    u8_to_int y <> 0 ⇒
    ?z. u8_rem x y = Return z /\ u8_to_int z = int_rem (u8_to_int x) (u8_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem u16_rem_eq:
  !x y.
    u16_to_int y <> 0 ⇒
    ?z. u16_rem x y = Return z /\ u16_to_int z = int_rem (u16_to_int x) (u16_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem u32_rem_eq:
  !x y.
    u32_to_int y <> 0 ⇒
    ?z. u32_rem x y = Return z /\ u32_to_int z = int_rem (u32_to_int x) (u32_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem u64_rem_eq:
  !x y.
    u64_to_int y <> 0 ⇒
    ?z. u64_rem x y = Return z /\ u64_to_int z = int_rem (u64_to_int x) (u64_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem u128_rem_eq:
  !x y.
    u128_to_int y <> 0 ⇒
    ?z. u128_rem x y = Return z /\ u128_to_int z = int_rem (u128_to_int x) (u128_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem usize_rem_eq:
  !x y.
    usize_to_int y <> 0 ⇒
    ?z. usize_rem x y = Return z /\ usize_to_int z = int_rem (usize_to_int x) (usize_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem i8_rem_eq:
  !x y.
    i8_to_int y <> 0 ⇒
    i8_min <= int_rem (i8_to_int x) (i8_to_int y) ⇒
    int_rem (i8_to_int x) (i8_to_int y) <= i8_max ⇒
    ?z. i8_rem x y = Return z /\ i8_to_int z = int_rem (i8_to_int x) (i8_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem i16_rem_eq:
  !x y.
    i16_to_int y <> 0 ⇒
    i16_min <= int_rem (i16_to_int x) (i16_to_int y) ⇒
    int_rem (i16_to_int x) (i16_to_int y) <= i16_max ⇒
    ?z. i16_rem x y = Return z /\ i16_to_int z = int_rem (i16_to_int x) (i16_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem i32_rem_eq:
  !x y.
    i32_to_int y <> 0 ⇒
    i32_min <= int_rem (i32_to_int x) (i32_to_int y) ⇒
    int_rem (i32_to_int x) (i32_to_int y) <= i32_max ⇒
    ?z. i32_rem x y = Return z /\ i32_to_int z = int_rem (i32_to_int x) (i32_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem i64_rem_eq:
  !x y.
    i64_to_int y <> 0 ⇒
    i64_min <= int_rem (i64_to_int x) (i64_to_int y) ⇒
    int_rem (i64_to_int x) (i64_to_int y) <= i64_max ⇒
    ?z. i64_rem x y = Return z /\ i64_to_int z = int_rem (i64_to_int x) (i64_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem i128_rem_eq:
  !x y.
    i128_to_int y <> 0 ⇒
    i128_min <= int_rem (i128_to_int x) (i128_to_int y) ⇒
    int_rem (i128_to_int x) (i128_to_int y) <= i128_max ⇒
    ?z. i128_rem x y = Return z /\ i128_to_int z = int_rem (i128_to_int x) (i128_to_int y)
Proof
  prove_arith_op_eq
QED

Theorem isize_rem_eq:
  !x y.
    isize_to_int y <> 0 ⇒
    (i16_min <= int_rem (isize_to_int x) (isize_to_int y) \/
     isize_min <= int_rem (isize_to_int x) (isize_to_int y)) ⇒
    (int_rem (isize_to_int x) (isize_to_int y) <= i16_max \/
     int_rem (isize_to_int x) (isize_to_int y) <= isize_max) ⇒
    ?z. isize_rem x y = Return z /\ isize_to_int z = int_rem (isize_to_int x) (isize_to_int y)
Proof
  prove_arith_op_eq
QED

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


(* Equality theorems for the comparisons between integers - used by evalLib *)

val prove_scalar_eq_equiv_tac = metis_tac all_scalar_to_int_to_scalar_lemmas

Theorem isize_eq_equiv:
  ∀x y. (x = y) = (isize_to_int x = isize_to_int y)
Proof
  prove_scalar_eq_equiv_tac
QED

Theorem i8_eq_equiv:
  ∀x y. (x = y) = (i8_to_int x = i8_to_int y)
Proof
  prove_scalar_eq_equiv_tac
QED

Theorem i16_eq_equiv:
  ∀x y. (x = y) = (i16_to_int x = i16_to_int y)
Proof
  prove_scalar_eq_equiv_tac
QED

Theorem i32_eq_equiv:
  ∀x y. (x = y) = (i32_to_int x = i32_to_int y)
Proof
  prove_scalar_eq_equiv_tac
QED

Theorem i64_eq_equiv:
  ∀x y. (x = y) = (i64_to_int x = i64_to_int y)
Proof
  prove_scalar_eq_equiv_tac
QED

Theorem i128_eq_equiv:
  ∀x y. (x = y) = (i128_to_int x = i128_to_int y)
Proof
  prove_scalar_eq_equiv_tac
QED

Theorem usize_eq_equiv:
  ∀x y. (x = y) = (usize_to_int x = usize_to_int y)
Proof
  prove_scalar_eq_equiv_tac
QED

Theorem u8_eq_equiv:
  ∀x y. (x = y) = (u8_to_int x = u8_to_int y)
Proof
  prove_scalar_eq_equiv_tac
QED

Theorem u16_eq_equiv:
  ∀x y. (x = y) = (u16_to_int x = u16_to_int y)
Proof
  prove_scalar_eq_equiv_tac
QED

Theorem u32_eq_equiv:
  ∀x y. (x = y) = (u32_to_int x = u32_to_int y)
Proof
  prove_scalar_eq_equiv_tac
QED

Theorem u64_eq_equiv:
  ∀x y. (x = y) = (u64_to_int x = u64_to_int y)
Proof
  prove_scalar_eq_equiv_tac
QED

Theorem u128_eq_equiv:
  ∀x y. (x = y) = (u128_to_int x = u128_to_int y)
Proof
  prove_scalar_eq_equiv_tac
QED


val _ = evalLib.add_rewrite_thms [
  "isize_eq_equiv",
  "i8_eq_equiv",
  "i16_eq_equiv",
  "i32_eq_equiv",
  "i64_eq_equiv",
  "i128_eq_equiv",
  "usize_eq_equiv",
  "u8_eq_equiv",
  "u16_eq_equiv",
  "u32_eq_equiv",
  "u64_eq_equiv",
  "u128_eq_equiv"
]

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

val mk_vec_axiom = new_axiom ("mk_vec_axiom",
  “∀l. len l ≤ usize_max ⇒ vec_to_list (mk_vec l) = l”)

Theorem update_len:
  ∀ls i y. len (update ls i y) = len ls
Proof
  Induct_on ‘ls’ >> Cases_on ‘i’ >> rw [update_def, len_def]
QED

Theorem update_spec:
  ∀ls i y.
    len (update ls i y) = len ls ∧
    (0 <= i ⇒
     i < len ls ⇒
     index i (update ls i y) = y ∧
     ∀j. j < len ls ⇒ j ≠ i ⇒ index j (update ls i y) = index j ls)
Proof
  Induct_on ‘ls’ >> Cases_on ‘i = 0’ >> rw [update_def, len_def, index_def] >>
  try_tac (exfalso >> cooper_tac) >>
  try_tac (
    pop_last_assum (qspecl_assume [‘i' - 1’, ‘y’]) >> fs [] >>
    pop_assum sg_premise_tac >- cooper_tac >>
    pop_assum sg_premise_tac >- cooper_tac >>
    rw [])
  >> (
    pop_assum (qspec_assume ‘j - 1’) >>
    pop_assum sg_premise_tac >- cooper_tac >>
    pop_assum sg_premise_tac >- cooper_tac >>
    rw [])
QED

Theorem len_update:
  ∀ ls i y. len (update ls i y) = len ls
Proof
 fs [update_spec]
QED
val _ = BasicProvers.export_rewrites ["len_update"]

Theorem index_update_same:
  ∀ls i j y.
    0 <= i ⇒
    i < len ls ⇒
    j < len ls ⇒ j ≠ i ⇒ index j (update ls i y) = index j ls
Proof
  rpt strip_tac >>
  qspecl_assume [‘ls’, ‘i’, ‘y’] update_spec >>
  rw []
QED

Theorem index_update_diff:
  ∀ls i j y.
    0 <= i ⇒
    i < len ls ⇒
    index i (update ls i y) = y
Proof
  rpt strip_tac >>
  qspecl_assume [‘ls’, ‘i’, ‘y’] update_spec >>
  rw []
QED

Theorem vec_to_list_int_bounds:
  !v. 0 <= len (vec_to_list v) /\ len (vec_to_list v) <= usize_max
Proof
  gen_tac >>
  qspec_assume ‘v’ vec_to_list_num_bounds >>
  fs [len_eq_LENGTH] >>
  assume_tac usize_bounds >> fs [u16_max_def] >>
  cooper_tac
QED

val vec_len_def = Define ‘vec_len v = int_to_usize (len (vec_to_list v))’
Theorem vec_len_spec:
  ∀v.
    vec_len v = int_to_usize (len (vec_to_list v)) ∧
    0 ≤ len (vec_to_list v) ∧ len (vec_to_list v) ≤ usize_max
Proof
  gen_tac >> rw [vec_len_def] >>
  qspec_assume ‘v’ vec_to_list_int_bounds >>
  fs []
QED

Definition vec_new_def:
  vec_new = mk_vec []
End

Theorem vec_to_list_vec_new:
  vec_to_list vec_new = []
Proof
  fs [vec_new_def] >>
  sg_dep_rewrite_all_tac mk_vec_axiom >> fs [len_def] >>
  assume_tac usize_bounds >> fs [u16_max_def] >> int_tac
QED
val _ = BasicProvers.export_rewrites ["vec_to_list_vec_new"]

Theorem vec_len_vec_new:
  vec_len vec_new = int_to_usize 0
Proof
  fs [vec_len_def, vec_new_def] >>
  sg_dep_rewrite_all_tac usize_to_int_int_to_usize >> fs [len_def, u16_max_def] >>
  assume_tac usize_bounds >> fs [u16_max_def] >> int_tac
QED
val _ = BasicProvers.export_rewrites ["vec_len_vec_new"]

(* A custom unfolding theorem for evaluation - we compare to “u16_max” rather
   than “usize_max” on purpose. *)
Theorem mk_vec_unfold:
  ∀l. vec_to_list (mk_vec l) = if len l ≤ u16_max then l else vec_to_list (mk_vec l)
Proof
  rw [] >> Cases_on ‘len l ≤ u16_max’ >> fs [] >>
  assume_tac usize_bounds >>
  sg ‘len l ≤ usize_max’ >- int_tac >>
  metis_tac [mk_vec_axiom]
QED
val _ = evalLib.add_unfold_thm "mk_vec_unfold"

(* Helper *)
Definition vec_index_def:
  vec_index v i = index (usize_to_int i) (vec_to_list v)
End

(* Helper *)
Definition vec_update_def:
  vec_update v i x = mk_vec (update (vec_to_list v) (usize_to_int i) x)
End

Theorem vec_update_eq:
 ∀ v i x.
   let nv = vec_update v i x in
   len (vec_to_list nv) = len (vec_to_list v) ∧
   len (update (vec_to_list v) (usize_to_int i) x) = len (vec_to_list v) ∧
   (usize_to_int i < len (vec_to_list v) ⇒
      vec_index nv i = x ∧
      (∀j. usize_to_int j < usize_to_int (vec_len nv) ⇒
            usize_to_int j ≠ usize_to_int i ⇒
            vec_index nv j = vec_index v j))
Proof
  rpt strip_tac >> fs [vec_update_def] >>
  qspec_assume ‘update (vec_to_list v) (usize_to_int i) x’ mk_vec_axiom >>
  sg_dep_rewrite_all_tac update_len >> fs [] >>
  qspec_assume ‘v’ vec_len_spec >> gvs [] >>
  fs [vec_len_def, vec_index_def] >>
  qspec_assume ‘i’ usize_to_int_bounds >>
  sg_dep_rewrite_all_tac usize_to_int_int_to_usize >- cooper_tac >> fs [] >>
  rw []
  >- (irule index_update_diff >> cooper_tac) >>
  sg_dep_rewrite_all_tac index_update_same >- cooper_tac >> fs []
QED

Theorem vec_to_list_vec_update:
  ∀ v i x. vec_to_list (vec_update v i x) = update (vec_to_list v) (usize_to_int i) x
Proof
  rw [vec_update_def] >>
  qspec_assume ‘v’ vec_len_spec >>
  qspecl_assume [‘v’, ‘i’, ‘x’] vec_update_eq >> fs [] >>
  qspecl_assume [‘vec_to_list v’, ‘usize_to_int i’, ‘x’] update_len >>
  sg_dep_rewrite_all_tac mk_vec_axiom >- fs [] >>
  fs []
QED
val _ = export_rewrites ["vec_to_list_vec_update"]

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

Theorem vec_index_fwd_spec:
  ∀v i.
    usize_to_int i < usize_to_int (vec_len v) ⇒
    vec_index_fwd v i = Return (vec_index v i)
Proof
  rw [vec_index_fwd_def]
QED

Theorem vec_index_back_spec:
  ∀v i.
    usize_to_int i < usize_to_int (vec_len v) ⇒
    vec_index_back v i = Return ()
Proof
  rw [vec_index_back_def]
QED

Theorem vec_index_mut_fwd_spec:
  ∀v i.
    usize_to_int i < usize_to_int (vec_len v) ⇒
    vec_index_mut_fwd v i = Return (vec_index v i)
Proof
  rw [vec_index_mut_fwd_def]
QED

Theorem vec_index_mut_back_spec:
  ∀v i x.
    usize_to_int i < usize_to_int (vec_len v) ⇒
    vec_index_mut_back v i x = Return (vec_update v i x)
Proof
  rw [vec_index_mut_back_def]
QED

Definition vec_insert_back_def:
  vec_insert_back (v : 'a vec) (i : usize) (x : 'a) =
    if usize_to_int i < usize_to_int (vec_len v) then
      Return (vec_update v i x)
    else Fail Failure
End

Theorem vec_insert_back_spec:
  ∀v i x.
    usize_to_int i < usize_to_int (vec_len v) ⇒
    vec_insert_back v i x = Return (vec_update v i x)
Proof
  rw [vec_insert_back_def]
QED

Definition vec_push_back_def:
  vec_push_back (v : 'a vec) (x : 'a) : ('a vec) result =
    if usize_to_int (vec_len v) < usize_max then
      Return (mk_vec ((vec_to_list v) ++ [x]))
    else Fail Failure
End

Theorem vec_push_back_unfold:
  ∀ v x. vec_push_back (v : 'a vec) (x : 'a) : ('a vec) result =
    if usize_to_int (vec_len v) < u16_max ∨ usize_to_int (vec_len v) < usize_max then
      Return (mk_vec ((vec_to_list v) ++ [x]))
    else Fail Failure
Proof
  assume_tac usize_bounds >>
  rw [vec_push_back_def] >> fs [] >>
  int_tac
QED
val _ = evalLib.add_unfold_thm "vec_push_back_unfold"

Theorem vec_push_back_spec:
  ∀ v x.
    usize_to_int (vec_len v) < usize_max ⇒
    ∃ nv. vec_push_back v x = Return nv ∧
    vec_to_list nv = vec_to_list v ++ [x]
Proof
  rw [vec_push_back_def, vec_len_def] >>
  qspec_assume ‘v’ vec_len_spec >>
  sg_dep_rewrite_all_tac usize_to_int_int_to_usize >- int_tac >> fs [] >>
  sg_dep_rewrite_all_tac mk_vec_axiom
  >- (fs [len_append, len_def, vec_len_def] >> int_tac) >>
  fs []
QED

val _ = export_theory ()
