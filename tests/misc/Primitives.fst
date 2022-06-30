/// This file lists primitive and assumed functions and types
module Primitives
open FStar.Mul
open FStar.List.Tot

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(*** Utilities *)
val list_update (#a : Type0) (ls : list a) (i : nat{i < length ls}) (x : a) :
  ls':list a{
    length ls' = length ls /\
    index ls' i == x
  }
#push-options "--fuel 1"
let rec list_update #a ls i x =
  match ls with
  | x' :: ls -> if i = 0 then x :: ls else x' :: list_update ls (i-1) x
#pop-options

(*** Result *)
type result (a : Type0) : Type0 =
| Return : v:a -> result a
| Fail : result a

// Monadic bind and return.
// Re-definining those allows us to customize the result of the monadic notations
// like: `y <-- f x;`
let return (#a : Type0) (x:a) : result a = Return x
let bind (#a #b : Type0) (m : result a) (f : a -> result b) : result b =
    match m with
    | Return x -> f x
    | Fail -> Fail

// Monadic assert(...)
let massert (b:bool) : result unit = if b then Return () else Fail

// Unwrap a successful result by normalisation (used for globals).
let eval_global (#a : Type0) (x : result a{Return? (normalize_term x)}) : a = Return?.v x

(*** Misc *)
type char = FStar.Char.char
type string = string

let mem_replace_fwd (a : Type0) (x : a) (y : a) : a = x
let mem_replace_back (a : Type0) (x : a) (y : a) : a = y

(*** Scalars *)
/// Rk.: most of the following code was at least partially generated

let isize_min : int = -9223372036854775808
let isize_max : int = 9223372036854775807
let i8_min : int = -128
let i8_max : int = 127
let i16_min : int = -32768
let i16_max : int = 32767
let i32_min : int = -2147483648
let i32_max : int = 2147483647
let i64_min : int = -9223372036854775808
let i64_max : int = 9223372036854775807
let i128_min : int = -170141183460469231731687303715884105728
let i128_max : int = 170141183460469231731687303715884105727
let usize_min : int = 0
let usize_max : int = 4294967295 // being conservative here: [u32_max] instead of [u64_max]
let u8_min : int = 0
let u8_max : int = 255
let u16_min : int = 0
let u16_max : int = 65535
let u32_min : int = 0
let u32_max : int = 4294967295
let u64_min : int = 0
let u64_max : int = 18446744073709551615
let u128_min : int = 0
let u128_max : int = 340282366920938463463374607431768211455

type scalar_ty =
| Isize
| I8
| I16
| I32
| I64
| I128
| Usize
| U8
| U16
| U32
| U64
| U128

let scalar_min (ty : scalar_ty) : int =
  match ty with
  | Isize -> isize_min
  | I8 -> i8_min
  | I16 -> i16_min
  | I32 -> i32_min
  | I64 -> i64_min
  | I128 -> i128_min
  | Usize -> usize_min
  | U8 -> u8_min
  | U16 -> u16_min
  | U32 -> u32_min
  | U64 -> u64_min
  | U128 -> u128_min

let scalar_max (ty : scalar_ty) : int =
  match ty with
  | Isize -> isize_max
  | I8 -> i8_max
  | I16 -> i16_max
  | I32 -> i32_max
  | I64 -> i64_max
  | I128 -> i128_max
  | Usize -> usize_max
  | U8 -> u8_max
  | U16 -> u16_max
  | U32 -> u32_max
  | U64 -> u64_max
  | U128 -> u128_max

type scalar (ty : scalar_ty) : eqtype = x:int{scalar_min ty <= x && x <= scalar_max ty}

let mk_scalar (ty : scalar_ty) (x : int) : result (scalar ty) =
  if scalar_min ty <= x && scalar_max ty >= x then Return x else Fail

let scalar_neg (#ty : scalar_ty) (x : scalar ty) : result (scalar ty) = mk_scalar ty (-x)

let scalar_div (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  if y <> 0 then mk_scalar ty (x / y) else Fail

/// The remainder operation
let int_rem (x : int) (y : int{y <> 0}) : int =
  if x >= 0 then (x % y) else -(x % y)

(* Checking consistency with Rust *)
let _ = assert_norm(int_rem 1 2 = 1)
let _ = assert_norm(int_rem (-1) 2 = -1)
let _ = assert_norm(int_rem 1 (-2) = 1)
let _ = assert_norm(int_rem (-1) (-2) = -1)

let scalar_rem (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  if y <> 0 then mk_scalar ty (int_rem x y) else Fail

let scalar_add (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  mk_scalar ty (x + y)

let scalar_sub (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  mk_scalar ty (x - y)

let scalar_mul (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  mk_scalar ty (x * y)

(** Cast an integer from a [src_ty] to a [tgt_ty] *)
let scalar_cast (src_ty : scalar_ty) (tgt_ty : scalar_ty) (x : scalar src_ty) : result (scalar tgt_ty) =
  mk_scalar tgt_ty x

/// The scalar types
type isize : eqtype = scalar Isize
type i8 : eqtype = scalar I8
type i16 : eqtype = scalar I16
type i32 : eqtype = scalar I32
type i64 : eqtype = scalar I64
type i128 : eqtype = scalar I128
type usize : eqtype = scalar Usize
type u8 : eqtype = scalar U8
type u16 : eqtype = scalar U16
type u32 : eqtype = scalar U32
type u64 : eqtype = scalar U64
type u128 : eqtype = scalar U128

/// Negation
let isize_neg = scalar_neg #Isize
let i8_neg = scalar_neg #I8
let i16_neg = scalar_neg #I16
let i32_neg = scalar_neg #I32
let i64_neg = scalar_neg #I64
let i128_neg = scalar_neg #I128

/// Division
let isize_div = scalar_div #Isize
let i8_div = scalar_div #I8
let i16_div = scalar_div #I16
let i32_div = scalar_div #I32
let i64_div = scalar_div #I64
let i128_div = scalar_div #I128
let usize_div = scalar_div #Usize
let u8_div = scalar_div #U8
let u16_div = scalar_div #U16
let u32_div = scalar_div #U32
let u64_div = scalar_div #U64
let u128_div = scalar_div #U128

/// Remainder
let isize_rem = scalar_rem #Isize
let i8_rem = scalar_rem #I8
let i16_rem = scalar_rem #I16
let i32_rem = scalar_rem #I32
let i64_rem = scalar_rem #I64
let i128_rem = scalar_rem #I128
let usize_rem = scalar_rem #Usize
let u8_rem = scalar_rem #U8
let u16_rem = scalar_rem #U16
let u32_rem = scalar_rem #U32
let u64_rem = scalar_rem #U64
let u128_rem = scalar_rem #U128

/// Addition
let isize_add = scalar_add #Isize
let i8_add = scalar_add #I8
let i16_add = scalar_add #I16
let i32_add = scalar_add #I32
let i64_add = scalar_add #I64
let i128_add = scalar_add #I128
let usize_add = scalar_add #Usize
let u8_add = scalar_add #U8
let u16_add = scalar_add #U16
let u32_add = scalar_add #U32
let u64_add = scalar_add #U64
let u128_add = scalar_add #U128

/// Substraction
let isize_sub = scalar_sub #Isize
let i8_sub = scalar_sub #I8
let i16_sub = scalar_sub #I16
let i32_sub = scalar_sub #I32
let i64_sub = scalar_sub #I64
let i128_sub = scalar_sub #I128
let usize_sub = scalar_sub #Usize
let u8_sub = scalar_sub #U8
let u16_sub = scalar_sub #U16
let u32_sub = scalar_sub #U32
let u64_sub = scalar_sub #U64
let u128_sub = scalar_sub #U128

/// Multiplication
let isize_mul = scalar_mul #Isize
let i8_mul = scalar_mul #I8
let i16_mul = scalar_mul #I16
let i32_mul = scalar_mul #I32
let i64_mul = scalar_mul #I64
let i128_mul = scalar_mul #I128
let usize_mul = scalar_mul #Usize
let u8_mul = scalar_mul #U8
let u16_mul = scalar_mul #U16
let u32_mul = scalar_mul #U32
let u64_mul = scalar_mul #U64
let u128_mul = scalar_mul #U128

(*** Vector *)
type vec (a : Type0) = v:list a{length v <= usize_max}

let vec_new (a  : Type0) : vec a = assert_norm(length #a [] == 0); []
let vec_len (a : Type0) (v : vec a) : usize = length v

// The **forward** function shouldn't be used
let vec_push_fwd (a  : Type0) (v : vec a) (x : a) : unit = ()
let vec_push_back (a  : Type0) (v : vec a) (x : a) :
  Pure (result (vec a))
  (requires True)
  (ensures (fun res ->
    match res with
    | Fail -> True
    | Return v' -> length v' = length v + 1)) =
  if length v < usize_max then begin
    (**) assert_norm(length [x] == 1);
    (**) append_length v [x];
    (**) assert(length (append v [x]) = length v + 1);
    Return (append v [x])
    end
  else Fail

// The **forward** function shouldn't be used
let vec_insert_fwd (a : Type0) (v : vec a) (i : usize) (x : a) : result unit =
  if i < length v then Return () else Fail
let vec_insert_back (a : Type0) (v : vec a) (i : usize) (x : a) : result (vec a) =
  if i < length v then Return (list_update v i x) else Fail

// The **backward** function shouldn't be used
let vec_index_fwd (a : Type0) (v : vec a) (i : usize) : result a =
  if i < length v then Return (index v i) else Fail
let vec_index_back (a : Type0) (v : vec a) (i : usize) (x : a) : result unit =
  if i < length v then Return () else Fail

let vec_index_mut_fwd (a : Type0) (v : vec a) (i : usize) : result a =
  if i < length v then Return (index v i) else Fail
let vec_index_mut_back (a : Type0) (v : vec a) (i : usize) (nx : a) : result (vec a) =
  if i < length v then Return (list_update v i nx) else Fail

