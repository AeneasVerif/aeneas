/// This file lists primitive and assumed functions and types, referenced by the
/// extraction mechanism.
module Assumed
open FStar.Mul

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

/// Result type
type result (a : Type0) : Type0 =
| Return : a -> result a
| Fail : result a

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
let usize_max : int = 18446744073709551615
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

type scalar (ty : scalar_ty) : Type0 = x:int{scalar_min ty <= x && x <= scalar_max ty}

let mk_scalar (ty : scalar_ty) (x : int) : result (scalar ty) =
  if scalar_min ty <= x && scalar_max ty >= x then Return x else Fail

let g_neg (#ty : scalar_ty) (x : scalar ty) : result (scalar ty) = mk_scalar ty (-x)

// TODO: remove
(*let g_lt (x : int) (y : int) = x <= y *)

let g_div (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  if y <> 0 then mk_scalar ty (x / y) else Fail

(* TODO:
let g_rem (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  if y <> 0 then mk_scalar ty (x / y) else Fail
*)

let g_add (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  mk_scalar ty (x + y)

let g_sub (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  mk_scalar ty (x - y)

let g_mul (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  mk_scalar ty (x * y)
