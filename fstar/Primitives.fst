/// This file lists primitive and assumed functions and types
module Primitives
open FStar.Mul

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(*** Result *)
type result (a : Type0) : Type0 =
| Return : a -> result a
| Fail : result a

(*** Misc *)
type char = FStar.Char.char

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

/// The scalar types
type isize = scalar Isize
type i8 = scalar I8
type i16 = scalar I16
type i32 = scalar I32
type i64 = scalar I64
type i128 = scalar I128
type usize = scalar Usize
type u8 = scalar U8
type u16 = scalar U16
type u32 = scalar U32
type u64 = scalar U64
type u128 = scalar U128

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
