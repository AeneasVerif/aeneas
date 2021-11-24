open Types
open Values

(** The minimum/maximum values an integer type can have depending on its type *)

let i8_min = Z.of_string "-128"

let i8_max = Z.of_string "127"

let i16_min = Z.of_string "-32768"

let i16_max = Z.of_string "32767"

let i32_min = Z.of_string "-2147483648"

let i32_max = Z.of_string "2147483647"

let i64_min = Z.of_string "-9223372036854775808"

let i64_max = Z.of_string "9223372036854775807"

let i128_min = Z.of_string "-170141183460469231731687303715884105728"

let i128_max = Z.of_string "170141183460469231731687303715884105727"

let u8_min = Z.of_string "0"

let u8_max = Z.of_string "255"

let u16_min = Z.of_string "0"

let u16_max = Z.of_string "65535"

let u32_min = Z.of_string "0"

let u32_max = Z.of_string "4294967295"

let u64_min = Z.of_string "0"

let u64_max = Z.of_string "18446744073709551615"

let u128_min = Z.of_string "0"

let u128_max = Z.of_string "340282366920938463463374607431768211455"

(** Being a bit conservative about isize/usize: depending on the system,
    the values are encoded as 32-bit values or 64-bit values - we may
    want to take that into account in the future *)

let isize_min = i32_min

let isize_max = i32_max

let usize_min = u32_min

let usize_max = u32_max

(** Return the integer value in a scalar value *)
let scalar_value_get_value (v : scalar_value) : big_int =
  match v with
  | Isize i -> i
  | I8 i -> i
  | I16 i -> i
  | I32 i -> i
  | I64 i -> i
  | I128 i -> i
  | Usize i -> i
  | U8 i -> i
  | U16 i -> i
  | U32 i -> i
  | U64 i -> i
  | U128 i -> i

(** Retrieve the [integer_type] of a scalar value *)
let scalar_value_get_integer_type (sv : scalar_value) : integer_type =
  match sv with
  | Isize _ -> Types.Isize
  | I8 _ -> Types.I8
  | I16 _ -> Types.I16
  | I32 _ -> Types.I32
  | I64 _ -> Types.I64
  | I128 _ -> Types.I128
  | Usize _ -> Types.Usize
  | U8 _ -> Types.U8
  | U16 _ -> Types.U16
  | U32 _ -> Types.U32
  | U64 _ -> Types.U64
  | U128 _ -> Types.U128

(** Check that an integer value is in range *)
let check_int_in_range (int_ty : integer_type) (i : big_int) : bool =
  match int_ty with
  | Isize -> Z.leq isize_min i && Z.leq i isize_max
  | I8 -> Z.leq i8_min i && Z.leq i i8_max
  | I16 -> Z.leq i16_min i && Z.leq i i16_max
  | I32 -> Z.leq i32_min i && Z.leq i i32_max
  | I64 -> Z.leq i64_min i && Z.leq i i64_max
  | I128 -> Z.leq i128_min i && Z.leq i i128_max
  | Usize -> Z.leq usize_min i && Z.leq i usize_max
  | U8 -> Z.leq u8_min i && Z.leq i u8_max
  | U16 -> Z.leq u16_min i && Z.leq i u16_max
  | U32 -> Z.leq u32_min i && Z.leq i u32_max
  | U64 -> Z.leq u64_min i && Z.leq i u64_max
  | U128 -> Z.leq u128_min i && Z.leq i u128_max

(** Check that a scalar value is correct (the integer value it contains is in range) *)
let check_scalar_value_in_range (v : scalar_value) : bool =
  let i = scalar_value_get_value v in
  let int_ty = scalar_value_get_integer_type v in
  check_int_in_range int_ty i

(** Make a scalar value, while checking the value is in range *)
let mk_scalar (int_ty : integer_type) (i : big_int) :
    (scalar_value, unit) result =
  if check_int_in_range int_ty i then
    match int_ty with
    | Types.Isize -> Ok (Isize i)
    | Types.I8 -> Ok (I8 i)
    | Types.I16 -> Ok (I16 i)
    | Types.I32 -> Ok (I32 i)
    | Types.I64 -> Ok (I64 i)
    | Types.I128 -> Ok (I128 i)
    | Types.Usize -> Ok (Usize i)
    | Types.U8 -> Ok (U8 i)
    | Types.U16 -> Ok (U16 i)
    | Types.U32 -> Ok (U32 i)
    | Types.U64 -> Ok (U64 i)
    | Types.U128 -> Ok (U128 i)
  else Error ()
