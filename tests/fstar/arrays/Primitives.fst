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
type error : Type0 =
| Failure
| OutOfFuel

type result (a : Type0) : Type0 =
| Ok : v:a -> result a
| Fail : e:error -> result a

// Monadic return operator
unfold let return (#a : Type0) (x : a) : result a = Ok x

// Monadic bind operator.
// Allows to use the notation:
// ```
// let* x = y in
// ...
// ```
unfold let (let*) (#a #b : Type0) (m: result a)
  (f: (x:a) -> Pure (result b) (requires (m == Ok x)) (ensures fun _ -> True)) :
  result b =
  match m with
  | Ok x -> f x
  | Fail e   -> Fail e

// Monadic assert(...)
let massert (b:bool) : result unit = if b then Ok () else Fail Failure

// Normalize and unwrap a successful result (used for globals).
let eval_global (#a : Type0) (x : result a{Ok? (normalize_term x)}) : a = Ok?.v x

(*** Misc *)
type char = FStar.Char.char
type string = string

let is_zero (n: nat) : bool = n = 0
let decrease (n: nat{n > 0}) : nat = n - 1

let core_mem_replace (#a : Type0) (x : a) (y : a) : a & a = (x, x)

// We don't really use raw pointers for now
type mut_raw_ptr (t : Type0) = { v : t }
type const_raw_ptr (t : Type0) = { v : t }

(*** Scalars *)
/// Rem.: most of the following code was partially generated

assume val size_numbits : pos

// TODO: we could use FStar.Int.int_t and FStar.UInt.int_t

let isize_min : int = -9223372036854775808 // TODO: should be opaque
let isize_max : int = 9223372036854775807 // TODO: should be opaque
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
let usize_max : int = 4294967295 // TODO: should be opaque
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

let is_unsigned = function
  | Isize | I8 | I16 | I32 | I64 | I128 -> false
  | Usize | U8 | U16 | U32 | U64 | U128 -> true

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
  if scalar_min ty <= x && scalar_max ty >= x then Ok x else Fail Failure

let scalar_neg (#ty : scalar_ty) (x : scalar ty) : result (scalar ty) = mk_scalar ty (-x)

let scalar_div (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  if y <> 0 then mk_scalar ty (x / y) else Fail Failure

/// The remainder operation
let int_rem (x : int) (y : int{y <> 0}) : int =
  if x >= 0 then (x % y) else -(x % y)

(* Checking consistency with Rust *)
let _ = assert_norm(int_rem 1 2 = 1)
let _ = assert_norm(int_rem (-1) 2 = -1)
let _ = assert_norm(int_rem 1 (-2) = 1)
let _ = assert_norm(int_rem (-1) (-2) = -1)

let scalar_rem (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  if y <> 0 then mk_scalar ty (int_rem x y) else Fail Failure

let scalar_add (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  mk_scalar ty (x + y)

let scalar_sub (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  mk_scalar ty (x - y)

let scalar_mul (#ty : scalar_ty) (x : scalar ty) (y : scalar ty) : result (scalar ty) =
  mk_scalar ty (x * y)

let scalar_xor (#ty : scalar_ty)
    (x : scalar ty) (y : scalar ty) : scalar ty =
  match ty with
  | U8 -> FStar.UInt.logxor #8 x y
  | U16 -> FStar.UInt.logxor #16 x y
  | U32 -> FStar.UInt.logxor #32 x y
  | U64 -> FStar.UInt.logxor #64 x y
  | U128 -> FStar.UInt.logxor #128 x y
  | Usize -> admit() // TODO
  | I8 ->
    // Encoding issues...
    normalize_spec (FStar.Int.int_t 8);
    normalize_spec (scalar I8);
    FStar.Int.logxor #8 x y
  | I16 ->
    // Encoding issues...
    normalize_spec (FStar.Int.int_t 16);
    normalize_spec (scalar I16);
    FStar.Int.logxor #16 x y
  | I32 -> FStar.Int.logxor #32 x y
  | I64 -> FStar.Int.logxor #64 x y
  | I128 ->
    // Encoding issues...
    normalize_spec (FStar.Int.int_t 128);
    normalize_spec (scalar I128);
    FStar.Int.logxor #128 x y
  | Isize -> admit() // TODO

let scalar_or (#ty : scalar_ty)
    (x : scalar ty) (y : scalar ty) : scalar ty =
  match ty with
  | U8 -> FStar.UInt.logor #8 x y
  | U16 -> FStar.UInt.logor #16 x y
  | U32 -> FStar.UInt.logor #32 x y
  | U64 -> FStar.UInt.logor #64 x y
  | U128 -> FStar.UInt.logor #128 x y
  | Usize -> admit() // TODO
  | I8 ->
    // Encoding issues...
    normalize_spec (FStar.Int.int_t 8);
    normalize_spec (scalar I8);
    FStar.Int.logor #8 x y
  | I16 ->
    // Encoding issues...
    normalize_spec (FStar.Int.int_t 16);
    normalize_spec (scalar I16);
    FStar.Int.logor #16 x y
  | I32 -> FStar.Int.logor #32 x y
  | I64 -> FStar.Int.logor #64 x y
  | I128 ->
    // Encoding issues...
    normalize_spec (FStar.Int.int_t 128);
    normalize_spec (scalar I128);
    FStar.Int.logor #128 x y
  | Isize -> admit() // TODO

let scalar_and (#ty : scalar_ty)
    (x : scalar ty) (y : scalar ty) : scalar ty =
  match ty with
  | U8 -> FStar.UInt.logand #8 x y
  | U16 -> FStar.UInt.logand #16 x y
  | U32 -> FStar.UInt.logand #32 x y
  | U64 -> FStar.UInt.logand #64 x y
  | U128 -> FStar.UInt.logand #128 x y
  | Usize -> admit() // TODO
  | I8 ->
    // Encoding issues...
    normalize_spec (FStar.Int.int_t 8);
    normalize_spec (scalar I8);
    FStar.Int.logand #8 x y
  | I16 ->
    // Encoding issues...
    normalize_spec (FStar.Int.int_t 16);
    normalize_spec (scalar I16);
    FStar.Int.logand #16 x y
  | I32 -> FStar.Int.logand #32 x y
  | I64 -> FStar.Int.logand #64 x y
  | I128 ->
    // Encoding issues...
    normalize_spec (FStar.Int.int_t 128);
    normalize_spec (scalar I128);
    FStar.Int.logand #128 x y
  | Isize -> admit() // TODO

// Shift left
let scalar_shl (#ty0 #ty1 : scalar_ty)
    (x : scalar ty0) (y : scalar ty1) : result (scalar ty0) =
  admit()

// Shift right
let scalar_shr (#ty0 #ty1 : scalar_ty)
    (x : scalar ty0) (y : scalar ty1) : result (scalar ty0) =
  admit()

let scalar_not #ty (x : scalar ty) : scalar ty = admit()

(** Cast an integer from a [src_ty] to a [tgt_ty] *)
// TODO: check the semantics of casts in Rust
let scalar_cast (src_ty : scalar_ty) (tgt_ty : scalar_ty) (x : scalar src_ty) : result (scalar tgt_ty) =
  mk_scalar tgt_ty x

// This can't fail, but for now we make all casts faillible (easier for the translation)
let scalar_cast_bool (tgt_ty : scalar_ty) (x : bool) : result (scalar tgt_ty) =
  mk_scalar tgt_ty (if x then 1 else 0)

/// The scalar types
type isize : eqtype = scalar Isize
type i8    : eqtype = scalar I8
type i16   : eqtype = scalar I16
type i32   : eqtype = scalar I32
type i64   : eqtype = scalar I64
type i128  : eqtype = scalar I128
type usize : eqtype = scalar Usize
type u8    : eqtype = scalar U8
type u16   : eqtype = scalar U16
type u32   : eqtype = scalar U32
type u64   : eqtype = scalar U64
type u128  : eqtype = scalar U128


let core_num_Isize_MIN : isize = isize_min
let core_num_Isize_MAX : isize = isize_max
let core_num_I8_MIN    : i8 = i8_min
let core_num_I8_MAX    : i8 = i8_max
let core_num_I16_MIN   : i16 = i16_min
let core_num_I16_MAX   : i16 = i16_max
let core_num_I32_MIN   : i32 = i32_min
let core_num_I32_MAX   : i32 = i32_max
let core_num_I64_MIN   : i64 = i64_min
let core_num_I64_MAX   : i64 = i64_max
let core_num_I128_MIN  : i128 = i128_min
let core_num_I128_MAX  : i128 = i128_max

let core_num_Usize_MIN : usize = usize_min
let core_num_Usize_MAX : usize = usize_max
let core_num_U8_MIN    : u8 = u8_min
let core_num_U8_MAX    : u8 = u8_max
let core_num_U16_MIN   : u16 = u16_min
let core_num_U16_MAX   : u16 = u16_max
let core_num_U32_MIN   : u32 = u32_min
let core_num_U32_MAX   : u32 = u32_max
let core_num_U64_MIN   : u64 = u64_min
let core_num_U64_MAX   : u64 = u64_max
let core_num_U128_MIN  : u128 = u128_min
let core_num_U128_MAX  : u128 = u128_max

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

/// Subtraction
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

/// Xor
let u8_xor = scalar_xor #U8
let u16_xor = scalar_xor #U16
let u32_xor = scalar_xor #U32
let u64_xor = scalar_xor #U64
let u128_xor = scalar_xor #U128
let usize_xor = scalar_xor #Usize
let i8_xor = scalar_xor #I8
let i16_xor = scalar_xor #I16
let i32_xor = scalar_xor #I32
let i64_xor = scalar_xor #I64
let i128_xor = scalar_xor #I128
let isize_xor = scalar_xor #Isize

/// Or
let u8_or = scalar_or #U8
let u16_or = scalar_or #U16
let u32_or = scalar_or #U32
let u64_or = scalar_or #U64
let u128_or = scalar_or #U128
let usize_or = scalar_or #Usize
let i8_or = scalar_or #I8
let i16_or = scalar_or #I16
let i32_or = scalar_or #I32
let i64_or = scalar_or #I64
let i128_or = scalar_or #I128
let isize_or = scalar_or #Isize

/// And
let u8_and = scalar_and #U8
let u16_and = scalar_and #U16
let u32_and = scalar_and #U32
let u64_and = scalar_and #U64
let u128_and = scalar_and #U128
let usize_and = scalar_and #Usize
let i8_and = scalar_and #I8
let i16_and = scalar_and #I16
let i32_and = scalar_and #I32
let i64_and = scalar_and #I64
let i128_and = scalar_and #I128
let isize_and = scalar_and #Isize

/// Shift left
let u8_shl #ty = scalar_shl #U8 #ty
let u16_shl #ty = scalar_shl #U16 #ty
let u32_shl #ty = scalar_shl #U32 #ty
let u64_shl #ty = scalar_shl #U64 #ty
let u128_shl #ty = scalar_shl #U128 #ty
let usize_shl #ty = scalar_shl #Usize #ty
let i8_shl #ty = scalar_shl #I8 #ty
let i16_shl #ty = scalar_shl #I16 #ty
let i32_shl #ty = scalar_shl #I32 #ty
let i64_shl #ty = scalar_shl #I64 #ty
let i128_shl #ty = scalar_shl #I128 #ty
let isize_shl #ty = scalar_shl #Isize #ty

/// Shift right
let u8_shr #ty = scalar_shr #U8 #ty
let u16_shr #ty = scalar_shr #U16 #ty
let u32_shr #ty = scalar_shr #U32 #ty
let u64_shr #ty = scalar_shr #U64 #ty
let u128_shr #ty = scalar_shr #U128 #ty
let usize_shr #ty = scalar_shr #Usize #ty
let i8_shr #ty = scalar_shr #I8 #ty
let i16_shr #ty = scalar_shr #I16 #ty
let i32_shr #ty = scalar_shr #I32 #ty
let i64_shr #ty = scalar_shr #I64 #ty
let i128_shr #ty = scalar_shr #I128 #ty
let isize_shr #ty = scalar_shr #Isize #ty

/// Not
let u8_not = scalar_not #U8
let u16_not = scalar_not #U16
let u32_not = scalar_not #U32
let u64_not = scalar_not #U64
let u128_not = scalar_not #U128
let usize_not = scalar_not #Usize
let i8_not = scalar_not #I8
let i16_not = scalar_not #I16
let i32_not = scalar_not #I32
let i64_not = scalar_not #I64
let i128_not = scalar_not #I128
let isize_not = scalar_not #Isize

(*** core *)

/// Trait declaration: [core::clone::Clone]
noeq type core_clone_Clone (self : Type0) = {
  clone : self → result self;
  clone_from : self -> self -> result self;
}

let core_clone_impls_CloneBool_clone (b : bool) : bool = b

let core_clone_CloneBool : core_clone_Clone bool = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

let core_clone_impls_CloneUsize_clone (x : usize) : usize = x
let core_clone_impls_CloneU8_clone (x : u8) : u8 = x
let core_clone_impls_CloneU16_clone (x : u16) : u16 = x
let core_clone_impls_CloneU32_clone (x : u32) : u32 = x
let core_clone_impls_CloneU64_clone (x : u64) : u64 = x
let core_clone_impls_CloneU128_clone (x : u128) : u128 = x

let core_clone_impls_CloneIsize_clone (x : isize) : isize = x
let core_clone_impls_CloneI8_clone (x : i8) : i8 = x
let core_clone_impls_CloneI16_clone (x : i16) : i16 = x
let core_clone_impls_CloneI32_clone (x : i32) : i32 = x
let core_clone_impls_CloneI64_clone (x : i64) : i64 = x
let core_clone_impls_CloneI128_clone (x : i128) : i128 = x

let core_clone_CloneUsize : core_clone_Clone usize = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

let core_clone_CloneU8 : core_clone_Clone u8 = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

let core_clone_CloneU16 : core_clone_Clone u16 = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

let core_clone_CloneU32 : core_clone_Clone u32 = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

let core_clone_CloneU64 : core_clone_Clone u64 = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

let core_clone_CloneU128 : core_clone_Clone u128 = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

let core_clone_CloneIsize : core_clone_Clone isize = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

let core_clone_CloneI8 : core_clone_Clone i8 = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

let core_clone_CloneI16 : core_clone_Clone i16 = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

let core_clone_CloneI32 : core_clone_Clone i32 = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

let core_clone_CloneI64 : core_clone_Clone i64 = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

let core_clone_CloneI128 : core_clone_Clone i128 = {
  clone = (fun b -> Ok b);
  clone_from = (fun _ x -> Ok x);
}

noeq type core_marker_Copy (self : Type0) = {
  cloneInst : core_clone_Clone self;
}

let core_marker_CopyU8 : core_marker_Copy u8 = {
  cloneInst = core_clone_CloneU8;
}

let core_marker_CopyU16 : core_marker_Copy u16 = {
  cloneInst = core_clone_CloneU16;
}

let core_marker_CopyU32 : core_marker_Copy u32 = {
  cloneInst = core_clone_CloneU32;
}

let core_marker_CopyU64 : core_marker_Copy u64 = {
  cloneInst = core_clone_CloneU64;
}

let core_marker_CopyU128 : core_marker_Copy u128 = {
  cloneInst = core_clone_CloneU128;
}

let core_marker_CopyUsize : core_marker_Copy usize = {
  cloneInst = core_clone_CloneUsize;
}

let core_marker_CopyI8 : core_marker_Copy i8 = {
  cloneInst = core_clone_CloneI8;
}

let core_marker_CopyI16 : core_marker_Copy i16 = {
  cloneInst = core_clone_CloneI16;
}

let core_marker_CopyI32 : core_marker_Copy i32 = {
  cloneInst = core_clone_CloneI32;
}

let core_marker_CopyI64 : core_marker_Copy i64 = {
  cloneInst = core_clone_CloneI64;
}

let core_marker_CopyI128 : core_marker_Copy i128 = {
  cloneInst = core_clone_CloneI128;
}

let core_marker_CopyIsize : core_marker_Copy isize = {
  cloneInst = core_clone_CloneIsize;
}

(** [core::option::{core::option::Option<T>}::unwrap] *)
let core_option_Option_unwrap (#t : Type0) (x : option t) : result t =
  match x with
  | None -> Fail Failure
  | Some x -> Ok x

(*** core::ops *)

// Trait declaration: [core::ops::index::Index]
noeq type core_ops_index_Index (self idx output : Type0) = {
  index : self → idx → result output
}

// Trait declaration: [core::ops::index::IndexMut]
noeq type core_ops_index_IndexMut (self idx output : Type0) = {
  indexInst : core_ops_index_Index self idx output;
  index_mut : self → idx → result (output & (output → self));
}

// Trait declaration [core::ops::deref::Deref]
noeq type core_ops_deref_Deref (self target : Type0) = {
  deref : self → result target;
}

// Trait declaration [core::ops::deref::DerefMut]
noeq type core_ops_deref_DerefMut (self target : Type0) = {
  derefInst : core_ops_deref_Deref self target;
  deref_mut : self → result (target & (target → self));
}

type core_ops_range_Range (a : Type0) = {
  start : a;
  end_ : a;
}

(*** [alloc] *)

let alloc_boxed_Box_deref (#t : Type0) (x : t) : t = x
let alloc_boxed_Box_deref_mut (#t : Type0) (x : t) : (t & (t -> t)) =
  (x, (fun x -> x))

// Trait instance
let alloc_boxed_Box_coreopsDerefInst (self : Type0) : core_ops_deref_Deref self self = {
  deref = (fun x -> Ok (alloc_boxed_Box_deref #self x));
}

// Trait instance
let alloc_boxed_Box_coreopsDerefMutInst (self : Type0) : core_ops_deref_DerefMut self self = {
  derefInst = alloc_boxed_Box_coreopsDerefInst self;
  deref_mut = (fun x -> Ok (alloc_boxed_Box_deref_mut #self x));
}

(*** Array *)
type array (a : Type0) (n : usize) = s:list a{length s = n}

// We tried putting the normalize_term condition as a refinement on the list
// but it didn't work. It works with the requires clause.
let mk_array (#a : Type0) (n : usize)
  (l : list a) :
  Pure (array a n)
  (requires (normalize_term(FStar.List.Tot.length l) = n))
  (ensures (fun _ -> True)) =
  normalize_term_spec (FStar.List.Tot.length l);
  l

let array_index_usize (#a : Type0) (#n : usize) (x : array a n) (i : usize) : result a =
  if i < length x then Ok (index x i)
  else Fail Failure

let array_update_usize (#a : Type0) (#n : usize) (x : array a n) (i : usize) (nx : a) :
  result (array a n) =
  if i < length x then Ok (list_update x i nx)
  else Fail Failure

let array_update (#a : Type0) (#n : usize) (x : array a n) (i : usize) (nx : a) :
  array a n =
  if i < length x then list_update x i nx
  else x

let array_index_mut_usize (#a : Type0) (#n : usize) (x : array a n) (i : usize) :
  result (a & (a -> array a n)) =
  match array_index_usize x i with
  | Fail e -> Fail e
  | Ok v ->
    Ok (v, array_update x i)

(*** Slice *)
type slice (a : Type0) = s:list a{length s <= usize_max}

let slice_len (#a : Type0) (s : slice a) : usize = length s

let slice_index_usize (#a : Type0) (x : slice a) (i : usize) : result a =
  if i < length x then Ok (index x i)
  else Fail Failure

let slice_update_usize (#a : Type0) (x : slice a) (i : usize) (nx : a) : result (slice a) =
  if i < length x then Ok (list_update x i nx)
  else Fail Failure

let slice_update (#a : Type0) (x : slice a) (i : usize) (nx : a) : slice a =
  if i < length x then list_update x i nx
  else x

let slice_index_mut_usize (#a : Type0) (s : slice a) (i : usize) :
  result (a & (a -> slice a)) =
  match slice_index_usize s i with
  | Fail e -> Fail e
  | Ok x ->
    Ok (x, slice_update s i)

(*** Subslices *)

let array_to_slice (#a : Type0) (#n : usize) (x : array a n) : slice a = x
let array_from_slice (#a : Type0) (#n : usize) (x : array a n) (s : slice a) : array a n =
  if length s = n then s
  else (* Unreachable case *) x

let array_to_slice_mut (#a : Type0) (#n : usize) (x : array a n) :
  slice a & (slice a -> array a n) =
  (x, array_from_slice x)

// TODO: finish the definitions below (there lacks [List.drop] and [List.take] in the standard library *)
let array_subslice (#a : Type0) (#n : usize) (x : array a n) (r : core_ops_range_Range usize) : result (slice a) =
  admit()

let array_update_subslice (#a : Type0) (#n : usize) (x : array a n) (r : core_ops_range_Range usize) (ns : slice a) : result (array a n) =
  admit()

let array_repeat (#a : Type0) (n : usize) (x : a) : array a n =
  admit()

let slice_subslice (#a : Type0) (x : slice a) (r : core_ops_range_Range usize) : result (slice a) =
  admit()

let slice_update_subslice (#a : Type0) (x : slice a) (r : core_ops_range_Range usize) (ns : slice a) : result (slice a) =
  admit()

(*** Vector *)
type alloc_vec_Vec (a : Type0) = v:list a{length v <= usize_max}

let alloc_vec_Vec_new (a  : Type0) : alloc_vec_Vec a = assert_norm(length #a [] == 0); []
let alloc_vec_Vec_len (#a : Type0) (v : alloc_vec_Vec a) : usize = length v


let alloc_vec_Vec_index_usize (#a : Type0) (v : alloc_vec_Vec a) (i : usize) : result a =
  if i < length v then Ok (index v i) else Fail Failure

let alloc_vec_Vec_update_usize (#a : Type0) (v : alloc_vec_Vec a) (i : usize) (x : a) : result (alloc_vec_Vec a) =
  if i < length v then Ok (list_update v i x) else Fail Failure

// Helper
let alloc_vec_Vec_update (#a : Type0) (v : alloc_vec_Vec a) (i : usize) (x : a) : alloc_vec_Vec a =
  if i < length v then list_update v i x else v

let alloc_vec_Vec_index_mut_usize (#a : Type0) (v: alloc_vec_Vec a) (i: usize) :
  result (a & (a → alloc_vec_Vec a)) =
  match alloc_vec_Vec_index_usize v i with
  | Ok x ->
    Ok (x, alloc_vec_Vec_update v i)
  | Fail e -> Fail e

let alloc_vec_Vec_push (#a  : Type0) (v : alloc_vec_Vec a) (x : a) :
  Pure (result (alloc_vec_Vec a))
  (requires True)
  (ensures (fun res ->
    match res with
    | Fail e -> e == Failure
    | Ok v' -> length v' = length v + 1)) =
  if length v < usize_max then begin
    (**) assert_norm(length [x] == 1);
    (**) append_length v [x];
    (**) assert(length (append v [x]) = length v + 1);
    Ok (append v [x])
    end
  else Fail Failure

let alloc_vec_Vec_insert (#a : Type0) (v : alloc_vec_Vec a) (i : usize) (x : a) : result (alloc_vec_Vec a) =
  if i < length v then Ok (list_update v i x) else Fail Failure

// Trait declaration: [core::slice::index::private_slice_index::Sealed]
type core_slice_index_private_slice_index_Sealed (self : Type0) = unit

// Trait declaration: [core::slice::index::SliceIndex]
noeq type core_slice_index_SliceIndex (self t output : Type0) = {
  sealedInst : core_slice_index_private_slice_index_Sealed self;
  get : self → t → result (option output);
  get_mut : self → t → result (option output & (option output -> t));
  get_unchecked : self → const_raw_ptr t → result (const_raw_ptr output);
  get_unchecked_mut : self → mut_raw_ptr t → result (mut_raw_ptr output);
  index : self → t → result output;
  index_mut : self → t → result (output & (output -> t));
}

// [core::slice::index::[T]::index]: forward function
let core_slice_index_Slice_index
  (#t #idx #output : Type0) (inst : core_slice_index_SliceIndex idx (slice t) output)
  (s : slice t) (i : idx) : result output =
  let* x = inst.get i s in
  match x with
  | None -> Fail Failure
  | Some x -> Ok x

// [core::slice::index::Range:::get]: forward function
let core_slice_index_SliceIndexRangeUsizeSlice_get (#t : Type0) (i : core_ops_range_Range usize) (s : slice t) :
  result (option (slice t)) =
  admit () // TODO

// [core::slice::index::Range::get_mut]: forward function
let core_slice_index_SliceIndexRangeUsizeSlice_get_mut (#t : Type0) :
  core_ops_range_Range usize → slice t → result (option (slice t) & (option (slice t) -> slice t)) =
  admit () // TODO

// [core::slice::index::Range::get_unchecked]: forward function
let core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked
  (#t : Type0) :
  core_ops_range_Range usize → const_raw_ptr (slice t) → result (const_raw_ptr (slice t)) =
  // Don't know what the model should be - for now we always fail to make
  // sure code which uses it fails
  fun _ _ -> Fail Failure

// [core::slice::index::Range::get_unchecked_mut]: forward function
let core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked_mut
  (#t : Type0) :
  core_ops_range_Range usize → mut_raw_ptr (slice t) → result (mut_raw_ptr (slice t)) =
  // Don't know what the model should be - for now we always fail to make
  // sure code which uses it fails
  fun _ _ -> Fail Failure

// [core::slice::index::Range::index]: forward function
let core_slice_index_SliceIndexRangeUsizeSlice_index
  (#t : Type0) : core_ops_range_Range usize → slice t → result (slice t) =
  admit () // TODO

// [core::slice::index::Range::index_mut]: forward function
let core_slice_index_SliceIndexRangeUsizeSlice_index_mut (#t : Type0) :
  core_ops_range_Range usize → slice t → result (slice t & (slice t -> slice t)) =
  admit () // TODO

// [core::slice::index::[T]::index_mut]: forward function
let core_slice_index_Slice_index_mut
  (#t #idx #output : Type0) (inst : core_slice_index_SliceIndex idx (slice t) output) :
  slice t → idx → result (output & (output -> slice t)) =
  admit () // 

// [core::array::[T; N]::index]: forward function
let core_array_Array_index
  (#t #idx #out : Type0) (#n : usize) (inst : core_ops_index_Index (slice t) idx out)
  (a : array t n) (i : idx) : result out =
  admit () // TODO

// [core::array::[T; N]::index_mut]: forward function
let core_array_Array_index_mut
  (#t #idx #out : Type0) (#n : usize) (inst : core_ops_index_IndexMut (slice t) idx out)
  (a : array t n) (i : idx) :
  result (out & (out -> array t n)) =
  admit () // TODO

// Trait implementation: [core::slice::index::private_slice_index::Range]
let core_slice_index_private_slice_index_SealedSliceIndexRangeUsizeSliceInst
  : core_slice_index_private_slice_index_Sealed (core_ops_range_Range usize) = ()

// Trait implementation: [core::slice::index::Range]
let core_slice_index_SliceIndexRangeUsizeSliceInst (t : Type0) :
  core_slice_index_SliceIndex (core_ops_range_Range usize) (slice t) (slice t) = {
  sealedInst = core_slice_index_private_slice_index_SealedSliceIndexRangeUsizeSliceInst;
  get = core_slice_index_SliceIndexRangeUsizeSlice_get #t;
  get_mut = core_slice_index_SliceIndexRangeUsizeSlice_get_mut #t;
  get_unchecked = core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked #t;
  get_unchecked_mut = core_slice_index_SliceIndexRangeUsizeSlice_get_unchecked_mut #t;
  index = core_slice_index_SliceIndexRangeUsizeSlice_index #t;
  index_mut = core_slice_index_SliceIndexRangeUsizeSlice_index_mut #t;
}

// Trait implementation: [core::slice::index::[T]]
let core_ops_index_IndexSliceInst (#t #idx #output : Type0)
  (inst : core_slice_index_SliceIndex idx (slice t) output) :
  core_ops_index_Index (slice t) idx output = {
  index = core_slice_index_Slice_index inst;
}

// Trait implementation: [core::slice::index::[T]]
let core_ops_index_IndexMutSliceInst (#t #idx #output : Type0)
  (inst : core_slice_index_SliceIndex idx (slice t) output) :
  core_ops_index_IndexMut (slice t) idx output = {
  indexInst = core_ops_index_IndexSliceInst inst;
  index_mut = core_slice_index_Slice_index_mut inst;
}

// Trait implementation: [core::array::[T; N]]
let core_ops_index_IndexArrayInst (#t #idx #output : Type0) (n : usize)
  (inst : core_ops_index_Index (slice t) idx output) :
  core_ops_index_Index (array t n) idx output = {
  index = core_array_Array_index inst;
}

// Trait implementation: [core::array::[T; N]]
let core_ops_index_IndexMutArrayIInst (#t #idx #output : Type0) (n : usize)
  (inst : core_ops_index_IndexMut (slice t) idx output) :
  core_ops_index_IndexMut (array t n) idx output = {
  indexInst = core_ops_index_IndexArrayInst n inst.indexInst;
  index_mut = core_array_Array_index_mut inst;
}

// [core::slice::index::usize::get]: forward function
let core_slice_index_usize_get
  (#t : Type0) : usize → slice t → result (option t) =
  admit () // TODO

// [core::slice::index::usize::get_mut]: forward function
let core_slice_index_usize_get_mut (#t : Type0) :
  usize → slice t → result (option t & (option t -> slice t)) =
  admit () // TODO

// [core::slice::index::usize::get_unchecked]: forward function
let core_slice_index_usize_get_unchecked
  (#t : Type0) : usize → const_raw_ptr (slice t) → result (const_raw_ptr t) =
  admit () // TODO

// [core::slice::index::usize::get_unchecked_mut]: forward function
let core_slice_index_usize_get_unchecked_mut
  (#t : Type0) : usize → mut_raw_ptr (slice t) → result (mut_raw_ptr t) =
  admit () // TODO

// [core::slice::index::usize::index]: forward function
let core_slice_index_usize_index (#t : Type0) : usize → slice t → result t =
  admit () // TODO

// [core::slice::index::usize::index_mut]: forward function
let core_slice_index_usize_index_mut (#t : Type0) :
  usize → slice t → result (t & (t -> slice t)) =
  admit () // TODO

// Trait implementation: [core::slice::index::private_slice_index::usize]
let core_slice_index_private_slice_index_SealedUsizeInst
  : core_slice_index_private_slice_index_Sealed usize = ()

// Trait implementation: [core::slice::index::usize]
let core_slice_index_SliceIndexUsizeSliceInst (t : Type0) :
  core_slice_index_SliceIndex usize (slice t) t = {
  sealedInst = core_slice_index_private_slice_index_SealedUsizeInst;
  get = core_slice_index_usize_get #t;
  get_mut = core_slice_index_usize_get_mut #t;
  get_unchecked = core_slice_index_usize_get_unchecked #t;
  get_unchecked_mut = core_slice_index_usize_get_unchecked_mut #t;
  index = core_slice_index_usize_index #t;
  index_mut = core_slice_index_usize_index_mut #t;
}

// [alloc::vec::Vec::index]: forward function
let alloc_vec_Vec_index (#t #idx #output : Type0)
  (inst : core_slice_index_SliceIndex idx (slice t) output)
  (self : alloc_vec_Vec t) (i : idx) : result output =
  admit () // TODO

// [alloc::vec::Vec::index_mut]: forward function
let alloc_vec_Vec_index_mut (#t #idx #output : Type0)
  (inst : core_slice_index_SliceIndex idx (slice t) output)
  (self : alloc_vec_Vec t) (i : idx) :
  result (output & (output -> alloc_vec_Vec t)) =
  admit () // TODO

// Trait implementation: [alloc::vec::Vec]
let alloc_vec_Vec_IndexInst (#t #idx #output : Type0)
  (inst : core_slice_index_SliceIndex idx (slice t) output) :
  core_ops_index_Index (alloc_vec_Vec t) idx output = {
  index = alloc_vec_Vec_index inst;
}

// Trait implementation: [alloc::vec::Vec]
let alloc_vec_Vec_IndexMutInst (#t #idx #output : Type0)
  (inst : core_slice_index_SliceIndex idx (slice t) output) :
  core_ops_index_IndexMut (alloc_vec_Vec t) idx output = {
  indexInst = alloc_vec_Vec_IndexInst inst;
  index_mut = alloc_vec_Vec_index_mut inst;
}

(*** Theorems *)

let alloc_vec_Vec_index_eq (#a : Type0) (v : alloc_vec_Vec a) (i : usize) :
  Lemma (
    alloc_vec_Vec_index (core_slice_index_SliceIndexUsizeSliceInst a) v i ==
      alloc_vec_Vec_index_usize v i)
  [SMTPat (alloc_vec_Vec_index (core_slice_index_SliceIndexUsizeSliceInst a) v i)]
  =
  admit()

let alloc_vec_Vec_index_mut_eq (#a : Type0) (v : alloc_vec_Vec a) (i : usize) :
  Lemma (
    alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceInst a) v i ==
      alloc_vec_Vec_index_mut_usize v i)
  [SMTPat (alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceInst a) v i)]
  =
  admit()
