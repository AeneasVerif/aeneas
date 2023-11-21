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
| Return : v:a -> result a
| Fail : e:error -> result a

// Monadic return operator
unfold let return (#a : Type0) (x : a) : result a = Return x

// Monadic bind operator.
// Allows to use the notation:
// ```
// let* x = y in
// ...
// ```
unfold let (let*) (#a #b : Type0) (m: result a)
  (f: (x:a) -> Pure (result b) (requires (m == Return x)) (ensures fun _ -> True)) :
  result b =
  match m with
  | Return x -> f x
  | Fail e   -> Fail e

// Monadic assert(...)
let massert (b:bool) : result unit = if b then Return () else Fail Failure

// Normalize and unwrap a successful result (used for globals).
let eval_global (#a : Type0) (x : result a{Return? (normalize_term x)}) : a = Return?.v x

(*** Misc *)
type char = FStar.Char.char
type string = string

let is_zero (n: nat) : bool = n = 0
let decrease (n: nat{n > 0}) : nat = n - 1

let core_mem_replace (a : Type0) (x : a) (y : a) : a = x
let core_mem_replace_back (a : Type0) (x : a) (y : a) : a = y

// We don't really use raw pointers for now
type mut_raw_ptr (t : Type0) = { v : t }
type const_raw_ptr (t : Type0) = { v : t }

(*** Scalars *)
/// Rem.: most of the following code was partially generated

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
  if scalar_min ty <= x && scalar_max ty >= x then Return x else Fail Failure

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

let scalar_lxor (#ty : scalar_ty { is_unsigned ty && ty <> Usize })
    (x : scalar ty) (y : scalar ty) : scalar ty =
  match ty with
  | U8 -> FStar.UInt.logxor #8 x y
  | U16 -> FStar.UInt.logxor #16 x y
  | U32 -> FStar.UInt.logxor #32 x y
  | U64 -> FStar.UInt.logxor #64 x y
  | U128 -> FStar.UInt.logxor #128 x y

(** Cast an integer from a [src_ty] to a [tgt_ty] *)
// TODO: check the semantics of casts in Rust
let scalar_cast (src_ty : scalar_ty) (tgt_ty : scalar_ty) (x : scalar src_ty) : result (scalar tgt_ty) =
  mk_scalar tgt_ty x

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


let core_isize_min : isize = isize_min
let core_isize_max : isize = isize_max
let core_i8_min    : i8 = i8_min
let core_i8_max    : i8 = i8_max
let core_i16_min   : i16 = i16_min
let core_i16_max   : i16 = i16_max
let core_i32_min   : i32 = i32_min
let core_i32_max   : i32 = i32_max
let core_i64_min   : i64 = i64_min
let core_i64_max   : i64 = i64_max
let core_i128_min  : i128 = i128_min
let core_i128_max  : i128 = i128_max

let core_usize_min : usize = usize_min
let core_usize_max : usize = usize_max
let core_u8_min    : u8 = u8_min
let core_u8_max    : u8 = u8_max
let core_u16_min   : u16 = u16_min
let core_u16_max   : u16 = u16_max
let core_u32_min   : u32 = u32_min
let core_u32_max   : u32 = u32_max
let core_u64_min   : u64 = u64_min
let core_u64_max   : u64 = u64_max
let core_u128_min  : u128 = u128_min
let core_u128_max  : u128 = u128_max

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

/// Logical operators, defined for unsigned types only, so far
let u8_xor = scalar_lxor #U8
let u16_xor = scalar_lxor #U16
let u32_xor = scalar_lxor #U32
let u64_xor = scalar_lxor #U64
let u128_xor = scalar_lxor #U128

(*** core::ops *)

// Trait declaration: [core::ops::index::Index]
noeq type core_ops_index_Index (self idx : Type0) = {
  output : Type0;
  index : self → idx → result output
}

// Trait declaration: [core::ops::index::IndexMut]
noeq type core_ops_index_IndexMut (self idx : Type0) = {
  indexInst : core_ops_index_Index self idx;
  index_mut : self → idx → result indexInst.output;
  index_mut_back : self → idx → indexInst.output → result self;
}

// Trait declaration [core::ops::deref::Deref]
noeq type core_ops_deref_Deref (self : Type0) = {
  target : Type0;
  deref : self → result target;
}

// Trait declaration [core::ops::deref::DerefMut]
noeq type core_ops_deref_DerefMut (self : Type0) = {
  derefInst : core_ops_deref_Deref self;
  deref_mut : self → result derefInst.target;
  deref_mut_back : self → derefInst.target → result self;
}

type core_ops_range_Range (a : Type0) = {
  start : a;
  end_ : a;
}

(*** [alloc] *)

let alloc_boxed_Box_deref (t : Type0) (x : t) : result t = Return x
let alloc_boxed_Box_deref_mut (t : Type0) (x : t) : result t = Return x
let alloc_boxed_Box_deref_mut_back (t : Type) (_ : t) (x : t) : result t = Return x

// Trait instance
let alloc_boxed_Box_coreopsDerefInst (self : Type0) : core_ops_deref_Deref self = {
  target = self;
  deref = alloc_boxed_Box_deref self;
}

// Trait instance
let alloc_boxed_Box_coreopsDerefMutInst (self : Type0) : core_ops_deref_DerefMut self = {
  derefInst = alloc_boxed_Box_coreopsDerefInst self;
  deref_mut = alloc_boxed_Box_deref_mut self;
  deref_mut_back = alloc_boxed_Box_deref_mut_back self;
}

(*** Array *)
type array (a : Type0) (n : usize) = s:list a{length s = n}

// We tried putting the normalize_term condition as a refinement on the list
// but it didn't work. It works with the requires clause.
let mk_array (a : Type0) (n : usize)
  (l : list a) :
  Pure (array a n)
  (requires (normalize_term(FStar.List.Tot.length l) = n))
  (ensures (fun _ -> True)) =
  normalize_term_spec (FStar.List.Tot.length l);
  l

let array_index_usize (a : Type0) (n : usize) (x : array a n) (i : usize) : result a =
  if i < length x then Return (index x i)
  else Fail Failure

let array_update_usize (a : Type0) (n : usize) (x : array a n) (i : usize) (nx : a) : result (array a n) =
  if i < length x then Return (list_update x i nx)
  else Fail Failure

(*** Slice *)
type slice (a : Type0) = s:list a{length s <= usize_max}

let slice_len (a : Type0) (s : slice a) : usize = length s

let slice_index_usize (a : Type0) (x : slice a) (i : usize) : result a =
  if i < length x then Return (index x i)
  else Fail Failure

let slice_update_usize (a : Type0) (x : slice a) (i : usize) (nx : a) : result (slice a) =
  if i < length x then Return (list_update x i nx)
  else Fail Failure

(*** Subslices *)

let array_to_slice (a : Type0) (n : usize) (x : array a n) : result (slice a) = Return x
let array_from_slice (a : Type0) (n : usize) (x : array a n) (s : slice a) : result (array a n) =
  if length s = n then Return s
  else Fail Failure

// TODO: finish the definitions below (there lacks [List.drop] and [List.take] in the standard library *)
let array_subslice (a : Type0) (n : usize) (x : array a n) (r : core_ops_range_Range usize) : result (slice a) =
  admit()

let array_update_subslice (a : Type0) (n : usize) (x : array a n) (r : core_ops_range_Range usize) (ns : slice a) : result (array a n) =
  admit()

let array_repeat (a : Type0) (n : usize) (x : a) : array a n =
  admit()

let slice_subslice (a : Type0) (x : slice a) (r : core_ops_range_Range usize) : result (slice a) =
  admit()

let slice_update_subslice (a : Type0) (x : slice a) (r : core_ops_range_Range usize) (ns : slice a) : result (slice a) =
  admit()

(*** Vector *)
type alloc_vec_Vec (a : Type0) = v:list a{length v <= usize_max}

let alloc_vec_Vec_new (a  : Type0) : alloc_vec_Vec a = assert_norm(length #a [] == 0); []
let alloc_vec_Vec_len (a : Type0) (v : alloc_vec_Vec a) : usize = length v

// Helper
let alloc_vec_Vec_index_usize (#a : Type0) (v : alloc_vec_Vec a) (i : usize) : result a =
  if i < length v then Return (index v i) else Fail Failure
// Helper
let alloc_vec_Vec_update_usize (#a : Type0) (v : alloc_vec_Vec a) (i : usize) (x : a) : result (alloc_vec_Vec a) =
  if i < length v then Return (list_update v i x) else Fail Failure

// The **forward** function shouldn't be used
let alloc_vec_Vec_push_fwd (a  : Type0) (v : alloc_vec_Vec a) (x : a) : unit = ()
let alloc_vec_Vec_push (a  : Type0) (v : alloc_vec_Vec a) (x : a) :
  Pure (result (alloc_vec_Vec a))
  (requires True)
  (ensures (fun res ->
    match res with
    | Fail e -> e == Failure
    | Return v' -> length v' = length v + 1)) =
  if length v < usize_max then begin
    (**) assert_norm(length [x] == 1);
    (**) append_length v [x];
    (**) assert(length (append v [x]) = length v + 1);
    Return (append v [x])
    end
  else Fail Failure

// The **forward** function shouldn't be used
let alloc_vec_Vec_insert_fwd (a : Type0) (v : alloc_vec_Vec a) (i : usize) (x : a) : result unit =
  if i < length v then Return () else Fail Failure
let alloc_vec_Vec_insert (a : Type0) (v : alloc_vec_Vec a) (i : usize) (x : a) : result (alloc_vec_Vec a) =
  if i < length v then Return (list_update v i x) else Fail Failure

// Trait declaration: [core::slice::index::private_slice_index::Sealed]
type core_slice_index_private_slice_index_Sealed (self : Type0) = unit

// Trait declaration: [core::slice::index::SliceIndex]
noeq type core_slice_index_SliceIndex (self t : Type0) = {
  sealedInst : core_slice_index_private_slice_index_Sealed self;
  output : Type0;
  get : self → t → result (option output);
  get_mut : self → t → result (option output);
  get_mut_back : self → t → option output → result t;
  get_unchecked : self → const_raw_ptr t → result (const_raw_ptr output);
  get_unchecked_mut : self → mut_raw_ptr t → result (mut_raw_ptr output);
  index : self → t → result output;
  index_mut : self → t → result output;
  index_mut_back : self → t → output → result t;
}

// [core::slice::index::[T]::index]: forward function
let core_slice_index_Slice_index
  (t idx : Type0) (inst : core_slice_index_SliceIndex idx (slice t))
  (s : slice t) (i : idx) : result inst.output =
  let* x = inst.get i s in
  match x with
  | None -> Fail Failure
  | Some x -> Return x

// [core::slice::index::Range:::get]: forward function
let core_slice_index_Range_get (t : Type0) (i : core_ops_range_Range usize) (s : slice t) :
  result (option (slice t)) =
  admit () // TODO

// [core::slice::index::Range::get_mut]: forward function
let core_slice_index_Range_get_mut
  (t : Type0) : core_ops_range_Range usize → slice t → result (option (slice t)) =
  admit () // TODO

// [core::slice::index::Range::get_mut]: backward function 0
let core_slice_index_Range_get_mut_back
  (t : Type0) :
  core_ops_range_Range usize → slice t → option (slice t) → result (slice t) =
  admit () // TODO

// [core::slice::index::Range::get_unchecked]: forward function
let core_slice_index_Range_get_unchecked
  (t : Type0) :
  core_ops_range_Range usize → const_raw_ptr (slice t) → result (const_raw_ptr (slice t)) =
  // Don't know what the model should be - for now we always fail to make
  // sure code which uses it fails
  fun _ _ -> Fail Failure

// [core::slice::index::Range::get_unchecked_mut]: forward function
let core_slice_index_Range_get_unchecked_mut
  (t : Type0) :
  core_ops_range_Range usize → mut_raw_ptr (slice t) → result (mut_raw_ptr (slice t)) =
  // Don't know what the model should be - for now we always fail to make
  // sure code which uses it fails
  fun _ _ -> Fail Failure

// [core::slice::index::Range::index]: forward function
let core_slice_index_Range_index
  (t : Type0) : core_ops_range_Range usize → slice t → result (slice t) =
  admit () // TODO

// [core::slice::index::Range::index_mut]: forward function
let core_slice_index_Range_index_mut
  (t : Type0) : core_ops_range_Range usize → slice t → result (slice t) =
  admit () // TODO

// [core::slice::index::Range::index_mut]: backward function 0
let core_slice_index_Range_index_mut_back
  (t : Type0) : core_ops_range_Range usize → slice t → slice t → result (slice t) =
  admit () // TODO

// [core::slice::index::[T]::index_mut]: forward function
let core_slice_index_Slice_index_mut
  (t idx : Type0) (inst : core_slice_index_SliceIndex idx (slice t)) :
  slice t → idx → result inst.output =
  admit () // 

// [core::slice::index::[T]::index_mut]: backward function 0
let core_slice_index_Slice_index_mut_back
  (t idx : Type0) (inst : core_slice_index_SliceIndex idx (slice t)) :
  slice t → idx → inst.output → result (slice t) =
  admit () // TODO

// [core::array::[T; N]::index]: forward function
let core_array_Array_index
  (t idx : Type0) (n : usize) (inst : core_ops_index_Index (slice t) idx)
  (a : array t n) (i : idx) : result inst.output =
  admit () // TODO

// [core::array::[T; N]::index_mut]: forward function
let core_array_Array_index_mut
  (t idx : Type0) (n : usize) (inst : core_ops_index_IndexMut (slice t) idx)
  (a : array t n) (i : idx) : result inst.indexInst.output =
  admit () // TODO

// [core::array::[T; N]::index_mut]: backward function 0
let core_array_Array_index_mut_back
  (t idx : Type0) (n : usize) (inst : core_ops_index_IndexMut (slice t) idx)
  (a : array t n) (i : idx) (x : inst.indexInst.output) : result (array t n) =
  admit () // TODO

// Trait implementation: [core::slice::index::private_slice_index::Range]
let core_slice_index_private_slice_index_SealedRangeUsizeInst
  : core_slice_index_private_slice_index_Sealed (core_ops_range_Range usize) = ()

// Trait implementation: [core::slice::index::Range]
let core_slice_index_SliceIndexRangeUsizeSliceTInst (t : Type0) :
  core_slice_index_SliceIndex (core_ops_range_Range usize) (slice t) = {
  sealedInst = core_slice_index_private_slice_index_SealedRangeUsizeInst;
  output = slice t;
  get = core_slice_index_Range_get t;
  get_mut = core_slice_index_Range_get_mut t;
  get_mut_back = core_slice_index_Range_get_mut_back t;
  get_unchecked = core_slice_index_Range_get_unchecked t;
  get_unchecked_mut = core_slice_index_Range_get_unchecked_mut t;
  index = core_slice_index_Range_index t;
  index_mut = core_slice_index_Range_index_mut t;
  index_mut_back = core_slice_index_Range_index_mut_back t;
}

// Trait implementation: [core::slice::index::[T]]
let core_ops_index_IndexSliceTIInst (t idx : Type0)
  (inst : core_slice_index_SliceIndex idx (slice t)) :
  core_ops_index_Index (slice t) idx = {
  output = inst.output;
  index = core_slice_index_Slice_index t idx inst;
}

// Trait implementation: [core::slice::index::[T]]
let core_ops_index_IndexMutSliceTIInst (t idx : Type0)
  (inst : core_slice_index_SliceIndex idx (slice t)) :
  core_ops_index_IndexMut (slice t) idx = {
  indexInst = core_ops_index_IndexSliceTIInst t idx inst;
  index_mut = core_slice_index_Slice_index_mut t idx inst;
  index_mut_back = core_slice_index_Slice_index_mut_back t idx inst;
}

// Trait implementation: [core::array::[T; N]]
let core_ops_index_IndexArrayInst (t idx : Type0) (n : usize)
  (inst : core_ops_index_Index (slice t) idx) :
  core_ops_index_Index (array t n) idx = {
  output = inst.output;
  index = core_array_Array_index t idx n inst;
}

// Trait implementation: [core::array::[T; N]]
let core_ops_index_IndexMutArrayIInst (t idx : Type0) (n : usize)
  (inst : core_ops_index_IndexMut (slice t) idx) :
  core_ops_index_IndexMut (array t n) idx = {
  indexInst = core_ops_index_IndexArrayInst t idx n inst.indexInst;
  index_mut = core_array_Array_index_mut t idx n inst;
  index_mut_back = core_array_Array_index_mut_back t idx n inst;
}

// [core::slice::index::usize::get]: forward function
let core_slice_index_usize_get
  (t : Type0) : usize → slice t → result (option t) =
  admit () // TODO

// [core::slice::index::usize::get_mut]: forward function
let core_slice_index_usize_get_mut
  (t : Type0) : usize → slice t → result (option t) =
  admit () // TODO

// [core::slice::index::usize::get_mut]: backward function 0
let core_slice_index_usize_get_mut_back
  (t : Type0) : usize → slice t → option t → result (slice t) =
  admit () // TODO

// [core::slice::index::usize::get_unchecked]: forward function
let core_slice_index_usize_get_unchecked
  (t : Type0) : usize → const_raw_ptr (slice t) → result (const_raw_ptr t) =
  admit () // TODO

// [core::slice::index::usize::get_unchecked_mut]: forward function
let core_slice_index_usize_get_unchecked_mut
  (t : Type0) : usize → mut_raw_ptr (slice t) → result (mut_raw_ptr t) =
  admit () // TODO

// [core::slice::index::usize::index]: forward function
let core_slice_index_usize_index (t : Type0) : usize → slice t → result t =
  admit () // TODO

// [core::slice::index::usize::index_mut]: forward function
let core_slice_index_usize_index_mut (t : Type0) : usize → slice t → result t =
  admit () // TODO

// [core::slice::index::usize::index_mut]: backward function 0
let core_slice_index_usize_index_mut_back
  (t : Type0) : usize → slice t → t → result (slice t) =
  admit () // TODO

// Trait implementation: [core::slice::index::private_slice_index::usize]
let core_slice_index_private_slice_index_SealedUsizeInst
  : core_slice_index_private_slice_index_Sealed usize = ()

// Trait implementation: [core::slice::index::usize]
let core_slice_index_SliceIndexUsizeSliceTInst (t : Type0) :
  core_slice_index_SliceIndex usize (slice t) = {
  sealedInst = core_slice_index_private_slice_index_SealedUsizeInst;
  output = t;
  get = core_slice_index_usize_get t;
  get_mut = core_slice_index_usize_get_mut t;
  get_mut_back = core_slice_index_usize_get_mut_back t;
  get_unchecked = core_slice_index_usize_get_unchecked t;
  get_unchecked_mut = core_slice_index_usize_get_unchecked_mut t;
  index = core_slice_index_usize_index t;
  index_mut = core_slice_index_usize_index_mut t;
  index_mut_back = core_slice_index_usize_index_mut_back t;
}

// [alloc::vec::Vec::index]: forward function
let alloc_vec_Vec_index (t idx : Type0) (inst : core_slice_index_SliceIndex idx (slice t))
  (self : alloc_vec_Vec t) (i : idx) : result inst.output =
  admit () // TODO

// [alloc::vec::Vec::index_mut]: forward function
let alloc_vec_Vec_index_mut (t idx : Type0) (inst : core_slice_index_SliceIndex idx (slice t))
  (self : alloc_vec_Vec t) (i : idx) : result inst.output =
  admit () // TODO

// [alloc::vec::Vec::index_mut]: backward function 0
let alloc_vec_Vec_index_mut_back
  (t idx : Type0) (inst : core_slice_index_SliceIndex idx (slice t))
  (self : alloc_vec_Vec t) (i : idx) (x : inst.output) : result (alloc_vec_Vec t) =
  admit () // TODO

// Trait implementation: [alloc::vec::Vec]
let alloc_vec_Vec_coreopsindexIndexInst (t idx : Type0)
  (inst : core_slice_index_SliceIndex idx (slice t)) :
  core_ops_index_Index (alloc_vec_Vec t) idx = {
  output = inst.output;
  index = alloc_vec_Vec_index t idx inst;
}

// Trait implementation: [alloc::vec::Vec]
let alloc_vec_Vec_coreopsindexIndexMutInst (t idx : Type0)
  (inst : core_slice_index_SliceIndex idx (slice t)) :
  core_ops_index_IndexMut (alloc_vec_Vec t) idx = {
  indexInst = alloc_vec_Vec_coreopsindexIndexInst t idx inst;
  index_mut = alloc_vec_Vec_index_mut t idx inst;
  index_mut_back = alloc_vec_Vec_index_mut_back t idx inst;
}

(*** Theorems *)

let alloc_vec_Vec_index_eq (#a : Type0) (v : alloc_vec_Vec a) (i : usize) :
  Lemma (
    alloc_vec_Vec_index a usize (core_slice_index_SliceIndexUsizeSliceTInst a) v i ==
      alloc_vec_Vec_index_usize v i)
  [SMTPat (alloc_vec_Vec_index a usize (core_slice_index_SliceIndexUsizeSliceTInst a) v i)]
  =
  admit()

let alloc_vec_Vec_index_mut_eq (#a : Type0) (v : alloc_vec_Vec a) (i : usize) :
  Lemma (
    alloc_vec_Vec_index_mut a usize (core_slice_index_SliceIndexUsizeSliceTInst a) v i ==
      alloc_vec_Vec_index_usize v i)
  [SMTPat (alloc_vec_Vec_index_mut a usize (core_slice_index_SliceIndexUsizeSliceTInst a) v i)]
  =
  admit()

let alloc_vec_Vec_index_mut_back_eq (#a : Type0) (v : alloc_vec_Vec a) (i : usize) (x : a) :
  Lemma (
    alloc_vec_Vec_index_mut_back a usize (core_slice_index_SliceIndexUsizeSliceTInst a) v i x ==
      alloc_vec_Vec_update_usize v i x)
  [SMTPat (alloc_vec_Vec_index_mut_back a usize (core_slice_index_SliceIndexUsizeSliceTInst a) v i x)]
  =
  admit()
