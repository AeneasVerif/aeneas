(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [arrays] *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Module Arrays.

(** [arrays::AB]
    Source: 'tests/src/arrays.rs', lines 6:0-9:1 *)
Inductive AB_t := | AB_A : AB_t | AB_B : AB_t.

(** [arrays::incr]:
    Source: 'tests/src/arrays.rs', lines 11:0-13:1 *)
Definition incr (x : u32) : result u32 :=
  u32_add x 1%u32.

(** [arrays::array_to_shared_slice_]:
    Source: 'tests/src/arrays.rs', lines 19:0-21:1 *)
Definition array_to_shared_slice_
  {T : Type} (s : array T 32%usize) : result (slice T) :=
  array_to_slice s
.

(** [arrays::array_to_mut_slice_]:
    Source: 'tests/src/arrays.rs', lines 24:0-26:1 *)
Definition array_to_mut_slice_
  {T : Type} (s : array T 32%usize) :
  result ((slice T) * (slice T -> array T 32%usize))
  :=
  array_to_slice_mut s
.

(** [arrays::array_len]:
    Source: 'tests/src/arrays.rs', lines 28:0-30:1 *)
Definition array_len {T : Type} (s : array T 32%usize) : result usize :=
  s1 <- array_to_slice s; Ok (slice_len s1)
.

(** [arrays::shared_array_len]:
    Source: 'tests/src/arrays.rs', lines 32:0-34:1 *)
Definition shared_array_len {T : Type} (s : array T 32%usize) : result usize :=
  s1 <- array_to_slice s; Ok (slice_len s1)
.

(** [arrays::shared_slice_len]:
    Source: 'tests/src/arrays.rs', lines 36:0-38:1 *)
Definition shared_slice_len {T : Type} (s : slice T) : result usize :=
  Ok (slice_len s)
.

(** [arrays::index_array_shared]:
    Source: 'tests/src/arrays.rs', lines 40:0-42:1 *)
Definition index_array_shared
  {T : Type} (s : array T 32%usize) (i : usize) : result T :=
  array_index_usize s i
.

(** [arrays::index_array_u32]:
    Source: 'tests/src/arrays.rs', lines 47:0-49:1 *)
Definition index_array_u32 (s : array u32 32%usize) (i : usize) : result u32 :=
  array_index_usize s i
.

(** [arrays::index_array_copy]:
    Source: 'tests/src/arrays.rs', lines 51:0-53:1 *)
Definition index_array_copy (x : array u32 32%usize) : result u32 :=
  array_index_usize x 0%usize
.

(** [arrays::index_mut_array]:
    Source: 'tests/src/arrays.rs', lines 55:0-57:1 *)
Definition index_mut_array
  {T : Type} (s : array T 32%usize) (i : usize) :
  result (T * (T -> array T 32%usize))
  :=
  array_index_mut_usize s i
.

(** [arrays::index_slice]:
    Source: 'tests/src/arrays.rs', lines 59:0-61:1 *)
Definition index_slice {T : Type} (s : slice T) (i : usize) : result T :=
  slice_index_usize s i
.

(** [arrays::index_mut_slice]:
    Source: 'tests/src/arrays.rs', lines 63:0-65:1 *)
Definition index_mut_slice
  {T : Type} (s : slice T) (i : usize) : result (T * (T -> slice T)) :=
  slice_index_mut_usize s i
.

(** [arrays::slice_subslice_shared_]:
    Source: 'tests/src/arrays.rs', lines 67:0-69:1 *)
Definition slice_subslice_shared_
  (x : slice u32) (y : usize) (z : usize) : result (slice u32) :=
  core_slice_index_Slice_index (core_slice_index_SliceIndexRangeUsizeSliceTInst
    u32) x
    {| core_ops_range_Range_start := y; core_ops_range_Range_end_ := z |}
.

(** [arrays::slice_subslice_mut_]:
    Source: 'tests/src/arrays.rs', lines 71:0-73:1 *)
Definition slice_subslice_mut_
  (x : slice u32) (y : usize) (z : usize) :
  result ((slice u32) * (slice u32 -> slice u32))
  :=
  core_slice_index_Slice_index_mut
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32) x
    {| core_ops_range_Range_start := y; core_ops_range_Range_end_ := z |}
.

(** [arrays::array_to_slice_shared_]:
    Source: 'tests/src/arrays.rs', lines 75:0-77:1 *)
Definition array_to_slice_shared_
  (x : array u32 32%usize) : result (slice u32) :=
  array_to_slice x
.

(** [arrays::array_to_slice_mut_]:
    Source: 'tests/src/arrays.rs', lines 79:0-81:1 *)
Definition array_to_slice_mut_
  (x : array u32 32%usize) :
  result ((slice u32) * (slice u32 -> array u32 32%usize))
  :=
  array_to_slice_mut x
.

(** [arrays::array_subslice_shared_]:
    Source: 'tests/src/arrays.rs', lines 83:0-85:1 *)
Definition array_subslice_shared_
  (x : array u32 32%usize) (y : usize) (z : usize) : result (slice u32) :=
  core_array_Array_index (core_ops_index_IndexSliceTIInst
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32)) x
    {| core_ops_range_Range_start := y; core_ops_range_Range_end_ := z |}
.

(** [arrays::array_subslice_mut_]:
    Source: 'tests/src/arrays.rs', lines 87:0-89:1 *)
Definition array_subslice_mut_
  (x : array u32 32%usize) (y : usize) (z : usize) :
  result ((slice u32) * (slice u32 -> array u32 32%usize))
  :=
  core_array_Array_index_mut (core_ops_index_IndexMutSliceTIInst
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32)) x
    {| core_ops_range_Range_start := y; core_ops_range_Range_end_ := z |}
.

(** [arrays::index_slice_0]:
    Source: 'tests/src/arrays.rs', lines 91:0-93:1 *)
Definition index_slice_0 {T : Type} (s : slice T) : result T :=
  slice_index_usize s 0%usize
.

(** [arrays::index_array_0]:
    Source: 'tests/src/arrays.rs', lines 95:0-97:1 *)
Definition index_array_0 {T : Type} (s : array T 32%usize) : result T :=
  array_index_usize s 0%usize
.

(** [arrays::index_index_array]:
    Source: 'tests/src/arrays.rs', lines 106:0-108:1 *)
Definition index_index_array
  (s : array (array u32 32%usize) 32%usize) (i : usize) (j : usize) :
  result u32
  :=
  a <- array_index_usize s i; array_index_usize a j
.

(** [arrays::update_update_array]:
    Source: 'tests/src/arrays.rs', lines 117:0-119:1 *)
Definition update_update_array
  (s : array (array u32 32%usize) 32%usize) (i : usize) (j : usize) :
  result (array (array u32 32%usize) 32%usize)
  :=
  p <- array_index_mut_usize s i;
  let (a, index_mut_back) := p in
  a1 <- array_update_usize a j 0%u32;
  Ok (index_mut_back a1)
.

(** [arrays::array_local_deep_copy]:
    Source: 'tests/src/arrays.rs', lines 121:0-123:1 *)
Definition array_local_deep_copy (x : array u32 32%usize) : result unit :=
  Ok tt
.

(** [arrays::array_update1]:
    Source: 'tests/src/arrays.rs', lines 126:0-128:1 *)
Definition array_update1
  (a : slice u32) (i : usize) (x : u32) : result (slice u32) :=
  i1 <- usize_add i 1%usize; i2 <- u32_add x 1%u32; slice_update_usize a i1 i2
.

(** [arrays::array_update2]:
    Source: 'tests/src/arrays.rs', lines 131:0-134:1 *)
Definition array_update2
  (a : slice u32) (i : usize) (x : u32) : result (slice u32) :=
  i1 <- u32_add x 1%u32;
  a1 <- slice_update_usize a i i1;
  i2 <- usize_add i 1%usize;
  i3 <- u32_add x 1%u32;
  slice_update_usize a1 i2 i3
.

(** [arrays::array_update3]:
    Source: 'tests/src/arrays.rs', lines 136:0-140:1 *)
Definition array_update3
  (a : slice u32) (i : usize) (x : u32) : result (slice u32) :=
  a1 <- slice_update_usize a i x;
  i1 <- usize_add i 1%usize;
  a2 <- slice_update_usize a1 i1 x;
  i2 <- usize_add i 2%usize;
  slice_update_usize a2 i2 x
.

(** [arrays::take_array]:
    Source: 'tests/src/arrays.rs', lines 142:0-142:33 *)
Definition take_array (a : array u32 2%usize) : result unit :=
  Ok tt.

(** [arrays::take_array_borrow]:
    Source: 'tests/src/arrays.rs', lines 143:0-143:41 *)
Definition take_array_borrow (a : array u32 2%usize) : result unit :=
  Ok tt.

(** [arrays::take_slice]:
    Source: 'tests/src/arrays.rs', lines 144:0-144:31 *)
Definition take_slice (s : slice u32) : result unit :=
  Ok tt.

(** [arrays::take_mut_slice]:
    Source: 'tests/src/arrays.rs', lines 145:0-145:39 *)
Definition take_mut_slice (s : slice u32) : result (slice u32) :=
  Ok s.

(** [arrays::const_array]:
    Source: 'tests/src/arrays.rs', lines 147:0-149:1 *)
Definition const_array : result (array u32 2%usize) :=
  Ok (mk_array 2%usize [ 0%u32; 0%u32 ])
.

(** [arrays::const_slice]:
    Source: 'tests/src/arrays.rs', lines 151:0-153:1 *)
Definition const_slice : result unit :=
  _ <- array_to_slice (mk_array 2%usize [ 0%u32; 0%u32 ]); Ok tt
.

(** [arrays::take_all]:
    Source: 'tests/src/arrays.rs', lines 161:0-173:1 *)
Definition take_all : result unit :=
  _ <- take_array (mk_array 2%usize [ 0%u32; 0%u32 ]);
  _ <- take_array (mk_array 2%usize [ 0%u32; 0%u32 ]);
  _ <- take_array_borrow (mk_array 2%usize [ 0%u32; 0%u32 ]);
  s <- array_to_slice (mk_array 2%usize [ 0%u32; 0%u32 ]);
  _ <- take_slice s;
  p <- array_to_slice_mut (mk_array 2%usize [ 0%u32; 0%u32 ]);
  let (s1, _) := p in
  _ <- take_mut_slice s1;
  Ok tt
.

(** [arrays::index_array]:
    Source: 'tests/src/arrays.rs', lines 175:0-177:1 *)
Definition index_array (x : array u32 2%usize) : result u32 :=
  array_index_usize x 0%usize
.

(** [arrays::index_array_borrow]:
    Source: 'tests/src/arrays.rs', lines 178:0-180:1 *)
Definition index_array_borrow (x : array u32 2%usize) : result u32 :=
  array_index_usize x 0%usize
.

(** [arrays::index_slice_u32_0]:
    Source: 'tests/src/arrays.rs', lines 182:0-184:1 *)
Definition index_slice_u32_0 (x : slice u32) : result u32 :=
  slice_index_usize x 0%usize
.

(** [arrays::index_mut_slice_u32_0]:
    Source: 'tests/src/arrays.rs', lines 186:0-188:1 *)
Definition index_mut_slice_u32_0
  (x : slice u32) : result (u32 * (slice u32)) :=
  i <- slice_index_usize x 0%usize; Ok (i, x)
.

(** [arrays::index_all]:
    Source: 'tests/src/arrays.rs', lines 190:0-202:1 *)
Definition index_all : result u32 :=
  i <- index_array (mk_array 2%usize [ 0%u32; 0%u32 ]);
  i1 <- index_array (mk_array 2%usize [ 0%u32; 0%u32 ]);
  i2 <- u32_add i i1;
  i3 <- index_array_borrow (mk_array 2%usize [ 0%u32; 0%u32 ]);
  i4 <- u32_add i2 i3;
  s <- array_to_slice (mk_array 2%usize [ 0%u32; 0%u32 ]);
  i5 <- index_slice_u32_0 s;
  i6 <- u32_add i4 i5;
  p <- array_to_slice_mut (mk_array 2%usize [ 0%u32; 0%u32 ]);
  let (s1, _) := p in
  p1 <- index_mut_slice_u32_0 s1;
  let (i7, _) := p1 in
  u32_add i6 i7
.

(** [arrays::update_array]:
    Source: 'tests/src/arrays.rs', lines 204:0-206:1 *)
Definition update_array (x : array u32 2%usize) : result unit :=
  _ <- array_index_mut_usize x 0%usize; Ok tt
.

(** [arrays::update_array_mut_borrow]:
    Source: 'tests/src/arrays.rs', lines 207:0-209:1 *)
Definition update_array_mut_borrow
  (x : array u32 2%usize) : result (array u32 2%usize) :=
  array_update_usize x 0%usize 1%u32
.

(** [arrays::update_mut_slice]:
    Source: 'tests/src/arrays.rs', lines 210:0-212:1 *)
Definition update_mut_slice (x : slice u32) : result (slice u32) :=
  slice_update_usize x 0%usize 1%u32
.

(** [arrays::update_all]:
    Source: 'tests/src/arrays.rs', lines 214:0-220:1 *)
Definition update_all : result unit :=
  _ <- update_array (mk_array 2%usize [ 0%u32; 0%u32 ]);
  _ <- update_array (mk_array 2%usize [ 0%u32; 0%u32 ]);
  x <- update_array_mut_borrow (mk_array 2%usize [ 0%u32; 0%u32 ]);
  p <- array_to_slice_mut x;
  let (s, _) := p in
  _ <- update_mut_slice s;
  Ok tt
.

(** [arrays::incr_array]:
    Source: 'tests/src/arrays.rs', lines 222:0-224:1 *)
Definition incr_array (x : array u32 2%usize) : result (array u32 2%usize) :=
  i <- array_index_usize x 0%usize;
  i1 <- u32_add i 1%u32;
  array_update_usize x 0%usize i1
.

(** [arrays::incr_slice]:
    Source: 'tests/src/arrays.rs', lines 226:0-228:1 *)
Definition incr_slice (x : slice u32) : result (slice u32) :=
  i <- slice_index_usize x 0%usize;
  i1 <- u32_add i 1%u32;
  slice_update_usize x 0%usize i1
.

(** [arrays::range_all]:
    Source: 'tests/src/arrays.rs', lines 233:0-237:1 *)
Definition range_all : result unit :=
  p <-
    core_array_Array_index_mut (core_ops_index_IndexMutSliceTIInst
      (core_slice_index_SliceIndexRangeUsizeSliceTInst u32))
      (mk_array 4%usize [ 0%u32; 0%u32; 0%u32; 0%u32 ])
      {|
        core_ops_range_Range_start := 1%usize;
        core_ops_range_Range_end_ := 3%usize
      |};
  let (s, _) := p in
  _ <- update_mut_slice s;
  Ok tt
.

(** [arrays::deref_array_borrow]:
    Source: 'tests/src/arrays.rs', lines 242:0-245:1 *)
Definition deref_array_borrow (x : array u32 2%usize) : result u32 :=
  array_index_usize x 0%usize
.

(** [arrays::deref_array_mut_borrow]:
    Source: 'tests/src/arrays.rs', lines 247:0-250:1 *)
Definition deref_array_mut_borrow
  (x : array u32 2%usize) : result (u32 * (array u32 2%usize)) :=
  i <- array_index_usize x 0%usize; Ok (i, x)
.

(** [arrays::take_array_t]:
    Source: 'tests/src/arrays.rs', lines 255:0-255:34 *)
Definition take_array_t (a : array AB_t 2%usize) : result unit :=
  Ok tt.

(** [arrays::non_copyable_array]:
    Source: 'tests/src/arrays.rs', lines 257:0-265:1 *)
Definition non_copyable_array : result unit :=
  take_array_t (mk_array 2%usize [ AB_A; AB_B ])
.

(** [arrays::sum]: loop 0:
    Source: 'tests/src/arrays.rs', lines 273:4-276:5 *)
Fixpoint sum_loop
  (n : nat) (s : slice u32) (sum1 : u32) (i : usize) : result u32 :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    let i1 := slice_len s in
    if i s< i1
    then (
      i2 <- slice_index_usize s i;
      sum3 <- u32_add sum1 i2;
      i3 <- usize_add i 1%usize;
      sum_loop n1 s sum3 i3)
    else Ok sum1
  end
.

(** [arrays::sum]:
    Source: 'tests/src/arrays.rs', lines 270:0-278:1 *)
Definition sum (n : nat) (s : slice u32) : result u32 :=
  sum_loop n s 0%u32 0%usize
.

(** [arrays::sum2]: loop 0:
    Source: 'tests/src/arrays.rs', lines 284:4-287:5 *)
Fixpoint sum2_loop
  (n : nat) (s : slice u32) (s2 : slice u32) (sum1 : u32) (i : usize) :
  result u32
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    let i1 := slice_len s in
    if i s< i1
    then (
      i2 <- slice_index_usize s i;
      i3 <- slice_index_usize s2 i;
      i4 <- u32_add i2 i3;
      sum3 <- u32_add sum1 i4;
      i5 <- usize_add i 1%usize;
      sum2_loop n1 s s2 sum3 i5)
    else Ok sum1
  end
.

(** [arrays::sum2]:
    Source: 'tests/src/arrays.rs', lines 280:0-289:1 *)
Definition sum2 (n : nat) (s : slice u32) (s2 : slice u32) : result u32 :=
  let i := slice_len s in
  let i1 := slice_len s2 in
  _ <- massert (i s= i1);
  sum2_loop n s s2 0%u32 0%usize
.

(** [arrays::f0]:
    Source: 'tests/src/arrays.rs', lines 291:0-294:1 *)
Definition f0 : result unit :=
  p <- array_to_slice_mut (mk_array 2%usize [ 1%u32; 2%u32 ]);
  let (s, _) := p in
  _ <- slice_index_mut_usize s 0%usize;
  Ok tt
.

(** [arrays::f1]:
    Source: 'tests/src/arrays.rs', lines 296:0-299:1 *)
Definition f1 : result unit :=
  _ <- array_index_mut_usize (mk_array 2%usize [ 1%u32; 2%u32 ]) 0%usize; Ok tt
.

(** [arrays::f2]:
    Source: 'tests/src/arrays.rs', lines 301:0-301:20 *)
Definition f2 (i : u32) : result unit :=
  Ok tt.

(** [arrays::f4]:
    Source: 'tests/src/arrays.rs', lines 310:0-312:1 *)
Definition f4
  (x : array u32 32%usize) (y : usize) (z : usize) : result (slice u32) :=
  core_array_Array_index (core_ops_index_IndexSliceTIInst
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32)) x
    {| core_ops_range_Range_start := y; core_ops_range_Range_end_ := z |}
.

(** [arrays::f3]:
    Source: 'tests/src/arrays.rs', lines 303:0-308:1 *)
Definition f3 (n : nat) : result u32 :=
  i <- array_index_usize (mk_array 2%usize [ 1%u32; 2%u32 ]) 0%usize;
  _ <- f2 i;
  let b := array_repeat 32%usize 0%u32 in
  s <- array_to_slice (mk_array 2%usize [ 1%u32; 2%u32 ]);
  s1 <- f4 b 16%usize 18%usize;
  sum2 n s s1
.

(** [arrays::SZ]
    Source: 'tests/src/arrays.rs', lines 314:0-314:25 *)
Definition sz_body : result usize := Ok 32%usize.
Definition sz : usize := sz_body%global.

(** [arrays::f5]:
    Source: 'tests/src/arrays.rs', lines 317:0-319:1 *)
Definition f5 (x : array u32 32%usize) : result u32 :=
  array_index_usize x 0%usize
.

(** [arrays::ite]:
    Source: 'tests/src/arrays.rs', lines 322:0-329:1 *)
Definition ite : result unit :=
  p <- array_to_slice_mut (mk_array 2%usize [ 0%u32; 0%u32 ]);
  let (s, _) := p in
  _ <- index_mut_slice_u32_0 s;
  p1 <- array_to_slice_mut (mk_array 2%usize [ 0%u32; 0%u32 ]);
  let (s1, _) := p1 in
  _ <- index_mut_slice_u32_0 s1;
  Ok tt
.

(** [arrays::zero_slice]: loop 0:
    Source: 'tests/src/arrays.rs', lines 334:4-337:5 *)
Fixpoint zero_slice_loop
  (n : nat) (a : slice u8) (i : usize) (len : usize) : result (slice u8) :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if i s< len
    then (
      a1 <- slice_update_usize a i 0%u8;
      i1 <- usize_add i 1%usize;
      zero_slice_loop n1 a1 i1 len)
    else Ok a
  end
.

(** [arrays::zero_slice]:
    Source: 'tests/src/arrays.rs', lines 331:0-338:1 *)
Definition zero_slice (n : nat) (a : slice u8) : result (slice u8) :=
  let len := slice_len a in zero_slice_loop n a 0%usize len
.

(** [arrays::iter_mut_slice]: loop 0:
    Source: 'tests/src/arrays.rs', lines 343:4-345:5 *)
Fixpoint iter_mut_slice_loop
  (n : nat) (len : usize) (i : usize) : result unit :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if i s< len
    then (i1 <- usize_add i 1%usize; iter_mut_slice_loop n1 len i1)
    else Ok tt
  end
.

(** [arrays::iter_mut_slice]:
    Source: 'tests/src/arrays.rs', lines 340:0-346:1 *)
Definition iter_mut_slice (n : nat) (a : slice u8) : result (slice u8) :=
  let len := slice_len a in _ <- iter_mut_slice_loop n len 0%usize; Ok a
.

(** [arrays::sum_mut_slice]: loop 0:
    Source: 'tests/src/arrays.rs', lines 351:4-354:5 *)
Fixpoint sum_mut_slice_loop
  (n : nat) (a : slice u32) (i : usize) (s : u32) : result u32 :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    let i1 := slice_len a in
    if i s< i1
    then (
      i2 <- slice_index_usize a i;
      s1 <- u32_add s i2;
      i3 <- usize_add i 1%usize;
      sum_mut_slice_loop n1 a i3 s1)
    else Ok s
  end
.

(** [arrays::sum_mut_slice]:
    Source: 'tests/src/arrays.rs', lines 348:0-356:1 *)
Definition sum_mut_slice
  (n : nat) (a : slice u32) : result (u32 * (slice u32)) :=
  i <- sum_mut_slice_loop n a 0%usize 0%u32; Ok (i, a)
.

End Arrays.
