(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [array] *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Module Array.

(** [array::AB] *)
Inductive AB_t := | AB_A : AB_t | AB_B : AB_t.

(** [array::incr]: merged forward/backward function
    (there is a single backward function, and the forward function returns ()) *)
Definition incr (x : u32) : result u32 :=
  u32_add x 1%u32.

(** [array::array_to_shared_slice_]: forward function *)
Definition array_to_shared_slice_
  (T : Type) (s : array T 32%usize) : result (slice T) :=
  array_to_slice T 32%usize s
.

(** [array::array_to_mut_slice_]: forward function *)
Definition array_to_mut_slice_
  (T : Type) (s : array T 32%usize) : result (slice T) :=
  array_to_slice T 32%usize s
.

(** [array::array_to_mut_slice_]: backward function 0 *)
Definition array_to_mut_slice__back
  (T : Type) (s : array T 32%usize) (ret : slice T) :
  result (array T 32%usize)
  :=
  array_from_slice T 32%usize s ret
.

(** [array::array_len]: forward function *)
Definition array_len (T : Type) (s : array T 32%usize) : result usize :=
  s0 <- array_to_slice T 32%usize s; let i := slice_len T s0 in Return i
.

(** [array::shared_array_len]: forward function *)
Definition shared_array_len (T : Type) (s : array T 32%usize) : result usize :=
  s0 <- array_to_slice T 32%usize s; let i := slice_len T s0 in Return i
.

(** [array::shared_slice_len]: forward function *)
Definition shared_slice_len (T : Type) (s : slice T) : result usize :=
  let i := slice_len T s in Return i
.

(** [array::index_array_shared]: forward function *)
Definition index_array_shared
  (T : Type) (s : array T 32%usize) (i : usize) : result T :=
  array_index_usize T 32%usize s i
.

(** [array::index_array_u32]: forward function *)
Definition index_array_u32 (s : array u32 32%usize) (i : usize) : result u32 :=
  array_index_usize u32 32%usize s i
.

(** [array::index_array_copy]: forward function *)
Definition index_array_copy (x : array u32 32%usize) : result u32 :=
  array_index_usize u32 32%usize x 0%usize
.

(** [array::index_mut_array]: forward function *)
Definition index_mut_array
  (T : Type) (s : array T 32%usize) (i : usize) : result T :=
  array_index_usize T 32%usize s i
.

(** [array::index_mut_array]: backward function 0 *)
Definition index_mut_array_back
  (T : Type) (s : array T 32%usize) (i : usize) (ret : T) :
  result (array T 32%usize)
  :=
  array_update_usize T 32%usize s i ret
.

(** [array::index_slice]: forward function *)
Definition index_slice (T : Type) (s : slice T) (i : usize) : result T :=
  slice_index_usize T s i
.

(** [array::index_mut_slice]: forward function *)
Definition index_mut_slice (T : Type) (s : slice T) (i : usize) : result T :=
  slice_index_usize T s i
.

(** [array::index_mut_slice]: backward function 0 *)
Definition index_mut_slice_back
  (T : Type) (s : slice T) (i : usize) (ret : T) : result (slice T) :=
  slice_update_usize T s i ret
.

(** [array::slice_subslice_shared_]: forward function *)
Definition slice_subslice_shared_
  (x : slice u32) (y : usize) (z : usize) : result (slice u32) :=
  core_slice_index_Slice_index u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32) x
    {| core_ops_range_Range_start := y; core_ops_range_Range_end_ := z |}
.

(** [array::slice_subslice_mut_]: forward function *)
Definition slice_subslice_mut_
  (x : slice u32) (y : usize) (z : usize) : result (slice u32) :=
  core_slice_index_Slice_index_mut u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32) x
    {| core_ops_range_Range_start := y; core_ops_range_Range_end_ := z |}
.

(** [array::slice_subslice_mut_]: backward function 0 *)
Definition slice_subslice_mut__back
  (x : slice u32) (y : usize) (z : usize) (ret : slice u32) :
  result (slice u32)
  :=
  core_slice_index_Slice_index_mut_back u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32) x
    {| core_ops_range_Range_start := y; core_ops_range_Range_end_ := z |} ret
.

(** [array::array_to_slice_shared_]: forward function *)
Definition array_to_slice_shared_
  (x : array u32 32%usize) : result (slice u32) :=
  array_to_slice u32 32%usize x
.

(** [array::array_to_slice_mut_]: forward function *)
Definition array_to_slice_mut_ (x : array u32 32%usize) : result (slice u32) :=
  array_to_slice u32 32%usize x
.

(** [array::array_to_slice_mut_]: backward function 0 *)
Definition array_to_slice_mut__back
  (x : array u32 32%usize) (ret : slice u32) : result (array u32 32%usize) :=
  array_from_slice u32 32%usize x ret
.

(** [array::array_subslice_shared_]: forward function *)
Definition array_subslice_shared_
  (x : array u32 32%usize) (y : usize) (z : usize) : result (slice u32) :=
  core_array_Array_index u32 (core_ops_range_Range usize) 32%usize
    (core_ops_index_IndexSliceTIInst u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32)) x
    {| core_ops_range_Range_start := y; core_ops_range_Range_end_ := z |}
.

(** [array::array_subslice_mut_]: forward function *)
Definition array_subslice_mut_
  (x : array u32 32%usize) (y : usize) (z : usize) : result (slice u32) :=
  core_array_Array_index_mut u32 (core_ops_range_Range usize) 32%usize
    (core_ops_index_IndexMutSliceTIInst u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32)) x
    {| core_ops_range_Range_start := y; core_ops_range_Range_end_ := z |}
.

(** [array::array_subslice_mut_]: backward function 0 *)
Definition array_subslice_mut__back
  (x : array u32 32%usize) (y : usize) (z : usize) (ret : slice u32) :
  result (array u32 32%usize)
  :=
  core_array_Array_index_mut_back u32 (core_ops_range_Range usize) 32%usize
    (core_ops_index_IndexMutSliceTIInst u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32)) x
    {| core_ops_range_Range_start := y; core_ops_range_Range_end_ := z |} ret
.

(** [array::index_slice_0]: forward function *)
Definition index_slice_0 (T : Type) (s : slice T) : result T :=
  slice_index_usize T s 0%usize
.

(** [array::index_array_0]: forward function *)
Definition index_array_0 (T : Type) (s : array T 32%usize) : result T :=
  array_index_usize T 32%usize s 0%usize
.

(** [array::index_index_array]: forward function *)
Definition index_index_array
  (s : array (array u32 32%usize) 32%usize) (i : usize) (j : usize) :
  result u32
  :=
  a <- array_index_usize (array u32 32%usize) 32%usize s i;
  array_index_usize u32 32%usize a j
.

(** [array::update_update_array]: forward function *)
Definition update_update_array
  (s : array (array u32 32%usize) 32%usize) (i : usize) (j : usize) :
  result unit
  :=
  a <- array_index_usize (array u32 32%usize) 32%usize s i;
  a0 <- array_update_usize u32 32%usize a j 0%u32;
  _ <- array_update_usize (array u32 32%usize) 32%usize s i a0;
  Return tt
.

(** [array::array_local_deep_copy]: forward function *)
Definition array_local_deep_copy (x : array u32 32%usize) : result unit :=
  Return tt
.

(** [array::take_array]: forward function *)
Definition take_array (a : array u32 2%usize) : result unit :=
  Return tt.

(** [array::take_array_borrow]: forward function *)
Definition take_array_borrow (a : array u32 2%usize) : result unit :=
  Return tt
.

(** [array::take_slice]: forward function *)
Definition take_slice (s : slice u32) : result unit :=
  Return tt.

(** [array::take_mut_slice]: merged forward/backward function
    (there is a single backward function, and the forward function returns ()) *)
Definition take_mut_slice (s : slice u32) : result (slice u32) :=
  Return s.

(** [array::take_all]: forward function *)
Definition take_all : result unit :=
  _ <- take_array (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  _ <- take_array_borrow (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  s <- array_to_slice u32 2%usize (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  _ <- take_slice s;
  s0 <- array_to_slice u32 2%usize (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  s1 <- take_mut_slice s0;
  _ <- array_from_slice u32 2%usize (mk_array u32 2%usize [ 0%u32; 0%u32 ]) s1;
  Return tt
.

(** [array::index_array]: forward function *)
Definition index_array (x : array u32 2%usize) : result u32 :=
  array_index_usize u32 2%usize x 0%usize
.

(** [array::index_array_borrow]: forward function *)
Definition index_array_borrow (x : array u32 2%usize) : result u32 :=
  array_index_usize u32 2%usize x 0%usize
.

(** [array::index_slice_u32_0]: forward function *)
Definition index_slice_u32_0 (x : slice u32) : result u32 :=
  slice_index_usize u32 x 0%usize
.

(** [array::index_mut_slice_u32_0]: forward function *)
Definition index_mut_slice_u32_0 (x : slice u32) : result u32 :=
  slice_index_usize u32 x 0%usize
.

(** [array::index_mut_slice_u32_0]: backward function 0 *)
Definition index_mut_slice_u32_0_back (x : slice u32) : result (slice u32) :=
  _ <- slice_index_usize u32 x 0%usize; Return x
.

(** [array::index_all]: forward function *)
Definition index_all : result u32 :=
  i <- index_array (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  i0 <- index_array (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  i1 <- u32_add i i0;
  i2 <- index_array_borrow (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  i3 <- u32_add i1 i2;
  s <- array_to_slice u32 2%usize (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  i4 <- index_slice_u32_0 s;
  i5 <- u32_add i3 i4;
  s0 <- array_to_slice u32 2%usize (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  i6 <- index_mut_slice_u32_0 s0;
  i7 <- u32_add i5 i6;
  s1 <- index_mut_slice_u32_0_back s0;
  _ <- array_from_slice u32 2%usize (mk_array u32 2%usize [ 0%u32; 0%u32 ]) s1;
  Return i7
.

(** [array::update_array]: forward function *)
Definition update_array (x : array u32 2%usize) : result unit :=
  _ <- array_update_usize u32 2%usize x 0%usize 1%u32; Return tt
.

(** [array::update_array_mut_borrow]: merged forward/backward function
    (there is a single backward function, and the forward function returns ()) *)
Definition update_array_mut_borrow
  (x : array u32 2%usize) : result (array u32 2%usize) :=
  array_update_usize u32 2%usize x 0%usize 1%u32
.

(** [array::update_mut_slice]: merged forward/backward function
    (there is a single backward function, and the forward function returns ()) *)
Definition update_mut_slice (x : slice u32) : result (slice u32) :=
  slice_update_usize u32 x 0%usize 1%u32
.

(** [array::update_all]: forward function *)
Definition update_all : result unit :=
  _ <- update_array (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  x <- update_array_mut_borrow (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  s <- array_to_slice u32 2%usize x;
  s0 <- update_mut_slice s;
  _ <- array_from_slice u32 2%usize x s0;
  Return tt
.

(** [array::range_all]: forward function *)
Definition range_all : result unit :=
  s <-
    core_array_Array_index_mut u32 (core_ops_range_Range usize) 4%usize
      (core_ops_index_IndexMutSliceTIInst u32 (core_ops_range_Range usize)
      (core_slice_index_SliceIndexRangeUsizeSliceTInst u32))
      (mk_array u32 4%usize [ 0%u32; 0%u32; 0%u32; 0%u32 ])
      {|
        core_ops_range_Range_start := 1%usize;
        core_ops_range_Range_end_ := 3%usize
      |};
  s0 <- update_mut_slice s;
  _ <-
    core_array_Array_index_mut_back u32 (core_ops_range_Range usize) 4%usize
      (core_ops_index_IndexMutSliceTIInst u32 (core_ops_range_Range usize)
      (core_slice_index_SliceIndexRangeUsizeSliceTInst u32))
      (mk_array u32 4%usize [ 0%u32; 0%u32; 0%u32; 0%u32 ])
      {|
        core_ops_range_Range_start := 1%usize;
        core_ops_range_Range_end_ := 3%usize
      |} s0;
  Return tt
.

(** [array::deref_array_borrow]: forward function *)
Definition deref_array_borrow (x : array u32 2%usize) : result u32 :=
  array_index_usize u32 2%usize x 0%usize
.

(** [array::deref_array_mut_borrow]: forward function *)
Definition deref_array_mut_borrow (x : array u32 2%usize) : result u32 :=
  array_index_usize u32 2%usize x 0%usize
.

(** [array::deref_array_mut_borrow]: backward function 0 *)
Definition deref_array_mut_borrow_back
  (x : array u32 2%usize) : result (array u32 2%usize) :=
  _ <- array_index_usize u32 2%usize x 0%usize; Return x
.

(** [array::take_array_t]: forward function *)
Definition take_array_t (a : array AB_t 2%usize) : result unit :=
  Return tt.

(** [array::non_copyable_array]: forward function *)
Definition non_copyable_array : result unit :=
  _ <- take_array_t (mk_array AB_t 2%usize [ AB_A; AB_B ]); Return tt
.

(** [array::sum]: loop 0: forward function *)
Fixpoint sum_loop
  (n : nat) (s : slice u32) (sum0 : u32) (i : usize) : result u32 :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    let i0 := slice_len u32 s in
    if i s< i0
    then (
      i1 <- slice_index_usize u32 s i;
      sum1 <- u32_add sum0 i1;
      i2 <- usize_add i 1%usize;
      sum_loop n0 s sum1 i2)
    else Return sum0
  end
.

(** [array::sum]: forward function *)
Definition sum (n : nat) (s : slice u32) : result u32 :=
  sum_loop n s 0%u32 0%usize
.

(** [array::sum2]: loop 0: forward function *)
Fixpoint sum2_loop
  (n : nat) (s : slice u32) (s2 : slice u32) (sum0 : u32) (i : usize) :
  result u32
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    let i0 := slice_len u32 s in
    if i s< i0
    then (
      i1 <- slice_index_usize u32 s i;
      i2 <- slice_index_usize u32 s2 i;
      i3 <- u32_add i1 i2;
      sum1 <- u32_add sum0 i3;
      i4 <- usize_add i 1%usize;
      sum2_loop n0 s s2 sum1 i4)
    else Return sum0
  end
.

(** [array::sum2]: forward function *)
Definition sum2 (n : nat) (s : slice u32) (s2 : slice u32) : result u32 :=
  let i := slice_len u32 s in
  let i0 := slice_len u32 s2 in
  if negb (i s= i0) then Fail_ Failure else sum2_loop n s s2 0%u32 0%usize
.

(** [array::f0]: forward function *)
Definition f0 : result unit :=
  s <- array_to_slice u32 2%usize (mk_array u32 2%usize [ 1%u32; 2%u32 ]);
  s0 <- slice_update_usize u32 s 0%usize 1%u32;
  _ <- array_from_slice u32 2%usize (mk_array u32 2%usize [ 1%u32; 2%u32 ]) s0;
  Return tt
.

(** [array::f1]: forward function *)
Definition f1 : result unit :=
  _ <-
    array_update_usize u32 2%usize (mk_array u32 2%usize [ 1%u32; 2%u32 ])
      0%usize 1%u32;
  Return tt
.

(** [array::f2]: forward function *)
Definition f2 (i : u32) : result unit :=
  Return tt.

(** [array::f4]: forward function *)
Definition f4
  (x : array u32 32%usize) (y : usize) (z : usize) : result (slice u32) :=
  core_array_Array_index u32 (core_ops_range_Range usize) 32%usize
    (core_ops_index_IndexSliceTIInst u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32)) x
    {| core_ops_range_Range_start := y; core_ops_range_Range_end_ := z |}
.

(** [array::f3]: forward function *)
Definition f3 (n : nat) : result u32 :=
  i <-
    array_index_usize u32 2%usize (mk_array u32 2%usize [ 1%u32; 2%u32 ])
      0%usize;
  _ <- f2 i;
  let b := array_repeat u32 32%usize 0%u32 in
  s <- array_to_slice u32 2%usize (mk_array u32 2%usize [ 1%u32; 2%u32 ]);
  s0 <- f4 b 16%usize 18%usize;
  sum2 n s s0
.

(** [array::SZ] *)
Definition sz_body : result usize := Return 32%usize.
Definition sz_c : usize := sz_body%global.

(** [array::f5]: forward function *)
Definition f5 (x : array u32 32%usize) : result u32 :=
  array_index_usize u32 32%usize x 0%usize
.

(** [array::ite]: forward function *)
Definition ite : result unit :=
  s <- array_to_slice u32 2%usize (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  s0 <- array_to_slice u32 2%usize (mk_array u32 2%usize [ 0%u32; 0%u32 ]);
  s1 <- index_mut_slice_u32_0_back s0;
  _ <- array_from_slice u32 2%usize (mk_array u32 2%usize [ 0%u32; 0%u32 ]) s1;
  s2 <- index_mut_slice_u32_0_back s;
  _ <- array_from_slice u32 2%usize (mk_array u32 2%usize [ 0%u32; 0%u32 ]) s2;
  Return tt
.

End Array .
