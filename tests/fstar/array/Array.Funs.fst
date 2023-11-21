(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [array]: function definitions *)
module Array.Funs
open Primitives
include Array.Types
include Array.Clauses

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [array::incr]: merged forward/backward function
    (there is a single backward function, and the forward function returns ()) *)
let incr (x : u32) : result u32 =
  u32_add x 1

(** [array::array_to_shared_slice_]: forward function *)
let array_to_shared_slice_ (t : Type0) (s : array t 32) : result (slice t) =
  array_to_slice t 32 s

(** [array::array_to_mut_slice_]: forward function *)
let array_to_mut_slice_ (t : Type0) (s : array t 32) : result (slice t) =
  array_to_slice t 32 s

(** [array::array_to_mut_slice_]: backward function 0 *)
let array_to_mut_slice__back
  (t : Type0) (s : array t 32) (ret : slice t) : result (array t 32) =
  array_from_slice t 32 s ret

(** [array::array_len]: forward function *)
let array_len (t : Type0) (s : array t 32) : result usize =
  let* s0 = array_to_slice t 32 s in let i = slice_len t s0 in Return i

(** [array::shared_array_len]: forward function *)
let shared_array_len (t : Type0) (s : array t 32) : result usize =
  let* s0 = array_to_slice t 32 s in let i = slice_len t s0 in Return i

(** [array::shared_slice_len]: forward function *)
let shared_slice_len (t : Type0) (s : slice t) : result usize =
  let i = slice_len t s in Return i

(** [array::index_array_shared]: forward function *)
let index_array_shared (t : Type0) (s : array t 32) (i : usize) : result t =
  array_index_usize t 32 s i

(** [array::index_array_u32]: forward function *)
let index_array_u32 (s : array u32 32) (i : usize) : result u32 =
  array_index_usize u32 32 s i

(** [array::index_array_copy]: forward function *)
let index_array_copy (x : array u32 32) : result u32 =
  array_index_usize u32 32 x 0

(** [array::index_mut_array]: forward function *)
let index_mut_array (t : Type0) (s : array t 32) (i : usize) : result t =
  array_index_usize t 32 s i

(** [array::index_mut_array]: backward function 0 *)
let index_mut_array_back
  (t : Type0) (s : array t 32) (i : usize) (ret : t) : result (array t 32) =
  array_update_usize t 32 s i ret

(** [array::index_slice]: forward function *)
let index_slice (t : Type0) (s : slice t) (i : usize) : result t =
  slice_index_usize t s i

(** [array::index_mut_slice]: forward function *)
let index_mut_slice (t : Type0) (s : slice t) (i : usize) : result t =
  slice_index_usize t s i

(** [array::index_mut_slice]: backward function 0 *)
let index_mut_slice_back
  (t : Type0) (s : slice t) (i : usize) (ret : t) : result (slice t) =
  slice_update_usize t s i ret

(** [array::slice_subslice_shared_]: forward function *)
let slice_subslice_shared_
  (x : slice u32) (y : usize) (z : usize) : result (slice u32) =
  core_slice_index_Slice_index u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32) x
    { start = y; end_ = z }

(** [array::slice_subslice_mut_]: forward function *)
let slice_subslice_mut_
  (x : slice u32) (y : usize) (z : usize) : result (slice u32) =
  core_slice_index_Slice_index_mut u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32) x
    { start = y; end_ = z }

(** [array::slice_subslice_mut_]: backward function 0 *)
let slice_subslice_mut__back
  (x : slice u32) (y : usize) (z : usize) (ret : slice u32) :
  result (slice u32)
  =
  core_slice_index_Slice_index_mut_back u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32) x
    { start = y; end_ = z } ret

(** [array::array_to_slice_shared_]: forward function *)
let array_to_slice_shared_ (x : array u32 32) : result (slice u32) =
  array_to_slice u32 32 x

(** [array::array_to_slice_mut_]: forward function *)
let array_to_slice_mut_ (x : array u32 32) : result (slice u32) =
  array_to_slice u32 32 x

(** [array::array_to_slice_mut_]: backward function 0 *)
let array_to_slice_mut__back
  (x : array u32 32) (ret : slice u32) : result (array u32 32) =
  array_from_slice u32 32 x ret

(** [array::array_subslice_shared_]: forward function *)
let array_subslice_shared_
  (x : array u32 32) (y : usize) (z : usize) : result (slice u32) =
  core_array_Array_index u32 (core_ops_range_Range usize) 32
    (core_ops_index_IndexSliceTIInst u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32)) x
    { start = y; end_ = z }

(** [array::array_subslice_mut_]: forward function *)
let array_subslice_mut_
  (x : array u32 32) (y : usize) (z : usize) : result (slice u32) =
  core_array_Array_index_mut u32 (core_ops_range_Range usize) 32
    (core_ops_index_IndexMutSliceTIInst u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32)) x
    { start = y; end_ = z }

(** [array::array_subslice_mut_]: backward function 0 *)
let array_subslice_mut__back
  (x : array u32 32) (y : usize) (z : usize) (ret : slice u32) :
  result (array u32 32)
  =
  core_array_Array_index_mut_back u32 (core_ops_range_Range usize) 32
    (core_ops_index_IndexMutSliceTIInst u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32)) x
    { start = y; end_ = z } ret

(** [array::index_slice_0]: forward function *)
let index_slice_0 (t : Type0) (s : slice t) : result t =
  slice_index_usize t s 0

(** [array::index_array_0]: forward function *)
let index_array_0 (t : Type0) (s : array t 32) : result t =
  array_index_usize t 32 s 0

(** [array::index_index_array]: forward function *)
let index_index_array
  (s : array (array u32 32) 32) (i : usize) (j : usize) : result u32 =
  let* a = array_index_usize (array u32 32) 32 s i in
  array_index_usize u32 32 a j

(** [array::update_update_array]: forward function *)
let update_update_array
  (s : array (array u32 32) 32) (i : usize) (j : usize) : result unit =
  let* a = array_index_usize (array u32 32) 32 s i in
  let* a0 = array_update_usize u32 32 a j 0 in
  let* _ = array_update_usize (array u32 32) 32 s i a0 in
  Return ()

(** [array::array_local_deep_copy]: forward function *)
let array_local_deep_copy (x : array u32 32) : result unit =
  Return ()

(** [array::take_array]: forward function *)
let take_array (a : array u32 2) : result unit =
  Return ()

(** [array::take_array_borrow]: forward function *)
let take_array_borrow (a : array u32 2) : result unit =
  Return ()

(** [array::take_slice]: forward function *)
let take_slice (s : slice u32) : result unit =
  Return ()

(** [array::take_mut_slice]: merged forward/backward function
    (there is a single backward function, and the forward function returns ()) *)
let take_mut_slice (s : slice u32) : result (slice u32) =
  Return s

(** [array::take_all]: forward function *)
let take_all : result unit =
  let* _ = take_array (mk_array u32 2 [ 0; 0 ]) in
  let* _ = take_array_borrow (mk_array u32 2 [ 0; 0 ]) in
  let* s = array_to_slice u32 2 (mk_array u32 2 [ 0; 0 ]) in
  let* _ = take_slice s in
  let* s0 = array_to_slice u32 2 (mk_array u32 2 [ 0; 0 ]) in
  let* s1 = take_mut_slice s0 in
  let* _ = array_from_slice u32 2 (mk_array u32 2 [ 0; 0 ]) s1 in
  Return ()

(** [array::index_array]: forward function *)
let index_array (x : array u32 2) : result u32 =
  array_index_usize u32 2 x 0

(** [array::index_array_borrow]: forward function *)
let index_array_borrow (x : array u32 2) : result u32 =
  array_index_usize u32 2 x 0

(** [array::index_slice_u32_0]: forward function *)
let index_slice_u32_0 (x : slice u32) : result u32 =
  slice_index_usize u32 x 0

(** [array::index_mut_slice_u32_0]: forward function *)
let index_mut_slice_u32_0 (x : slice u32) : result u32 =
  slice_index_usize u32 x 0

(** [array::index_mut_slice_u32_0]: backward function 0 *)
let index_mut_slice_u32_0_back (x : slice u32) : result (slice u32) =
  let* _ = slice_index_usize u32 x 0 in Return x

(** [array::index_all]: forward function *)
let index_all : result u32 =
  let* i = index_array (mk_array u32 2 [ 0; 0 ]) in
  let* i0 = index_array (mk_array u32 2 [ 0; 0 ]) in
  let* i1 = u32_add i i0 in
  let* i2 = index_array_borrow (mk_array u32 2 [ 0; 0 ]) in
  let* i3 = u32_add i1 i2 in
  let* s = array_to_slice u32 2 (mk_array u32 2 [ 0; 0 ]) in
  let* i4 = index_slice_u32_0 s in
  let* i5 = u32_add i3 i4 in
  let* s0 = array_to_slice u32 2 (mk_array u32 2 [ 0; 0 ]) in
  let* i6 = index_mut_slice_u32_0 s0 in
  let* i7 = u32_add i5 i6 in
  let* s1 = index_mut_slice_u32_0_back s0 in
  let* _ = array_from_slice u32 2 (mk_array u32 2 [ 0; 0 ]) s1 in
  Return i7

(** [array::update_array]: forward function *)
let update_array (x : array u32 2) : result unit =
  let* _ = array_update_usize u32 2 x 0 1 in Return ()

(** [array::update_array_mut_borrow]: merged forward/backward function
    (there is a single backward function, and the forward function returns ()) *)
let update_array_mut_borrow (x : array u32 2) : result (array u32 2) =
  array_update_usize u32 2 x 0 1

(** [array::update_mut_slice]: merged forward/backward function
    (there is a single backward function, and the forward function returns ()) *)
let update_mut_slice (x : slice u32) : result (slice u32) =
  slice_update_usize u32 x 0 1

(** [array::update_all]: forward function *)
let update_all : result unit =
  let* _ = update_array (mk_array u32 2 [ 0; 0 ]) in
  let* x = update_array_mut_borrow (mk_array u32 2 [ 0; 0 ]) in
  let* s = array_to_slice u32 2 x in
  let* s0 = update_mut_slice s in
  let* _ = array_from_slice u32 2 x s0 in
  Return ()

(** [array::range_all]: forward function *)
let range_all : result unit =
  let* s =
    core_array_Array_index_mut u32 (core_ops_range_Range usize) 4
      (core_ops_index_IndexMutSliceTIInst u32 (core_ops_range_Range usize)
      (core_slice_index_SliceIndexRangeUsizeSliceTInst u32))
      (mk_array u32 4 [ 0; 0; 0; 0 ]) { start = 1; end_ = 3 } in
  let* s0 = update_mut_slice s in
  let* _ =
    core_array_Array_index_mut_back u32 (core_ops_range_Range usize) 4
      (core_ops_index_IndexMutSliceTIInst u32 (core_ops_range_Range usize)
      (core_slice_index_SliceIndexRangeUsizeSliceTInst u32))
      (mk_array u32 4 [ 0; 0; 0; 0 ]) { start = 1; end_ = 3 } s0 in
  Return ()

(** [array::deref_array_borrow]: forward function *)
let deref_array_borrow (x : array u32 2) : result u32 =
  array_index_usize u32 2 x 0

(** [array::deref_array_mut_borrow]: forward function *)
let deref_array_mut_borrow (x : array u32 2) : result u32 =
  array_index_usize u32 2 x 0

(** [array::deref_array_mut_borrow]: backward function 0 *)
let deref_array_mut_borrow_back (x : array u32 2) : result (array u32 2) =
  let* _ = array_index_usize u32 2 x 0 in Return x

(** [array::take_array_t]: forward function *)
let take_array_t (a : array aB_t 2) : result unit =
  Return ()

(** [array::non_copyable_array]: forward function *)
let non_copyable_array : result unit =
  let* _ = take_array_t (mk_array aB_t 2 [ AB_A; AB_B ]) in Return ()

(** [array::sum]: loop 0: forward function *)
let rec sum_loop
  (s : slice u32) (sum0 : u32) (i : usize) :
  Tot (result u32) (decreases (sum_loop_decreases s sum0 i))
  =
  let i0 = slice_len u32 s in
  if i < i0
  then
    let* i1 = slice_index_usize u32 s i in
    let* sum1 = u32_add sum0 i1 in
    let* i2 = usize_add i 1 in
    sum_loop s sum1 i2
  else Return sum0

(** [array::sum]: forward function *)
let sum (s : slice u32) : result u32 =
  sum_loop s 0 0

(** [array::sum2]: loop 0: forward function *)
let rec sum2_loop
  (s : slice u32) (s2 : slice u32) (sum0 : u32) (i : usize) :
  Tot (result u32) (decreases (sum2_loop_decreases s s2 sum0 i))
  =
  let i0 = slice_len u32 s in
  if i < i0
  then
    let* i1 = slice_index_usize u32 s i in
    let* i2 = slice_index_usize u32 s2 i in
    let* i3 = u32_add i1 i2 in
    let* sum1 = u32_add sum0 i3 in
    let* i4 = usize_add i 1 in
    sum2_loop s s2 sum1 i4
  else Return sum0

(** [array::sum2]: forward function *)
let sum2 (s : slice u32) (s2 : slice u32) : result u32 =
  let i = slice_len u32 s in
  let i0 = slice_len u32 s2 in
  if not (i = i0) then Fail Failure else sum2_loop s s2 0 0

(** [array::f0]: forward function *)
let f0 : result unit =
  let* s = array_to_slice u32 2 (mk_array u32 2 [ 1; 2 ]) in
  let* s0 = slice_update_usize u32 s 0 1 in
  let* _ = array_from_slice u32 2 (mk_array u32 2 [ 1; 2 ]) s0 in
  Return ()

(** [array::f1]: forward function *)
let f1 : result unit =
  let* _ = array_update_usize u32 2 (mk_array u32 2 [ 1; 2 ]) 0 1 in Return ()

(** [array::f2]: forward function *)
let f2 (i : u32) : result unit =
  Return ()

(** [array::f4]: forward function *)
let f4 (x : array u32 32) (y : usize) (z : usize) : result (slice u32) =
  core_array_Array_index u32 (core_ops_range_Range usize) 32
    (core_ops_index_IndexSliceTIInst u32 (core_ops_range_Range usize)
    (core_slice_index_SliceIndexRangeUsizeSliceTInst u32)) x
    { start = y; end_ = z }

(** [array::f3]: forward function *)
let f3 : result u32 =
  let* i = array_index_usize u32 2 (mk_array u32 2 [ 1; 2 ]) 0 in
  let* _ = f2 i in
  let b = array_repeat u32 32 0 in
  let* s = array_to_slice u32 2 (mk_array u32 2 [ 1; 2 ]) in
  let* s0 = f4 b 16 18 in
  sum2 s s0

(** [array::SZ] *)
let sz_body : result usize = Return 32
let sz_c : usize = eval_global sz_body

(** [array::f5]: forward function *)
let f5 (x : array u32 32) : result u32 =
  array_index_usize u32 32 x 0

(** [array::ite]: forward function *)
let ite : result unit =
  let* s = array_to_slice u32 2 (mk_array u32 2 [ 0; 0 ]) in
  let* s0 = array_to_slice u32 2 (mk_array u32 2 [ 0; 0 ]) in
  let* s1 = index_mut_slice_u32_0_back s0 in
  let* _ = array_from_slice u32 2 (mk_array u32 2 [ 0; 0 ]) s1 in
  let* s2 = index_mut_slice_u32_0_back s in
  let* _ = array_from_slice u32 2 (mk_array u32 2 [ 0; 0 ]) s2 in
  Return ()

