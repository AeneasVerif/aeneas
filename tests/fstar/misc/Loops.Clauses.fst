(** [loops]: templates for the decreases clauses *)
module Loops.Clauses
open Primitives
open Loops.Types

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [loops::sum]: decreases clause *)
unfold let sum_loop_decreases (max : u32) (i : u32) (s : u32) : nat =
  if i <= max then max - i else 0

(** [loops::sum_with_mut_borrows]: decreases clause *)
unfold
let sum_with_mut_borrows_loop_decreases (max : u32) (mi : u32) (ms : u32) : nat =
  if max >= mi then max - mi else 0

(** [loops::sum_with_shared_borrows]: decreases clause *)
unfold
let sum_with_shared_borrows_loop_decreases (max : u32) (i : u32) (s : u32) : nat =
  if max >= i then max - i else 0

(** [loops::sum_array]: decreases clause *)
unfold
let sum_array_loop_decreases (#n : usize) (_ : array u32 n) (i : usize) (_ : u32) : nat =
  if n >= i then n - i else 0

(** [loops::clear]: decreases clause *)
unfold let clear_loop_decreases (v : alloc_vec_Vec u32) (i : usize) : nat =
  if i <= List.Tot.length v then List.Tot.length v - i else 0

(** [loops::list_mem]: decreases clause *)
unfold let list_mem_loop_decreases (i : u32) (ls : list_t u32) : list_t u32 =
  ls

(** [loops::list_nth_mut_loop]: decreases clause *)
unfold
let list_nth_mut_loop_loop_decreases (#t : Type0) (ls : list_t t) (i : u32) : nat =
  i

(** [loops::list_nth_shared_loop]: decreases clause *)
unfold
let list_nth_shared_loop_loop_decreases (#t : Type0) (ls : list_t t) (i : u32) : list_t t =
  ls

(** [loops::get_elem_mut]: decreases clause *)
unfold
let get_elem_mut_loop_decreases (x : usize) (ls : list_t usize) : list_t usize = ls

(** [loops::get_elem_shared]: decreases clause *)
unfold
let get_elem_shared_loop_decreases (x : usize) (ls : list_t usize) : list_t usize =
  ls

(** [loops::list_nth_mut_loop_with_id]: decreases clause *)
unfold
let list_nth_mut_loop_with_id_loop_decreases (#t : Type0) (i : u32) (ls : list_t t) :
  list_t t =
  ls

(** [loops::list_nth_shared_loop_with_id]: decreases clause *)
unfold
let list_nth_shared_loop_with_id_loop_decreases (#t : Type0) (i : u32)
  (ls : list_t t) : list_t t =
  ls

(** [loops::list_nth_mut_loop_pair]: decreases clause *)
unfold
let list_nth_mut_loop_pair_loop_decreases (#t : Type0) (l : list_t t) (l0 : list_t t)
  (i : u32) : nat =
  i

(** [loops::list_nth_shared_loop_pair]: decreases clause *)
unfold
let list_nth_shared_loop_pair_loop_decreases (#t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : list_t t =
  l

(** [loops::list_nth_mut_loop_pair_merge]: decreases clause *)
unfold
let list_nth_mut_loop_pair_merge_loop_decreases (#t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : nat =
  i

(** [loops::list_nth_shared_loop_pair_merge]: decreases clause *)
unfold
let list_nth_shared_loop_pair_merge_loop_decreases (#t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : list_t t =
  l

(** [loops::list_nth_mut_shared_loop_pair]: decreases clause *)
unfold
let list_nth_mut_shared_loop_pair_loop_decreases (#t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : list_t t =
  l

(** [loops::list_nth_mut_shared_loop_pair_merge]: decreases clause *)
unfold
let list_nth_mut_shared_loop_pair_merge_loop_decreases (#t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : list_t t =
  l

(** [loops::list_nth_shared_mut_loop_pair]: decreases clause *)
unfold
let list_nth_shared_mut_loop_pair_loop_decreases (#t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : list_t t =
  l

(** [loops::list_nth_shared_mut_loop_pair_merge]: decreases clause *)
unfold
let list_nth_shared_mut_loop_pair_merge_loop_decreases (#t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : list_t t =
  l

(** [loops::ignore_input_mut_borrow]: decreases clause
    Source: 'src/loops.rs', lines 345:0-349:1 *)
unfold let ignore_input_mut_borrow_loop_decreases (i : u32) : nat = i

(** [loops::incr_ignore_input_mut_borrow]: decreases clause
    Source: 'src/loops.rs', lines 353:0-358:1 *)
unfold
let incr_ignore_input_mut_borrow_loop_decreases (i : u32) : nat = i

(** [loops::ignore_input_shared_borrow]: decreases clause
    Source: 'src/loops.rs', lines 362:0-366:1 *)
unfold let ignore_input_shared_borrow_loop_decreases (i : u32) : nat = i

