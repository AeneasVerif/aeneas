(** [loops]: templates for the decreases clauses *)
module Loops.Clauses
open Primitives
open Loops.Types

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [loops::sum]: decreases clause *)
unfold let sum_decreases (max : u32) (i : u32) (s : u32) : nat =
  if i <= max then max - i else 0

(** [loops::sum_with_mut_borrows]: decreases clause *)
unfold
let sum_with_mut_borrows_decreases (max : u32) (mi : u32) (ms : u32) : nat =
  if max >= mi then max - mi else 0

(** [loops::sum_with_shared_borrows]: decreases clause *)
unfold
let sum_with_shared_borrows_decreases (max : u32) (i : u32) (s : u32) : nat =
  if max >= i then max - i else 0

(** [loops::clear]: decreases clause *)
unfold let clear_decreases (v : vec u32) (i : usize) : nat =
  if i <= List.Tot.length v then List.Tot.length v - i else 0

(** [loops::list_mem]: decreases clause *)
unfold let list_mem_decreases (i : u32) (ls : list_t u32) : list_t u32 =
  ls

(** [loops::list_nth_mut_loop]: decreases clause *)
unfold
let list_nth_mut_loop_decreases (t : Type0) (ls : list_t t) (i : u32) : nat =
  i

(** [loops::list_nth_shared_loop]: decreases clause *)
unfold
let list_nth_shared_loop_decreases (t : Type0) (ls : list_t t) (i : u32) : list_t t =
  ls

(** [loops::get_elem_mut]: decreases clause *)
unfold
let get_elem_mut_decreases (x : usize) (ls : list_t usize) : list_t usize = ls

(** [loops::get_elem_shared]: decreases clause *)
unfold
let get_elem_shared_decreases (x : usize) (v : vec (list_t usize))
  (l : list_t usize) (ls : list_t usize) : list_t usize =
  ls

(** [loops::list_nth_mut_loop_with_id]: decreases clause *)
unfold
let list_nth_mut_loop_with_id_decreases (t : Type0) (i : u32) (ls : list_t t) :
  list_t t =
  ls

(** [loops::list_nth_shared_loop_with_id]: decreases clause *)
unfold
let list_nth_shared_loop_with_id_decreases (t : Type0) (l : list_t t)
  (i : u32) (ls : list_t t) : list_t t =
  ls

(** [loops::list_nth_mut_loop_pair]: decreases clause *)
unfold
let list_nth_mut_loop_pair_decreases (t : Type0) (l : list_t t) (l0 : list_t t)
  (i : u32) : nat =
  i

(** [loops::list_nth_shared_loop_pair]: decreases clause *)
unfold
let list_nth_shared_loop_pair_decreases (t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : list_t t =
  l

(** [loops::list_nth_mut_loop_pair_merge]: decreases clause *)
unfold
let list_nth_mut_loop_pair_merge_decreases (t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : nat =
  i

(** [loops::list_nth_shared_loop_pair_merge]: decreases clause *)
unfold
let list_nth_shared_loop_pair_merge_decreases (t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : list_t t =
  l

(** [loops::list_nth_mut_shared_loop_pair]: decreases clause *)
unfold
let list_nth_mut_shared_loop_pair_decreases (t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : list_t t =
  l

(** [loops::list_nth_mut_shared_loop_pair_merge]: decreases clause *)
unfold
let list_nth_mut_shared_loop_pair_merge_decreases (t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : list_t t =
  l

(** [loops::list_nth_shared_mut_loop_pair]: decreases clause *)
unfold
let list_nth_shared_mut_loop_pair_decreases (t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : list_t t =
  l

(** [loops::list_nth_shared_mut_loop_pair_merge]: decreases clause *)
unfold
let list_nth_shared_mut_loop_pair_merge_decreases (t : Type0) (l : list_t t)
  (l0 : list_t t) (i : u32) : list_t t =
  l
