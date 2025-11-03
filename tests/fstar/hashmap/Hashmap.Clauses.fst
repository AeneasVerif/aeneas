(** [hashmap]: the decreases clauses *)
module Hashmap.Clauses
open Primitives
open FStar.List.Tot
open Hashmap.Types

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(** [hashmap::HashMap::allocate_slots]: decreases clause *)
unfold
let hashMap_allocate_slots_loop_decreases (#t : Type0)
  (slots : alloc_vec_Vec (aList_t t)) (n : usize) : nat = n

(** [hashmap::HashMap::clear]: decreases clause *)
unfold
let hashMap_clear_loop_decreases (#t : Type0) (slots : alloc_vec_Vec (aList_t t))
  (i : usize) : nat =
  if i < length slots then length slots - i else 0

(** [hashmap::HashMap::insert_in_list]: decreases clause *)
unfold
let hashMap_insert_in_list_loop_decreases (#t : Type0) (key : usize) (value : t)
  (ls : aList_t t) : aList_t t =
  ls

(** [hashmap::HashMap::move_elements_from_list]: decreases clause *)
unfold
let hashMap_move_elements_from_list_loop_decreases (#t : Type0)
  (ntable : hashMap_t t) (ls : aList_t t) : aList_t t =
  ls

(** [hashmap::HashMap::move_elements]: decreases clause *)
unfold
let hashMap_move_elements_loop_decreases (#t : Type0) (ntable : hashMap_t t)
  (slots : alloc_vec_Vec (aList_t t)) (i : usize) : nat =
  if i < length slots then length slots - i else 0

(** [hashmap::HashMap::contains_key_in_list]: decreases clause *)
unfold
let hashMap_contains_key_in_list_loop_decreases (#t : Type0) (key : usize)
  (ls : aList_t t) : aList_t t =
  ls

(** [hashmap::HashMap::get_in_list]: decreases clause *)
unfold
let hashMap_get_in_list_loop_decreases (#t : Type0) (key : usize) (ls : aList_t t) :
  aList_t t =
  ls

(** [hashmap::HashMap::get_mut_in_list]: decreases clause *)
unfold
let hashMap_get_mut_in_list_loop_decreases (#t : Type0) (ls : aList_t t)
  (key : usize) : aList_t t =
  ls

(** [hashmap::HashMap::remove_from_list]: decreases clause *)
unfold
let hashMap_remove_from_list_loop_decreases (#t : Type0) (key : usize)
  (ls : aList_t t) : aList_t t =
  ls