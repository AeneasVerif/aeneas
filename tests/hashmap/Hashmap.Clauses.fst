(** [hashmap]: the decreases clauses *)
module Hashmap.Clauses
open Primitives
open FStar.List.Tot
open Hashmap.Types

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(** [hashmap::HashMap::allocate_slots]: decreases clause *)
unfold
let hash_map_allocate_slots_decreases (t : Type0) (slots : vec (list_t t))
  (n : usize) : nat = n

(** [hashmap::HashMap::clear_slots]: decreases clause *)
unfold
let hash_map_clear_slots_decreases (t : Type0) (slots : vec (list_t t))
  (i : usize) : nat =
  if i < length slots then length slots - i else 0

(** [hashmap::HashMap::insert_in_list]: decreases clause *)
unfold
let hash_map_insert_in_list_decreases (t : Type0) (key : usize) (value : t)
  (ls : list_t t) : list_t t =
  ls

(** [hashmap::HashMap::move_elements_from_list]: decreases clause *)
unfold
let hash_map_move_elements_from_list_decreases (t : Type0)
  (ntable : hash_map_t t) (ls : list_t t) : list_t t =
  ls

(** [hashmap::HashMap::move_elements]: decreases clause *)
unfold
let hash_map_move_elements_decreases (t : Type0) (ntable : hash_map_t t)
  (slots : vec (list_t t)) (i : usize) : nat =
  if i < length slots then length slots - i else 0

(** [hashmap::HashMap::contains_key_in_list]: decreases clause *)
unfold
let hash_map_contains_key_in_list_decreases (t : Type0) (key : usize)
  (ls : list_t t) : list_t t =
  ls

(** [hashmap::HashMap::get_in_list]: decreases clause *)
unfold
let hash_map_get_in_list_decreases (t : Type0) (key : usize) (ls : list_t t) :
  list_t t =
  ls

(** [hashmap::HashMap::get_mut_in_list]: decreases clause *)
unfold
let hash_map_get_mut_in_list_decreases (t : Type0) (key : usize)
  (ls : list_t t) : list_t t =
  ls

(** [hashmap::HashMap::remove_from_list]: decreases clause *)
unfold
let hash_map_remove_from_list_decreases (t : Type0) (key : usize)
  (ls : list_t t) : list_t t =
  ls

