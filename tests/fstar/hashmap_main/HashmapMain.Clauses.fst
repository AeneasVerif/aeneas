(** [hashmap]: the decreases clauses *)
module HashmapMain.Clauses
open Primitives
open FStar.List.Tot
open HashmapMain.Types

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(** [hashmap::HashMap::allocate_slots]: decreases clause *)
unfold
let hashmap_HashMap_allocate_slots_loop_decreases (t : Type0) (slots : alloc_vec_Vec (hashmap_List_t t))
  (n : usize) : nat = n

(** [hashmap::HashMap::clear]: decreases clause *)
unfold
let hashmap_HashMap_clear_loop_decreases (t : Type0) (slots : alloc_vec_Vec (hashmap_List_t t))
  (i : usize) : nat =
  if i < length slots then length slots - i else 0

(** [hashmap::HashMap::insert_in_list]: decreases clause *)
unfold
let hashmap_HashMap_insert_in_list_loop_decreases (t : Type0) (key : usize) (value : t)
  (ls : hashmap_List_t t) : hashmap_List_t t =
  ls

(** [hashmap::HashMap::move_elements_from_list]: decreases clause *)
unfold
let hashmap_HashMap_move_elements_from_list_loop_decreases (t : Type0)
  (ntable : hashmap_HashMap_t t) (ls : hashmap_List_t t) : hashmap_List_t t =
  ls

(** [hashmap::HashMap::move_elements]: decreases clause *)
unfold
let hashmap_HashMap_move_elements_loop_decreases (t : Type0) (ntable : hashmap_HashMap_t t)
  (slots : alloc_vec_Vec (hashmap_List_t t)) (i : usize) : nat =
  if i < length slots then length slots - i else 0

(** [hashmap::HashMap::contains_key_in_list]: decreases clause *)
unfold
let hashmap_HashMap_contains_key_in_list_loop_decreases (t : Type0) (key : usize)
  (ls : hashmap_List_t t) : hashmap_List_t t =
  ls

(** [hashmap::HashMap::get_in_list]: decreases clause *)
unfold
let hashmap_HashMap_get_in_list_loop_decreases (t : Type0) (key : usize) (ls : hashmap_List_t t) :
  hashmap_List_t t =
  ls

(** [hashmap::HashMap::get_mut_in_list]: decreases clause *)
unfold
let hashmap_HashMap_get_mut_in_list_loop_decreases (t : Type0)
  (ls : hashmap_List_t t) (key : usize) : hashmap_List_t t =
  ls

(** [hashmap::HashMap::remove_from_list]: decreases clause *)
unfold
let hashmap_HashMap_remove_from_list_loop_decreases (t : Type0) (key : usize)
  (ls : hashmap_List_t t) : hashmap_List_t t =
  ls

