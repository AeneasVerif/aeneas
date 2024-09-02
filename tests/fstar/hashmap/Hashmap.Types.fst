(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [hashmap]: type definitions *)
module Hashmap.Types
open Primitives
include Hashmap.TypesExternal

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [hashmap::AList]
    Source: 'tests/src/hashmap.rs', lines 30:0-33:1 *)
type aList_t (t : Type0) =
| AList_Cons : usize -> t -> aList_t t -> aList_t t
| AList_Nil : aList_t t

(** [hashmap::HashMap]
    Source: 'tests/src/hashmap.rs', lines 46:0-58:1 *)
type hashMap_t (t : Type0) =
{
  num_entries : usize;
  max_load_factor : (usize & usize);
  max_load : usize;
  saturated : bool;
  slots : alloc_vec_Vec (aList_t t);
}

