(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [hashmap_main]: type definitions *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import HashmapMain_TypesExternal.
Include HashmapMain_TypesExternal.
Module HashmapMain_Types.

(** [hashmap_main::hashmap::List]
    Source: 'src/hashmap.rs', lines 19:0-19:16 *)
Inductive hashmap_List_t (T : Type) :=
| Hashmap_List_Cons : usize -> T -> hashmap_List_t T -> hashmap_List_t T
| Hashmap_List_Nil : hashmap_List_t T
.

Arguments Hashmap_List_Cons { _ }.
Arguments Hashmap_List_Nil { _ }.

(** [hashmap_main::hashmap::HashMap]
    Source: 'src/hashmap.rs', lines 35:0-35:21 *)
Record hashmap_HashMap_t (T : Type) :=
mkhashmap_HashMap_t {
  hashmap_HashMap_num_entries : usize;
  hashmap_HashMap_max_load_factor : (usize * usize);
  hashmap_HashMap_max_load : usize;
  hashmap_HashMap_slots : alloc_vec_Vec (hashmap_List_t T);
}
.

Arguments mkhashmap_HashMap_t { _ }.
Arguments hashmap_HashMap_num_entries { _ }.
Arguments hashmap_HashMap_max_load_factor { _ }.
Arguments hashmap_HashMap_max_load { _ }.
Arguments hashmap_HashMap_slots { _ }.

End HashmapMain_Types.
