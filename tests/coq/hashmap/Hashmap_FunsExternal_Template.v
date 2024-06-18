(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [hashmap]: external functions.
-- This is a template file: rename it to "FunsExternal.lean" and fill the holes. *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Hashmap_Types.
Include Hashmap_Types.
Module Hashmap_FunsExternal_Template.

(** [hashmap::utils::deserialize]:
    Source: 'tests/src/hashmap.rs', lines 331:4-331:47 *)
Axiom utils_deserialize : state -> result (state * (HashMap_t u64)).

(** [hashmap::utils::serialize]:
    Source: 'tests/src/hashmap.rs', lines 326:4-326:46 *)
Axiom utils_serialize : HashMap_t u64 -> state -> result (state * unit).

End Hashmap_FunsExternal_Template.