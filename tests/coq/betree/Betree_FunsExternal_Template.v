(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [betree]: external functions.
-- This is a template file: rename it to "FunsExternal.lean" and fill the holes. *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Betree_Types.
Include Betree_Types.
Module Betree_FunsExternal_Template.

(** [betree::betree_utils::load_internal_node]:
    Source: 'src/betree_utils.rs', lines 98:0-112:1 *)
Axiom betree_utils_load_internal_node
  : u64 -> state -> result (state * (betree_List_t (u64 * betree_Message_t)))
.

(** [betree::betree_utils::store_internal_node]:
    Source: 'src/betree_utils.rs', lines 115:0-129:1 *)
Axiom betree_utils_store_internal_node
  :
  u64 -> betree_List_t (u64 * betree_Message_t) -> state -> result (state *
    unit)
.

(** [betree::betree_utils::load_leaf_node]:
    Source: 'src/betree_utils.rs', lines 132:0-142:1 *)
Axiom betree_utils_load_leaf_node
  : u64 -> state -> result (state * (betree_List_t (u64 * u64)))
.

(** [betree::betree_utils::store_leaf_node]:
    Source: 'src/betree_utils.rs', lines 145:0-155:1 *)
Axiom betree_utils_store_leaf_node
  : u64 -> betree_List_t (u64 * u64) -> state -> result (state * unit)
.

End Betree_FunsExternal_Template.
