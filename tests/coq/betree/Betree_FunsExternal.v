(** [betree_main]: external functions.
-- This is a template file: rename it to "FunsExternal.lean" and fill the holes. *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Export Betree_Types.
Import Betree_Types.
Module Betree_FunsExternal.

(** [betree_main::betree_utils::load_internal_node]: forward function
    Source: 'src/betree_utils.rs', lines 98:0-98:63 *)
Axiom betree_utils_load_internal_node
  : u64 -> state -> result (state * (betree_List_t (u64 * betree_Message_t)))
.

(** [betree_main::betree_utils::store_internal_node]: forward function
    Source: 'src/betree_utils.rs', lines 115:0-115:71 *)
Axiom betree_utils_store_internal_node
  :
  u64 -> betree_List_t (u64 * betree_Message_t) -> state -> result (state *
    unit)
.

(** [betree_main::betree_utils::load_leaf_node]: forward function
    Source: 'src/betree_utils.rs', lines 132:0-132:55 *)
Axiom betree_utils_load_leaf_node
  : u64 -> state -> result (state * (betree_List_t (u64 * u64)))
.

(** [betree_main::betree_utils::store_leaf_node]: forward function
    Source: 'src/betree_utils.rs', lines 145:0-145:63 *)
Axiom betree_utils_store_leaf_node
  : u64 -> betree_List_t (u64 * u64) -> state -> result (state * unit)
.

End Betree_FunsExternal.
