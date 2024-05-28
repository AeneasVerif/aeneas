(** [hashmap]: external functions. *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Export Hashmap_Types.
Import Hashmap_Types.
Module Hashmap_FunsExternal.

(** [hashmap::utils::deserialize]:
    Source: 'tests/src/hashmap.rs', lines 330:4-330:47 *)
Axiom utils_deserialize : state -> result (state * (HashMap_t u64)).

(** [hashmap::utils::serialize]:
    Source: 'tests/src/hashmap.rs', lines 325:4-325:46 *)
Axiom utils_serialize : HashMap_t u64 -> state -> result (state * unit)
.

End Hashmap_FunsExternal.
