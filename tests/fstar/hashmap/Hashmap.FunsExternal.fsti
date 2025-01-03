(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [hashmap]: external function declarations *)
module Hashmap.FunsExternal
open Primitives
include Hashmap.Types

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [hashmap::utils::deserialize]:
    Source: 'tests/src/hashmap.rs', lines 331:4-333:5 *)
val utils_deserialize : state -> result (state & (hashMap_t u64))

(** [hashmap::utils::serialize]:
    Source: 'tests/src/hashmap.rs', lines 326:4-328:5 *)
val utils_serialize : hashMap_t u64 -> state -> result (state & unit)

(** [core::clone::Clone::clone_from]:
    Source: '/rustc/library/core/src/clone.rs', lines 174:4-174:43
    Name pattern: core::clone::Clone::clone_from *)
val core_clone_Clone_clone_from
  (#self : Type0) (self_clause : core_clone_Clone self) :
  self -> self -> state -> result (state & self)

