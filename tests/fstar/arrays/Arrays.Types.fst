(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [arrays]: type definitions *)
module Arrays.Types
open Primitives

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [arrays::AB]
    Source: 'tests/src/arrays.rs', lines 6:0-9:1 *)
type aB_t = | AB_A : aB_t | AB_B : aB_t

