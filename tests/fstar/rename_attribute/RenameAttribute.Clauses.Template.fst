(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [rename_attribute]: templates for the decreases clauses *)
module RenameAttribute.Clauses.Template
open Primitives
open RenameAttribute.Types

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [rename_attribute::factorial]: decreases clause
    Source: 'tests/src/rename_attribute.rs', lines 55:0-55:27 *)
unfold let factfn_decreases (n : u64) : nat = admit ()

(** [rename_attribute::sum]: decreases clause
    Source: 'tests/src/rename_attribute.rs', lines 64:0-64:27 *)
unfold
let no_borrows_sum_loop_decreases (max : u32) (i : u32) (s : u32) : nat =
  admit ()

