(** [rename_attribute]: the decreases clauses *)
module RenameAttribute.Clauses
open Primitives
open RenameAttribute.Types

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [rename_attribute::factorial]: decreases clause
    Source: 'tests/src/rename_attribute.rs', lines 55:0-55:27 *)
unfold let factfn_decreases (n : u64) : nat = n

(** [rename_attribute::sum]: decreases clause
    Source: 'tests/src/rename_attribute.rs', lines 64:0-64:27 *)
unfold let no_borrows_sum_loop_decreases (max : u32) (i : u32) (s : u32) : nat =
  if max >= i then max - i else 0

