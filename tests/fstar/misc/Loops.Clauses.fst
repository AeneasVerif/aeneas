(** [loops]: templates for the decreases clauses *)
module Loops.Clauses
open Primitives
open Loops.Types

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [loops::sum]: decreases clause *)
unfold let sum_decreases (max : u32) (i : u32) (s : u32) : nat =
  if i <= max then max - i else 0

(** [loops::list_nth_mut_loop]: decreases clause *)
unfold
let list_nth_mut_loop_decreases (t : Type0) (ls : list_t t) (i : u32) : nat =
  i

