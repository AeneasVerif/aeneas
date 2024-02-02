(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [arrays]: templates for the decreases clauses *)
module Arrays.Clauses.Template
open Primitives
open Arrays.Types

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [arrays::sum]: decreases clause
    Source: 'src/arrays.rs', lines 242:0-250:1 *)
unfold
let sum_loop_decreases (s : slice u32) (sum1 : u32) (i : usize) : nat =
  admit ()

(** [arrays::sum2]: decreases clause
    Source: 'src/arrays.rs', lines 252:0-261:1 *)
unfold
let sum2_loop_decreases (s : slice u32) (s2 : slice u32) (sum1 : u32)
  (i : usize) : nat =
  admit ()
