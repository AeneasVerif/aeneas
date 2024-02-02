(** [arrays]: decreases clauses *)
module Arrays.Clauses
open Primitives
open Arrays.Types
open FStar.List.Tot

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [arrays::sum]: decreases clause *)
unfold
let sum_loop_decreases (s : slice u32) (sum : u32) (i : usize) : nat =
  if i < length s then length s - i else 0

(** [arrays::sum2]: decreases clause *)
unfold
let sum2_loop_decreases (s : slice u32) (s2 : slice u32) (sum : u32)
  (i : usize) : nat =
  if i < length s then length s - i else 0

