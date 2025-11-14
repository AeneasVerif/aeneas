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

(** [arrays::zero_slice]: decreases clause
    Source: 'src/arrays.rs', lines 303:0-310:1 *)
unfold
let zero_slice_loop_decreases (a : slice u8) (i : usize) (len : usize) : nat =
  if i < len then len - i else 0

(** [arrays::iter_mut_slice]: decreases clause
    Source: 'src/arrays.rs', lines 312:0-318:1 *)
unfold
let iter_mut_slice_loop_decreases (len : usize) (i : usize) : nat =
  if i < len then len - i else 0

(** [arrays::sum_mut_slice]: decreases clause
    Source: 'src/arrays.rs', lines 320:0-328:1 *)
unfold
let sum_mut_slice_loop_decreases (a : slice u32) (i : usize) (s : u32) : nat =
  if i < slice_len a then slice_len a - i else 0

unfold
let add_acc_loop_decreases (pa_src : array u32 256) (pe_dst : array u32 256) (i : usize) : nat =
  if i < 256 then 256 - i else 0
