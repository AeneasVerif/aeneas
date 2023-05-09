-- [loops]: decreases clauses
import Base.Primitives
import Loops.Types

/- [loops::sum]: termination measure -/
@[simp]
def sum_loop_terminates (max : U32) (i : U32) (s : U32) := (max, i, s)

syntax "sum_loop_decreases" term+ : tactic

macro_rules
| `(tactic| sum_loop_decreases $max $i $s) =>`(tactic| sorry)

/- [loops::sum_with_mut_borrows]: termination measure -/
@[simp]
def sum_with_mut_borrows_loop_terminates (max : U32) (mi : U32) (ms : U32) :=
  (max, mi, ms)

syntax "sum_with_mut_borrows_loop_decreases" term+ : tactic

macro_rules
| `(tactic| sum_with_mut_borrows_loop_decreases $max $mi $ms) =>`(tactic| sorry)

/- [loops::sum_with_shared_borrows]: termination measure -/
@[simp]
def sum_with_shared_borrows_loop_terminates (max : U32) (i : U32) (s : U32) :=
  (max, i, s)

syntax "sum_with_shared_borrows_loop_decreases" term+ : tactic

macro_rules
| `(tactic| sum_with_shared_borrows_loop_decreases $max $i $s) =>`(tactic| sorry)

/- [loops::clear]: termination measure -/
@[simp] def clear_loop_terminates (v : Vec U32) (i : Usize) := (v, i)

syntax "clear_loop_decreases" term+ : tactic

macro_rules
| `(tactic| clear_loop_decreases $v $i) =>`(tactic| sorry)

/- [loops::list_mem]: termination measure -/
@[simp]
def list_mem_loop_terminates (x : U32) (ls : list_t U32) := (x, ls)

syntax "list_mem_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_mem_loop_decreases $x $ls) =>`(tactic| sorry)

/- [loops::list_nth_mut_loop]: termination measure -/
@[simp]
def list_nth_mut_loop_loop_terminates (T : Type) (ls : list_t T) (i : U32) :=
  (ls, i)

syntax "list_nth_mut_loop_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_nth_mut_loop_loop_decreases $ls $i) =>`(tactic| sorry)

/- [loops::list_nth_shared_loop]: termination measure -/
@[simp]
def list_nth_shared_loop_loop_terminates (T : Type) (ls : list_t T) (i : U32) :=
  (ls, i)

syntax "list_nth_shared_loop_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_nth_shared_loop_loop_decreases $ls $i) =>`(tactic| sorry)

/- [loops::get_elem_mut]: termination measure -/
@[simp]
def get_elem_mut_loop_terminates (x : Usize) (ls : list_t Usize) := (x, ls)

syntax "get_elem_mut_loop_decreases" term+ : tactic

macro_rules
| `(tactic| get_elem_mut_loop_decreases $x $ls) =>`(tactic| sorry)

/- [loops::get_elem_shared]: termination measure -/
@[simp]
def get_elem_shared_loop_terminates (x : Usize) (ls : list_t Usize) := (x, ls)

syntax "get_elem_shared_loop_decreases" term+ : tactic

macro_rules
| `(tactic| get_elem_shared_loop_decreases $x $ls) =>`(tactic| sorry)

/- [loops::list_nth_mut_loop_with_id]: termination measure -/
@[simp]
def list_nth_mut_loop_with_id_loop_terminates (T : Type) (i : U32)
  (ls : list_t T) :=
  (i, ls)

syntax "list_nth_mut_loop_with_id_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_nth_mut_loop_with_id_loop_decreases $i $ls) =>`(tactic| sorry)

/- [loops::list_nth_shared_loop_with_id]: termination measure -/
@[simp]
def list_nth_shared_loop_with_id_loop_terminates (T : Type) (i : U32)
  (ls : list_t T) :=
  (i, ls)

syntax "list_nth_shared_loop_with_id_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_nth_shared_loop_with_id_loop_decreases $i $ls) =>`(tactic| sorry)

/- [loops::list_nth_mut_loop_pair]: termination measure -/
@[simp]
def list_nth_mut_loop_pair_loop_terminates (T : Type) (ls0 : list_t T)
  (ls1 : list_t T) (i : U32) :=
  (ls0, ls1, i)

syntax "list_nth_mut_loop_pair_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_nth_mut_loop_pair_loop_decreases $ls0 $ls1 $i) =>`(tactic| sorry)

/- [loops::list_nth_shared_loop_pair]: termination measure -/
@[simp]
def list_nth_shared_loop_pair_loop_terminates (T : Type) (ls0 : list_t T)
  (ls1 : list_t T) (i : U32) :=
  (ls0, ls1, i)

syntax "list_nth_shared_loop_pair_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_nth_shared_loop_pair_loop_decreases $ls0 $ls1 $i) =>
  `(tactic| sorry)

/- [loops::list_nth_mut_loop_pair_merge]: termination measure -/
@[simp]
def list_nth_mut_loop_pair_merge_loop_terminates (T : Type) (ls0 : list_t T)
  (ls1 : list_t T) (i : U32) :=
  (ls0, ls1, i)

syntax "list_nth_mut_loop_pair_merge_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_nth_mut_loop_pair_merge_loop_decreases $ls0 $ls1 $i) =>
  `(tactic| sorry)

/- [loops::list_nth_shared_loop_pair_merge]: termination measure -/
@[simp]
def list_nth_shared_loop_pair_merge_loop_terminates (T : Type) (ls0 : list_t T)
  (ls1 : list_t T) (i : U32) :=
  (ls0, ls1, i)

syntax "list_nth_shared_loop_pair_merge_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_nth_shared_loop_pair_merge_loop_decreases $ls0 $ls1 $i) =>
  `(tactic| sorry)

/- [loops::list_nth_mut_shared_loop_pair]: termination measure -/
@[simp]
def list_nth_mut_shared_loop_pair_loop_terminates (T : Type) (ls0 : list_t T)
  (ls1 : list_t T) (i : U32) :=
  (ls0, ls1, i)

syntax "list_nth_mut_shared_loop_pair_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_nth_mut_shared_loop_pair_loop_decreases $ls0 $ls1 $i) =>
  `(tactic| sorry)

/- [loops::list_nth_mut_shared_loop_pair_merge]: termination measure -/
@[simp]
def list_nth_mut_shared_loop_pair_merge_loop_terminates (T : Type)
  (ls0 : list_t T) (ls1 : list_t T) (i : U32) :=
  (ls0, ls1, i)

syntax "list_nth_mut_shared_loop_pair_merge_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_nth_mut_shared_loop_pair_merge_loop_decreases $ls0 $ls1 $i) =>
  `(tactic| sorry)

/- [loops::list_nth_shared_mut_loop_pair]: termination measure -/
@[simp]
def list_nth_shared_mut_loop_pair_loop_terminates (T : Type) (ls0 : list_t T)
  (ls1 : list_t T) (i : U32) :=
  (ls0, ls1, i)

syntax "list_nth_shared_mut_loop_pair_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_nth_shared_mut_loop_pair_loop_decreases $ls0 $ls1 $i) =>
  `(tactic| sorry)

/- [loops::list_nth_shared_mut_loop_pair_merge]: termination measure -/
@[simp]
def list_nth_shared_mut_loop_pair_merge_loop_terminates (T : Type)
  (ls0 : list_t T) (ls1 : list_t T) (i : U32) :=
  (ls0, ls1, i)

syntax "list_nth_shared_mut_loop_pair_merge_loop_decreases" term+ : tactic

macro_rules
| `(tactic| list_nth_shared_mut_loop_pair_merge_loop_decreases $ls0 $ls1 $i) =>
  `(tactic| sorry)

