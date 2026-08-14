import Aeneas.SLPoC.Step

/-!
# Pulse array tests

This module ports the executable behavior and specifications of:

* [`pulse/test/ArrayTests.fst`](https://github.com/FStarLang/FStar/blob/master/pulse/test/ArrayTests.fst),
* [`Pulse.Lib.Array.fsti`](https://github.com/FStarLang/FStar/blob/master/pulse/lib/pulse/lib/Pulse.Lib.Array.fsti),
* [`pulse/test/VecAlloc.fst`](https://github.com/FStarLang/FStar/blob/master/pulse/test/VecAlloc.fst).

Unlike Pulse's primitive contiguous arrays, an executable `PulseArray.Array α`
stores an ordered list of element pointers.  The separation-logic predicate
`PulseArray.owns` recursively owns those cells and relates them to a pure
`List α`.  This cell-wise model makes allocation, deallocation, reads, writes,
fills, and comparisons reusable by later data-structure ports.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace PulseArray

/-! # Executable definitions -/

/-- An executable array is an ordered collection of separately allocated cells. -/
structure Array (α : Type) where
  cells : List (Ptr α)

/-- Allocate `n` cells, each initialized to `value`. -/
def allocCells (n : Nat) (value : α) : St (List (Ptr α)) :=
  match n with
  | 0 => pure []
  | n + 1 => do
      let p ← Aeneas.SLPoC.alloc value
      let ps ← allocCells n value
      pure (p :: ps)

/-- Allocate an initialized array. -/
def alloc (n : Nat) (value : α) : St (Array α) := do
  let cells ← allocCells n value
  pure ⟨cells⟩

/-- Free every pointer in a list of cells. -/
def freeCells : List (Ptr α) → St Unit
  | [] => pure ()
  | p :: ps => do
      Aeneas.SLPoC.free p
      freeCells ps

/-- Free every cell of an array. -/
def free (a : Array α) : St Unit :=
  freeCells a.cells

/-- Read a cell by logical index, returning `none` when out of bounds. -/
def readCells : List (Ptr α) → Nat → St (Option α)
  | [], _ => pure none
  | p :: _, 0 => do
      let value ← Aeneas.SLPoC.read p
      pure (some value)
  | _ :: ps, i + 1 => readCells ps i

/-- Read an array element by logical index. -/
def readAt (a : Array α) (i : Nat) : St (Option α) :=
  readCells a.cells i

/-- Write a cell by logical index, returning whether the index was in bounds. -/
def writeCells : List (Ptr α) → Nat → α → St Bool
  | [], _, _ => pure false
  | p :: _, 0, value => do
      Aeneas.SLPoC.update p value
      pure true
  | _ :: ps, i + 1, value => writeCells ps i value

/-- Write an array element by logical index. -/
def writeAt (a : Array α) (i : Nat) (value : α) : St Bool :=
  writeCells a.cells i value

/-- Recursively overwrite every cell with `value`. -/
def fillCells : List (Ptr α) → α → St Unit
  | [], _ => pure ()
  | p :: ps, value => do
      Aeneas.SLPoC.update p value
      fillCells ps value

/-- Pulse `ArrayTests.fill_array`: overwrite every logical element. -/
def fill (a : Array α) (value : α) : St Unit :=
  fillCells a.cells value

/-- Recursively compare two cell lists, stopping at the first unequal value. -/
def compareCells [DecidableEq α] :
    List (Ptr α) → List (Ptr α) → St Bool
  | [], [] => pure true
  | [], _ :: _ => pure false
  | _ :: _, [] => pure false
  | p :: ps, q :: qs => do
      let left ← Aeneas.SLPoC.read p
      let right ← Aeneas.SLPoC.read q
      if left = right then
        compareCells ps qs
      else
        pure false

/-- Pulse `ArrayTests.compare`, generalized to arrays of possibly different lengths. -/
def compare [DecidableEq α] (left right : Array α) : St Bool :=
  compareCells left.cells right.cells

/-- Pulse `VecAlloc.hf`: allocate 100 initialized cells and free them all. -/
def vecAllocSmoke : St Unit := do
  let a ← alloc 100 (1 : Nat)
  free a

/-! # Ghost state, specifications and proofs -/

/-- Recursive ownership of cell pointers and their corresponding logical values. -/
def ownsCells : List (Ptr α) → List α → SLProp
  | [], [] => emp
  | p :: ps, value :: values => iprop(p ↦ value ∗ ownsCells ps values)
  | _, _ => ⌜False⌝

/-- Full ownership of an executable array with logical contents `values`. -/
def owns (a : Array α) (values : List α) : SLProp :=
  ownsCells a.cells values

@[simp] theorem ownsCells_nil :
    ownsCells ([] : List (Ptr α)) ([] : List α) = emp := rfl

@[simp] theorem ownsCells_cons (p : Ptr α) (ps : List (Ptr α))
    (value : α) (values : List α) :
    ownsCells (p :: ps) (value :: values) =
      iprop(p ↦ value ∗ ownsCells ps values) := rfl

@[simp] theorem owns_mk (cells : List (Ptr α)) (values : List α) :
    owns (Array.mk cells) values = ownsCells cells values := rfl

/-! ## Allocation and deallocation -/

/-- Recursive allocation invariant: every returned pointer owns an initialized cell. -/
@[step]
theorem allocCells.spec (n : Nat) (value : α) :
    ⦃ emp ⦄ allocCells n value
      ⦃⇓ cells =>
        ⌜cells.length = n⌝ ∗ ownsCells cells (List.replicate n value)⦄ := by
  induction n with
  | zero =>
      simp only [allocCells, List.replicate_zero]
      sl_pure
      simp only [List.length_nil, ownsCells_nil]
      sl_frame
  | succ n ih =>
      rw [allocCells]
      sl_step as ⟨ p ⟩
      sl_step with ih as ⟨ cells, hlength ⟩
      sl_pure
      simp only [List.length_cons, hlength, List.replicate_succ, ownsCells_cons]
      sl_frame

/-- Allocation returns `n` initialized cells and exposes their exact length. -/
@[step]
theorem alloc.spec (n : Nat) (value : α) :
    ⦃ emp ⦄ alloc n value
      ⦃⇓ a =>
        ⌜a.cells.length = n⌝ ∗ owns a (List.replicate n value)⦄ := by
  unfold alloc
  sl_step as ⟨ cells, hlength ⟩
  sl_pure
  simp only [hlength, owns]
  sl_frame

/-- Recursive deallocation invariant: every owned cell is consumed exactly once. -/
@[step]
theorem freeCells.spec (cells : List (Ptr α)) (values : List α) :
    ⦃ ownsCells cells values ⦄ freeCells cells ⦃⇓ emp⦄ := by
  induction cells generalizing values with
  | nil =>
      cases values with
      | nil =>
          simp only [freeCells]
          sl_step*
      | cons value values =>
          sl_pull
          contradiction
  | cons p cells ih =>
      cases values with
      | nil =>
          sl_pull
          contradiction
      | cons value values =>
          simp only [freeCells]
          sl_step
          sl_step with ih values

/-- Free consumes the complete array ownership predicate. -/
@[step]
theorem free.spec (a : Array α) (values : List α) :
    ⦃ owns a values ⦄ free a ⦃⇓ emp⦄ := by
  unfold free
  sl_step*

/-! ## Indexed reads and writes -/

/-- Recursive read invariant: the logical contents and all ownership are preserved. -/
@[step]
theorem readCells.spec (cells : List (Ptr α)) (values : List α) (i : Nat) :
    ⦃ ownsCells cells values ⦄ readCells cells i
      ⦃⇓ result => ⌜result = values[i]?⌝ ∗ ownsCells cells values⦄ := by
  induction cells generalizing values i with
  | nil =>
      cases values with
      | nil =>
          simp only [readCells, List.getElem?_nil]
          sl_step*
      | cons value values =>
          sl_pull
          contradiction
  | cons p cells ih =>
      cases values with
      | nil =>
          sl_pull
          contradiction
      | cons value values =>
          cases i with
          | zero =>
              simp only [readCells, List.getElem?_cons_zero]
              sl_step*
          | succ i =>
              simp only [readCells, List.getElem?_cons_succ]
              sl_step with ih values i

/-- Exact public read specification. -/
@[step]
theorem readAt.spec (a : Array α) (values : List α) (i : Nat) :
    ⦃ owns a values ⦄ readAt a i
      ⦃⇓ result => ⌜result = values[i]?⌝ ∗ owns a values⦄ := by
  unfold readAt
  sl_step*

/-- Recursive write invariant: only the selected logical element changes. -/
@[step]
theorem writeCells.spec (cells : List (Ptr α)) (values : List α)
    (i : Nat) (value : α) :
    ⦃ ownsCells cells values ⦄ writeCells cells i value
      ⦃⇓ written =>
        ⌜written = decide (i < values.length)⌝ ∗
        ownsCells cells (values.set i value)⦄ := by
  induction cells generalizing values i with
  | nil =>
      cases values with
      | nil =>
          simp only [writeCells, List.length_nil, Nat.not_lt_zero,
            decide_false, List.set_nil]
          sl_step*
      | cons old values =>
          sl_pull
          contradiction
  | cons p cells ih =>
      cases values with
      | nil =>
          sl_pull
          contradiction
      | cons old values =>
          cases i with
          | zero =>
              simp only [writeCells, List.length_cons, Nat.zero_lt_succ,
                decide_true, List.set_cons_zero]
              sl_step*
          | succ i =>
              simp only [writeCells, List.length_cons, Nat.succ_lt_succ_iff,
                List.set_cons_succ]
              sl_step with ih values i

/-- Exact public write specification, including its bounds result. -/
@[step]
theorem writeAt.spec (a : Array α) (values : List α) (i : Nat) (value : α) :
    ⦃ owns a values ⦄ writeAt a i value
      ⦃⇓ written =>
        ⌜written = decide (i < values.length)⌝ ∗
        owns a (values.set i value)⦄ := by
  unfold writeAt
  sl_step*

/-! ## Fill and compare -/

/-- Recursive fill invariant: the processed head is updated before recurring on the tail. -/
@[step]
theorem fillCells.spec (cells : List (Ptr α)) (values : List α) (value : α) :
    ⦃ ownsCells cells values ⦄ fillCells cells value
      ⦃⇓ ownsCells cells (List.replicate values.length value)⦄ := by
  induction cells generalizing values with
  | nil =>
      cases values with
      | nil =>
          simp only [fillCells, List.length_nil, List.replicate_zero]
          sl_step*
      | cons old values =>
          sl_pull
          contradiction
  | cons p cells ih =>
      cases values with
      | nil =>
          sl_pull
          contradiction
      | cons old values =>
          simp only [fillCells, List.length_cons, List.replicate_succ]
          sl_step
          sl_step with ih values

/-- Pulse `fill_array`: every logical element becomes `value`, with ownership preserved. -/
@[step]
theorem fill.spec (a : Array α) (values : List α) (value : α) :
    ⦃ owns a values ⦄ fill a value
      ⦃⇓ owns a (List.replicate values.length value)⦄ := by
  unfold fill
  sl_step*

/-- Recursive comparison invariant for spatially disjoint inputs: both ownership
predicates are preserved exactly. -/
@[step]
theorem compareCells.disjoint_spec [DecidableEq α]
    (leftCells rightCells : List (Ptr α)) (leftValues rightValues : List α) :
    ⦃ ownsCells leftCells leftValues ∗ ownsCells rightCells rightValues ⦄
      compareCells leftCells rightCells
    ⦃⇓ equal =>
      ⌜equal = decide (leftValues = rightValues)⌝ ∗
      ownsCells leftCells leftValues ∗ ownsCells rightCells rightValues⦄ := by
  induction leftCells generalizing leftValues rightCells rightValues with
  | nil =>
      cases leftValues with
      | cons value values =>
          sl_pull
          contradiction
      | nil =>
          cases rightCells with
          | nil =>
              cases rightValues with
              | nil =>
                  simp only [ownsCells_nil, compareCells, decide_true]
                  sl_step*
              | cons value values =>
                  simp only [ownsCells]
                  sl_pull
                  contradiction
          | cons q rightCells =>
              cases rightValues with
              | nil =>
                  simp only [ownsCells]
                  sl_pull
                  contradiction
              | cons rightValue rightValues =>
                  simp only [ownsCells_nil, ownsCells_cons, compareCells]
                  sl_step*
  | cons p leftCells ih =>
      cases leftValues with
      | nil =>
          sl_pull
          contradiction
      | cons leftValue leftValues =>
          cases rightCells with
          | nil =>
              cases rightValues with
              | nil =>
                  simp only [ownsCells_cons, ownsCells_nil, compareCells,
                    List.cons_ne_nil, decide_false]
                  sl_step*
              | cons value values =>
                  simp only [ownsCells]
                  rw [hstar_comm_eq _ (⌜False⌝)]
                  apply triple_hpure
                  intro hfalse
                  contradiction
          | cons q rightCells =>
              cases rightValues with
              | nil =>
                  simp only [ownsCells]
                  rw [hstar_comm_eq _ (⌜False⌝)]
                  apply triple_hpure
                  intro hfalse
                  contradiction
              | cons rightValue rightValues =>
                  simp only [ownsCells_cons, compareCells]
                  sl_step* 2
                  split
                  · rename_i heq
                    subst rightValue
                    simp only [List.cons.injEq, true_and]
                    sl_step with ih rightCells leftValues rightValues
                  · rename_i hne
                    simp only [List.cons.injEq, hne, false_and, decide_false]
                    sl_step*

/-- Comparing a cell list with itself needs only one ownership predicate.
Each pair of immutable reads returns the same owned value, and recursion
preserves the ownership of the unprocessed tail. -/
theorem compareCells.self_spec [DecidableEq α]
    (cells : List (Ptr α)) (values : List α) :
    ⦃ ownsCells cells values ⦄ compareCells cells cells
      ⦃⇓ equal => ⌜equal = true⌝ ∗ ownsCells cells values⦄ := by
  induction cells generalizing values with
  | nil =>
      cases values with
      | nil =>
          simp only [compareCells]
          sl_step*
      | cons value values =>
          sl_pull
          contradiction
  | cons p cells ih =>
      cases values with
      | nil =>
          sl_pull
          contradiction
      | cons value values =>
          simp only [compareCells]
          sl_step* 2
          rw [if_pos True.intro]
          sl_step with ih values

/-- Disjoint-input form of Pulse `compare`: the result exactly characterizes
logical equality and both independent ownership predicates are preserved.

Together with `compare.self_spec`, this covers safe source comparisons whose
arrays are either exactly self-aliased or spatially disjoint. Partial cell
overlap is intentionally outside this first-order ownership model. -/
@[step]
theorem compare.disjoint_spec [DecidableEq α]
    (left right : Array α) (leftValues rightValues : List α) :
    ⦃ owns left leftValues ∗ owns right rightValues ⦄ compare left right
      ⦃⇓ equal =>
        ⌜equal = decide (leftValues = rightValues)⌝ ∗
        owns left leftValues ∗ owns right rightValues⦄ := by
  unfold compare
  sl_step*

/-- Exact-self-alias form of Pulse `compare`: the actual program
`compare a a` returns `true` while preserving the array's single ownership
predicate. This models legal upstream immutable self-aliasing without
fractional permissions. -/
theorem compare.self_spec [DecidableEq α] (a : Array α) (values : List α) :
    ⦃ owns a values ⦄ compare a a
      ⦃⇓ equal => ⌜equal = true⌝ ∗ owns a values⦄ := by
  unfold compare
  sl_step with compareCells.self_spec a.cells values

/-- The Vec allocation smoke test allocates initialized cells and frees all of them. -/
@[step]
theorem vecAllocSmoke.spec :
    ⦃ emp ⦄ vecAllocSmoke ⦃⇓ emp⦄ := by
  unfold vecAllocSmoke
  sl_step*

end PulseArray

end Aeneas.SLPoC
