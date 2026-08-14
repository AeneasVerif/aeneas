import Aeneas.SLPoC.Examples.PulseArrayTests

/-!
# Pulse insertion sort

This module ports
[`Pulse.Lib.InsertionSort`](https://github.com/FStarLang/FStar/blob/master/pulse/lib/pulse/lib/Pulse.Lib.InsertionSort.fst).
Pulse's outer loop extends a sorted prefix and its inner loop shifts larger
elements right before writing the saved key.  Here structural recursion visits
the array from right to left: the recursive call sorts the suffix, and
`insertCells` inserts the preceding cell by swapping it rightward through that
suffix.  This is the same stable insertion-sort step with the traversal
direction reversed; every comparison, read, and write still acts on an
individual `PulseArray.Array` cell.

The final specification identifies the exact logical contents left in the
original array, proves them sorted, and proves them a permutation of the input.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace PulseInsertionSort

open PulseArray

/-! # Executable definitions -/

/-- The executable comparison corresponding to Pulse's total-order `<=?`. -/
def inOrder [LinearOrder α] (left right : α) : Bool :=
  decide (left ≤ right)

/--
Insert the value in `current` into the sorted suffix.

When the next value is smaller, the two cells are swapped and insertion
continues from the next cell.  Thus the routine is genuinely in-place and
touches only the cells whose values move.
-/
def insertCells [LinearOrder α] (current : Ptr α) : List (Ptr α) → St Unit
  | [] => pure ()
  | next :: rest => do
      let key ← read current
      let value ← read next
      if inOrder key value then
        pure ()
      else
        update current value
        update next key
        insertCells next rest

/--
Sort a list of array cells in place.

The recursive call sorts the suffix; `insertCells` then inserts the head value
into it.  This is the structurally recursive, right-to-left counterpart of
Pulse's prefix-growing outer loop.
-/
def sortCells [LinearOrder α] : List (Ptr α) → St Unit
  | [] => pure ()
  | current :: rest => do
      sortCells rest
      insertCells current rest

/-- In-place insertion sort over the cell-wise Pulse array representation. -/
def insertionSort [LinearOrder α] (array : PulseArray.Array α) : St Unit :=
  sortCells array.cells

/-! # Ghost state, specifications and proofs -/

/-- Pure insertion matching the cell-wise executable insertion step. -/
def orderedInsert [LinearOrder α] (key : α) : List α → List α
  | [] => [key]
  | value :: rest =>
      if inOrder key value then
        key :: value :: rest
      else
        value :: orderedInsert key rest

/-- Pure insertion sort matching `sortCells`. -/
def sortedContents [LinearOrder α] : List α → List α
  | [] => []
  | key :: rest => orderedInsert key (sortedContents rest)

/-- Pulse's `sorted` predicate, represented by pairwise nondecreasing order. -/
def Sorted [LinearOrder α] (values : List α) : Prop :=
  values.Pairwise (· ≤ ·)

/-- Pulse's count-based permutation predicate, using Lean's list permutation. -/
def Permutation (before after : List α) : Prop :=
  before.Perm after

/-- Every value in a list is bounded below by `lower`. -/
def LowerBound [LE α] (lower : α) (values : List α) : Prop :=
  ∀ value ∈ values, lower ≤ value

private theorem lowerBound_cons [LE α] {lower head : α} {tail : List α} :
    LowerBound lower (head :: tail) ↔ lower ≤ head ∧ LowerBound lower tail := by
  simp [LowerBound]

private theorem lowerBound_orderedInsert [LinearOrder α]
    {lower key : α} {values : List α}
    (hlower : LowerBound lower values) (hkey : lower ≤ key) :
    LowerBound lower (orderedInsert key values) := by
  induction values with
  | nil =>
      simpa [orderedInsert, LowerBound] using hkey
  | cons value rest ih =>
      rw [lowerBound_cons] at hlower
      simp only [orderedInsert]
      split
      · simp only [LowerBound, List.mem_cons]
        intro item hitem
        rcases hitem with rfl | rfl | hitem
        · exact hkey
        · exact hlower.1
        · exact hlower.2 item hitem
      · rw [lowerBound_cons]
        exact ⟨hlower.1, ih hlower.2⟩

/-- Inserting into a sorted list preserves sortedness. -/
theorem orderedInsert_sorted [LinearOrder α] (key : α) (values : List α)
    (hsorted : Sorted values) :
    Sorted (orderedInsert key values) := by
  induction values with
  | nil =>
      simp [orderedInsert, Sorted]
  | cons value rest ih =>
      rw [Sorted, List.pairwise_cons] at hsorted
      simp only [orderedInsert]
      split
      · rename_i hkey
        simp only [inOrder, decide_eq_true_eq] at hkey
        rw [Sorted, List.pairwise_cons]
        refine ⟨?_, ?_⟩
        intro item hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with rfl | hmem
        · exact hkey
        · exact hkey.trans (hsorted.1 item hmem)
        rw [List.pairwise_cons]
        exact hsorted
      · rename_i hkey
        simp only [inOrder, decide_eq_true_eq, not_le] at hkey
        rw [Sorted, List.pairwise_cons]
        refine ⟨?_, ih hsorted.2⟩
        apply lowerBound_orderedInsert hsorted.1
        exact hkey.le

/-- Pure insertion preserves exactly the input multiset. -/
theorem orderedInsert_perm [LinearOrder α] (key : α) (values : List α) :
    Permutation (key :: values) (orderedInsert key values) := by
  induction values with
  | nil =>
      simp [orderedInsert, Permutation]
  | cons value rest ih =>
      simp only [orderedInsert]
      split
      · exact List.Perm.refl _
      · exact (List.Perm.swap key value rest).symm.trans
          (List.Perm.cons value ih)

/-- The pure model always produces sorted contents. -/
theorem sortedContents_sorted [LinearOrder α] (values : List α) :
    Sorted (sortedContents values) := by
  induction values with
  | nil =>
      simp [sortedContents, Sorted]
  | cons key rest ih =>
      simp only [sortedContents]
      exact orderedInsert_sorted key (sortedContents rest) ih

/-- The pure model preserves exactly the input multiset. -/
theorem sortedContents_perm [LinearOrder α] (values : List α) :
    Permutation values (sortedContents values) := by
  induction values with
  | nil =>
      simp [sortedContents, Permutation]
  | cons key rest ih =>
      simp only [sortedContents]
      exact (List.Perm.cons key ih).trans
        (orderedInsert_perm key (sortedContents rest))

/--
The inner-loop invariant: insertion changes the logical values exactly as
`orderedInsert` specifies while retaining ownership of the same cell pointers.
-/
@[step]
theorem insertCells.spec [LinearOrder α] (current : Ptr α)
    (cells : List (Ptr α)) (key : α) (values : List α) :
    ⦃ PulseArray.ownsCells (current :: cells) (key :: values) ⦄
      insertCells current cells
    ⦃⇓ PulseArray.ownsCells (current :: cells) (orderedInsert key values)⦄ := by
  induction cells generalizing current key values with
  | nil =>
      cases values with
      | nil =>
          simp only [insertCells, orderedInsert]
          sl_step*
      | cons value values =>
          simp only [PulseArray.ownsCells]
          rw [hstar_comm_eq _ (⌜False⌝)]
          apply triple_hpure
          intro hfalse
          contradiction
  | cons next cells ih =>
      cases values with
      | nil =>
          simp only [PulseArray.ownsCells]
          rw [hstar_comm_eq _ (⌜False⌝)]
          apply triple_hpure
          intro hfalse
          contradiction
      | cons value values =>
          simp only [insertCells]
          sl_step* 2
          split
          · rename_i horder
            simp only [orderedInsert, horder]
            sl_step*
          · rename_i horder
            simp only [orderedInsert, horder]
            sl_step* 2
            sl_step with ih next key values

/--
The outer-loop invariant: the recursively processed suffix has precisely the
pure sorted contents, and the head insertion extends that result without
changing array ownership.
-/
@[step]
theorem sortCells.spec [LinearOrder α] (cells : List (Ptr α))
    (values : List α) :
    ⦃ PulseArray.ownsCells cells values ⦄ sortCells cells
    ⦃⇓ PulseArray.ownsCells cells (sortedContents values)⦄ := by
  induction cells generalizing values with
  | nil =>
      cases values with
      | nil =>
          simp only [sortCells, sortedContents]
          sl_step*
      | cons value values =>
          sl_pull
          contradiction
  | cons current cells ih =>
      cases values with
      | nil =>
          sl_pull
          contradiction
      | cons key values =>
          simp only [sortCells, sortedContents]
          sl_step with ih values
          sl_step with insertCells.spec current cells key (sortedContents values)

/--
Complete Pulse-style correctness theorem.  The original array retains exact
ownership, its final logical contents are sorted, and they are a permutation
of the original contents.
-/
@[step]
theorem insertionSort.spec [LinearOrder α] (array : PulseArray.Array α)
    (values : List α) :
    ⦃ PulseArray.owns array values ⦄ insertionSort array
    ⦃⇓
      ⌜Sorted (sortedContents values) ∧
        Permutation values (sortedContents values)⌝ ∗
      PulseArray.owns array (sortedContents values)⦄ := by
  have hcorrect :
      Sorted (sortedContents values) ∧
      Permutation values (sortedContents values) :=
    ⟨sortedContents_sorted values, sortedContents_perm values⟩
  unfold insertionSort
  sl_step with sortCells.spec array.cells values

end PulseInsertionSort

end Aeneas.SLPoC
