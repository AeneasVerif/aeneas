import Aeneas.SLPoC.MutableData.Array

/-!
# The array interface

Regression tests for `Aeneas.SLPoC.MutableData.Array`: every operation of the
interface, run end to end by the certified interpreter, and the ownership
lemmas that relate an array to the slice and the range underneath it.
-/

namespace Aeneas.SLPoC

open Aeneas.Std (Heap Result)

/-! ## Allocation, indexed access and release -/

def arrayRoundTrip : Result Nat := do
  let a ← Array.alloc Nat 3 (0 : Nat)
  a.write 0 1
  a.write 2 41
  let x ← a.read 0
  let y ← a.read 2
  a.free
  pure (x + y)

theorem arrayRoundTrip.spec :
    ⦃ emp ⦄ arrayRoundTrip ⦃⇓ result => ⌜result = 42⌝⦄ := by
  unfold arrayRoundTrip
  have hAlloc :
      ⦃ emp ⦄ Array.alloc Nat 3 (0 : Nat) ⦃⇓ a => a ↦ [0, 0, 0]⦄ := by
    simpa using Array.alloc.spec Nat 3 (0 : Nat)
  apply triple_bind hAlloc
  intro a
  have hWriteZero :
      ⦃ a ↦ [0, 0, 0] ⦄ a.write 0 1 ⦃⇓ a ↦ [1, 0, 0]⦄ := by
    simpa using Array.write.spec_array a [0, 0, 0] 0 1 (by simp)
  apply triple_bind hWriteZero
  intro _
  have hWriteTwo :
      ⦃ a ↦ [1, 0, 0] ⦄ a.write 2 41 ⦃⇓ a ↦ [1, 0, 41]⦄ := by
    simpa using Array.write.spec_array a [1, 0, 0] 2 41 (by simp)
  apply triple_bind hWriteTwo
  intro _
  apply triple_bind (Array.read.spec_array a [1, 0, 41] 0 (by simp))
  intro x
  apply triple_ipure
  intro hx
  apply triple_bind (Array.read.spec_array a [1, 0, 41] 2 (by simp))
  intro y
  apply triple_ipure
  intro hy
  apply triple_seq (Array.free.spec a [1, 0, 41])
  exact triple_pure fun _ _ => by simp_all

#guard (execClosed arrayRoundTrip arrayRoundTrip.spec).1 = 42

/-- The interpreter frees every slot, so nothing is left behind. -/
example : (execClosed arrayRoundTrip arrayRoundTrip.spec).2.size = 0 := by
  native_decide

/-! ## `ofList`, `swap` and `fill` -/

def arraySwap : Result (Nat × Nat) := do
  let a ← Array.ofList [7, 8]
  a.swap 0 1
  let x ← a.read 0
  let y ← a.read 1
  a.free
  pure (x, y)

theorem arraySwap.spec : ⦃ emp ⦄ arraySwap ⦃⇓ result => ⌜result = (8, 7)⌝⦄ := by
  unfold arraySwap
  apply triple_bind (Array.ofList.spec [7, 8])
  intro a
  have hSwap :
      ⦃ a ↦ [7, 8] ⦄ a.swap 0 1 ⦃⇓ a ↦ [8, 7]⦄ := by
    simpa using Array.swap.spec a [7, 8] 0 1 (by simp) (by simp)
  apply triple_bind hSwap
  intro _
  have hReadZero :
      ⦃ a ↦ [8, 7] ⦄ a.read 0
        ⦃⇓ result => ⌜result = 8⌝ ∗ a ↦ [8, 7]⦄ := by
    simpa using Array.read.spec_array a [8, 7] 0 (by simp)
  apply triple_bind hReadZero
  intro x
  apply triple_ipure
  intro hx
  apply triple_bind (Array.read.spec_array a [8, 7] 1 (by simp))
  intro y
  apply triple_ipure
  intro hy
  apply triple_seq (Array.free.spec a [8, 7])
  exact triple_pure fun _ _ => by simp_all

#guard (execClosed arraySwap arraySwap.spec).1 = (8, 7)

def arrayFill : Result Nat := do
  let a ← Array.alloc Nat 3 (0 : Nat)
  a.fill 5
  let value ← a.read 1
  a.free
  pure value

theorem arrayFill.spec : ⦃ emp ⦄ arrayFill ⦃⇓ result => ⌜result = 5⌝⦄ := by
  unfold arrayFill
  have hAlloc :
      ⦃ emp ⦄ Array.alloc Nat 3 (0 : Nat) ⦃⇓ a => a ↦ [0, 0, 0]⦄ := by
    simpa using Array.alloc.spec Nat 3 (0 : Nat)
  apply triple_bind hAlloc
  intro a
  have hFill :
      ⦃ a ↦ [0, 0, 0] ⦄ a.fill 5 ⦃⇓ a ↦ [5, 5, 5]⦄ := by
    simpa using Array.fill.spec a [0, 0, 0] 5
  apply triple_bind hFill
  intro _
  have hRead :
      ⦃ a ↦ [5, 5, 5] ⦄ a.read 1
        ⦃⇓ result => ⌜result = 5⌝ ∗ a ↦ [5, 5, 5]⦄ := by
    simpa using Array.read.spec_array a [5, 5, 5] 1 (by simp)
  apply triple_bind hRead
  intro value
  apply triple_ipure
  intro hValue
  apply triple_seq (Array.free.spec a [5, 5, 5])
  exact triple_pure fun _ _ => hValue

#guard (execClosed arrayFill arrayFill.spec).1 = 5

/-! ## `copy` and `compare`

Both take two arrays, and the separating conjunction is what says they are two
allocations: nothing has to assume it. -/

def arrayCopyCompare : Result Bool := do
  let src ← Array.ofList [1, 2, 3]
  let dst ← Array.alloc Nat 3 (0 : Nat)
  dst.copy src
  let same ← Array.compare dst src
  dst.free
  src.free
  pure same

theorem arrayCopyCompare.spec :
    ⦃ emp ⦄ arrayCopyCompare ⦃⇓ result => ⌜result = true⌝⦄ := by
  unfold arrayCopyCompare
  apply triple_bind (Array.ofList.spec [1, 2, 3])
  intro src
  apply triple_bind
    (triple_conseq
      (triple_frame (Array.alloc.spec Nat 3 (0 : Nat)) (src ↦ [1, 2, 3]))
      (sep_emp_l _).mpr fun _ => entails_refl _)
  intro dst
  apply triple_bind
    (triple_conseq (Array.copy.spec dst src (List.replicate 3 0) [1, 2, 3])
      (by iframe) fun _ => entails_refl _)
  intro _
  apply triple_bind (Array.compare.spec dst src [1, 2, 3] [1, 2, 3])
  intro same
  apply triple_ipure
  intro hSame
  apply triple_bind (triple_frame (Array.free.spec dst [1, 2, 3]) _)
  intro _
  apply triple_seq
    (triple_conseq (Array.free.spec src [1, 2, 3]) (sep_elim_left _ _)
      fun _ => entails_refl _)
  exact triple_pure fun _ _ => by simpa using hSame

#guard (execClosed arrayCopyCompare arrayCopyCompare.spec).1 = true

/-! ## An array is a slice, and a slice is a range

The three layers own the same slots; crossing between them transfers ownership
and nothing else. -/

/-- Owning an array is owning the slice that spans it. -/
example (a : Array Nat 3) (values : List Nat) :
    (a ↦ values) = (a.toBuffer ↦ values) :=
  Array.pointsTo_eq_buffer a values

/-- And owning the slice is owning the range its pointer owns. -/
example (a : Array Nat 3) (values : List Nat) :
    a ↦ values ⊢ a.ptr ↦* values :=
  Array.pointsTo_entails_range a values

/-- An array holds exactly as many values as its type says. -/
example (a : Array Nat 3) (values : List Nat) (h : Heap)
    (hPointsTo : (a ↦ values) h) : values.length = 3 :=
  Array.length_of_pointsTo hPointsTo

/-- A slice of known length is an array. -/
example (b : Buffer Nat) (values : List Nat) (hLength : values.length = 3) :
    b ↦ values ⊢ (b.toArray 3) ↦ values :=
  Buffer.pointsTo_toArray hLength

/-- Ownership of an array still splits along its indices, since the range
underneath it does. -/
example (a : Array Nat 3) (xs ys : List Nat) :
    a.ptr ↦* (xs ++ ys) ⊣⊢ a.ptr ↦* xs ∗ (a.ptr.add xs.length) ↦* ys :=
  Ptr.pointsToRange_append a.ptr xs ys

/-! ## Functional/memory interoperability -/

private def functionalArray :
    Aeneas.Std.Array Nat (Aeneas.Std.Usize.ofNat 3) :=
  ⟨[1, 2, 3], by simp⟩

def arrayMutToRawRoundTrip :
    Result (Aeneas.Std.Array Nat (Aeneas.Std.Usize.ofNat 3)) := do
  let a ← Array.mut_to_raw functionalArray
  a.write 1 9
  Array.end_mut_to_raw functionalArray a

theorem arrayMutToRawRoundTrip.spec :
    (arrayMutToRawRoundTrip)
      ⦃⇓ result => result.val = [1, 9, 3]⦄ := by
  unfold arrayMutToRawRoundTrip
  have hStart :
      ⦃ emp ⦄ Array.mut_to_raw functionalArray
        ⦃⇓ a => a ↦ [1, 2, 3]⦄ := by
    simpa [functionalArray] using Array.mut_to_raw.spec functionalArray
  apply triple_bind hStart
  intro a
  apply triple_bind (Array.write.spec_array a [1, 2, 3] 1 9 (by simp))
  intro _
  exact Array.end_mut_to_raw.spec functionalArray a [1, 9, 3]

#guard (execClosed arrayMutToRawRoundTrip arrayMutToRawRoundTrip.spec).1.val =
  [1, 9, 3]

/-- Ending the raw array borrow releases every materialized slot. -/
example :
    (execClosed arrayMutToRawRoundTrip arrayMutToRawRoundTrip.spec).2.size = 0 := by
  native_decide

private def functionalSlice : Aeneas.Std.Slice Nat :=
  ⟨[4, 5, 6], by scalar_tac⟩

def bufferMutToRawRoundTrip : Result (Aeneas.Std.Slice Nat) := do
  let b ← Buffer.mut_to_raw functionalSlice
  b.write 2 7
  Buffer.end_mut_to_raw functionalSlice b

theorem bufferMutToRawRoundTrip.spec :
    (bufferMutToRawRoundTrip)
      ⦃⇓ result => result.val = [4, 5, 7]⦄ := by
  unfold bufferMutToRawRoundTrip
  have hStart :
      ⦃ emp ⦄ Buffer.mut_to_raw functionalSlice
        ⦃⇓ b => b ↦ [4, 5, 6]⦄ := by
    simpa [functionalSlice] using Buffer.mut_to_raw.spec functionalSlice
  apply triple_bind hStart
  intro b
  apply triple_bind (Buffer.write.spec_array b [4, 5, 6] 2 7 (by simp))
  intro _
  exact triple_conseq (Buffer.end_mut_to_raw.spec functionalSlice b [4, 5, 7])
    (entails_refl _) fun _ h hPost => by
      simpa [functionalSlice, List.setSlice!] using hPost

#guard (execClosed bufferMutToRawRoundTrip bufferMutToRawRoundTrip.spec).1.val =
  [4, 5, 7]

/-- Ending the raw slice borrow releases every materialized slot. -/
example :
    (execClosed bufferMutToRawRoundTrip bufferMutToRawRoundTrip.spec).2.size = 0 := by
  native_decide

end Aeneas.SLPoC
