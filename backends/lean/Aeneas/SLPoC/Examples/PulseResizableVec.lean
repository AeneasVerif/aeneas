import Aeneas.SLPoC.Examples.PulseArrayTests

/-!
# Pulse bounded resizable vectors

This module is a Lean SLPoC port of
[`Pulse.Lib.ResizableVec`](https://github.com/FStarLang/FStar/blob/master/pulse/lib/pulse/lib/Pulse.Lib.ResizableVec.fst)
and its interface.  As in Pulse, a vector owns a fixed-capacity backing buffer
of `Option α` cells and separate mutable size and capacity cells.  The logical
contents describe exactly the initialized prefix; cells after that prefix are
logically uninitialized and may retain old `some` values after `pop`, matching
the source implementation.

Pulse uses refinements to require in-bounds `get`/`set`, room for `push`, and a
nonempty vector for `pop`.  The executable Lean interface makes those checks
explicit: `get` and `pop` return `Option`, while `set` and `push` return `Bool`.
The upstream module itself exposes no buffer-growth operation: despite its
name, it is a bounded vector.  This port therefore preserves that exact
fixed-capacity behavior rather than assuming successful resizing.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace PulseResizableVec

/-! # Executable definitions -/

/-- Composite representation corresponding to Pulse's buffer, size box, and
capacity box. -/
structure ResizableVec (α : Type) where
  buffer : PulseArray.Array (Option α)
  sizeCell : Ptr Nat
  capacityCell : Ptr Nat

/-- Allocate a vector with an empty logical prefix and `capacity` buffer cells. -/
def new (capacity : Nat) : St (ResizableVec α) := do
  let buffer ← PulseArray.alloc capacity none
  let sizeCell ← Aeneas.SLPoC.alloc 0
  let capacityCell ← Aeneas.SLPoC.alloc capacity
  pure ⟨buffer, sizeCell, capacityCell⟩

/-- Read the current logical length. -/
def length (v : ResizableVec α) : St Nat :=
  Aeneas.SLPoC.read v.sizeCell

/-- Read the fixed maximum capacity. -/
def capacity (v : ResizableVec α) : St Nat :=
  Aeneas.SLPoC.read v.capacityCell

/-- Read an element, returning `none` exactly when the logical index is out of bounds. -/
def get (v : ResizableVec α) (i : Nat) : St (Option α) := do
  let size ← length v
  if i < size then
    let slot ← PulseArray.readAt v.buffer i
    pure slot.join
  else
    pure none

/-- Update an element and report whether the logical index was in bounds. -/
def set (v : ResizableVec α) (i : Nat) (value : α) : St Bool := do
  let size ← length v
  if i < size then
    let _ ← PulseArray.writeAt v.buffer i (some value)
    pure true
  else
    pure false

/-- Append when there is room, returning `false` without changing the vector when full. -/
def push (v : ResizableVec α) (value : α) : St Bool := do
  let size ← length v
  let cap ← capacity v
  if size < cap then
    let _ ← PulseArray.writeAt v.buffer size (some value)
    Aeneas.SLPoC.update v.sizeCell (size + 1)
    pure true
  else
    pure false

/-- Remove the last logical element, returning `none` exactly when empty. -/
def pop (v : ResizableVec α) : St (Option α) := do
  let size ← length v
  if size = 0 then
    pure none
  else
    let last := size - 1
    let slot ← PulseArray.readAt v.buffer last
    Aeneas.SLPoC.update v.sizeCell last
    pure slot.join

/-- Test whether another element can be appended. -/
def hasRoom (v : ResizableVec α) : St Bool := do
  let size ← length v
  let cap ← capacity v
  pure (size < cap)

/-- Free the backing cells and the two separately owned metadata cells. -/
def free (v : ResizableVec α) : St Unit := do
  PulseArray.free v.buffer
  Aeneas.SLPoC.free v.sizeCell
  Aeneas.SLPoC.free v.capacityCell

/-! # Ghost state, specifications and proofs -/

/-- The backing list has fixed length `cap`, and its initialized prefix stores
exactly `contents`.  The suffix is deliberately unconstrained, as in Pulse's
`buf_wf`: `pop` decreases the size without clearing the old slot. -/
def bufferInv (contents : List α) (cap : Nat) (buffer : List (Option α)) : Prop :=
  buffer.length = cap ∧
  contents.length ≤ cap ∧
  0 < cap ∧
  ∀ i, i < contents.length →
    buffer[i]? = contents[i]?.map some

/-- Full composite ownership of the buffer and both metadata cells. -/
def owns (v : ResizableVec α) (contents : List α) (cap : Nat) : SLProp :=
  hexists fun buffer =>
    iprop(
      ⌜bufferInv contents cap buffer⌝ ∗
      PulseArray.owns v.buffer buffer ∗
      v.sizeCell ↦ contents.length ∗
      v.capacityCell ↦ cap)

@[simp] theorem bufferInv_empty (cap : Nat) (hcap : 0 < cap) :
    bufferInv ([] : List α) cap (List.replicate cap none) := by
  simp [bufferInv, hcap]

@[simp] theorem join_map_some (value : Option α) :
    (value.map some).join = value := by
  cases value <;> rfl

theorem list_set_eq_self_of_length_le (values : List α) (i : Nat) (value : α)
    (h : values.length ≤ i) :
    values.set i value = values := by
  induction values generalizing i with
  | nil => simp
  | cons head tail ih =>
      cases i with
      | zero => simp at h
      | succ i =>
          simp only [List.set_cons_succ]
          congr
          apply ih
          simp only [List.length_cons, Nat.succ_le_succ_iff] at h
          exact h

theorem bufferInv_get (h : bufferInv contents cap buffer)
    (hi : i < contents.length) :
    buffer[i]? = contents[i]?.map some :=
  h.2.2.2 i hi

theorem bufferInv_set (h : bufferInv contents cap buffer) :
    bufferInv (contents.set i value) cap (buffer.set i (some value)) := by
  rcases h with ⟨hbuffer, hcontents, hcap, hget⟩
  constructor
  · simpa using hbuffer
  constructor
  · simpa using hcontents
  constructor
  · exact hcap
  · intro j hj
    have hj' : j < contents.length := by simpa using hj
    have hjBuffer : j < buffer.length := by omega
    rw [List.getElem?_set_of_lt (some value) buffer hjBuffer]
    rw [List.getElem?_set_of_lt value contents hj']
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, hget j hj']

theorem bufferInv_push (h : bufferInv contents cap buffer)
    (hroom : contents.length < cap) :
    bufferInv (contents ++ [value]) cap
      (buffer.set contents.length (some value)) := by
  rcases h with ⟨hbuffer, hcontents, hcap, hget⟩
  have hindex : contents.length < buffer.length := by omega
  constructor
  · simpa using hbuffer
  constructor
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  constructor
  · exact hcap
  · intro j hj
    simp only [List.length_append, List.length_cons, List.length_nil] at hj
    by_cases hjold : j < contents.length
    · have hjBuffer : j < buffer.length := by omega
      rw [List.getElem?_set_of_lt (some value) buffer hjBuffer]
      have hne : contents.length ≠ j := by omega
      simp only [hne, if_false, List.getElem?_append_left hjold]
      exact hget j hjold
    · have hjeq : j = contents.length := by omega
      subst j
      rw [List.getElem?_set_eq_of_lt (some value) hindex]
      simp

theorem bufferInv_pop (h : bufferInv contents cap buffer) :
    bufferInv contents.dropLast cap buffer := by
  rcases h with ⟨hbuffer, hcontents, hcap, hget⟩
  constructor
  · exact hbuffer
  constructor
  · rw [List.length_dropLast]
    omega
  constructor
  · exact hcap
  · intro i hi
    have hi' : i < contents.length := by
      rw [List.length_dropLast] at hi
      omega
    have hvalue := hget i hi'
    rw [List.getElem?_eq_getElem hi'] at hvalue
    rw [List.getElem?_eq_getElem hi]
    rw [List.getElem_dropLast hi]
    exact hvalue

/-! ## Construction and observations -/

/-- Allocation establishes empty contents, exact capacity, and ownership of all cells. -/
@[step]
theorem new.spec (cap : Nat) (hcap : 0 < cap) :
    ⦃ emp ⦄ new (α := α) cap
      ⦃⇓ v => owns v [] cap⦄ := by
  unfold new
  sl_step as ⟨ buffer, hlength ⟩
  sl_step as ⟨ sizeCell ⟩
  sl_step as ⟨ capacityCell ⟩
  sl_pure
  unfold owns
  have hInv := bufferInv_empty (α := α) cap hcap
  sl_frame

/-- Length returns the exact logical length and preserves complete ownership. -/
@[step]
theorem length.spec (v : ResizableVec α) (contents : List α) (cap : Nat) :
    ⦃ owns v contents cap ⦄ length v
      ⦃⇓ n => ⌜n = contents.length⌝ ∗ owns v contents cap⦄ := by
  unfold length
  sl_pull
  sl_step*

/-- Capacity returns the exact fixed capacity and preserves complete ownership. -/
@[step]
theorem capacity.spec (v : ResizableVec α) (contents : List α) (cap : Nat) :
    ⦃ owns v contents cap ⦄ capacity v
      ⦃⇓ n => ⌜n = cap⌝ ∗ owns v contents cap⦄ := by
  unfold capacity
  sl_pull
  sl_step*

/-- The room test is exact and preserves complete ownership. -/
@[step]
theorem hasRoom.spec (v : ResizableVec α) (contents : List α) (cap : Nat) :
    ⦃ owns v contents cap ⦄ hasRoom v
      ⦃⇓ room =>
        ⌜room = decide (contents.length < cap)⌝ ∗ owns v contents cap⦄ := by
  unfold hasRoom
  sl_step*

/-! ## Indexed access -/

/-- `get` returns the exact logical optional lookup, including the out-of-bounds result. -/
@[step]
theorem get.spec (v : ResizableVec α) (contents : List α) (cap i : Nat) :
    ⦃ owns v contents cap ⦄ get v i
      ⦃⇓ result => ⌜result = contents[i]?⌝ ∗ owns v contents cap⦄ := by
  unfold get length
  sl_pull _ hInv
  sl_step
  split
  · rename_i hi
    sl_step
    have hslot := bufferInv_get hInv hi
    simp only [hslot, join_map_some]
    sl_step*
  · rename_i hi
    have hout : contents[i]? = none := List.getElem?_eq_none (by omega)
    simp only [hout]
    sl_step*

/-- `set` reports the exact bounds test and updates exactly the selected logical element. -/
@[step]
theorem set.spec (v : ResizableVec α) (contents : List α) (cap i : Nat)
    (value : α) :
    ⦃ owns v contents cap ⦄ set v i value
      ⦃⇓ written =>
        ⌜written = decide (i < contents.length)⌝ ∗
        owns v (contents.set i value) cap⦄ := by
  unfold set length
  sl_pull _ hInv
  sl_step
  split
  · rename_i hi
    sl_step
    have hnewInv := bufferInv_set (i := i) (value := value) hInv
    simp only [hi, decide_true]
    sl_step*
  · rename_i hi
    have hset : contents.set i value = contents :=
      list_set_eq_self_of_length_le contents i value (by omega)
    simp only [hi, decide_false, hset]
    sl_step*

/-! ## Stack operations -/

/-- `push` succeeds exactly below capacity, appends exactly one value on
success, and always preserves the fixed capacity and all ownership. -/
@[step]
theorem push.spec (v : ResizableVec α) (contents : List α) (cap : Nat)
    (value : α) :
    ⦃ owns v contents cap ⦄ push v value
      ⦃⇓ pushed =>
        ⌜pushed = decide (contents.length < cap)⌝ ∗
        owns v (if contents.length < cap then contents ++ [value] else contents) cap⦄ := by
  unfold push length capacity
  sl_pull buffer hInv
  sl_step* 2
  split
  · rename_i hroom
    have hindex : contents.length < buffer.length := by
      rw [hInv.1]
      exact hroom
    sl_step*
    have hnewInv := bufferInv_push (value := value) hInv hroom
    simp only [hroom, decide_true]
    sl_step*
  · rename_i hfull
    simp only [hfull, decide_false]
    sl_step*

/-- `pop` returns the exact last element, removes exactly that element, and
preserves capacity and complete ownership. -/
@[step]
theorem pop.spec (v : ResizableVec α) (contents : List α) (cap : Nat) :
    ⦃ owns v contents cap ⦄ pop v
      ⦃⇓ result =>
        ⌜result = contents.getLast?⌝ ∗ owns v contents.dropLast cap⦄ := by
  unfold pop length
  sl_pull _ hInv
  sl_step
  split
  · rename_i hEmpty
    have hnil : contents = [] := List.eq_nil_of_length_eq_zero hEmpty
    subst contents
    simp only [List.getLast?_nil, List.dropLast_nil]
    sl_step*
  · rename_i hnonempty
    have hlast : contents.length - 1 < contents.length := by omega
    sl_step
    have hslot := bufferInv_get hInv hlast
    sl_step
    simp only [hslot, join_map_some]
    have hlastValue : contents[contents.length - 1]? = contents.getLast? := by
      exact List.getLast?_eq_getElem?.symm
    rw [hlastValue]
    have hnewInv := bufferInv_pop hInv
    sl_step*

/-! ## Deallocation -/

/-- Free consumes the complete buffer and metadata ownership. -/
@[step]
theorem free.spec (v : ResizableVec α) (contents : List α) (cap : Nat) :
    ⦃ owns v contents cap ⦄ free v ⦃⇓ emp⦄ := by
  unfold free
  sl_pull
  sl_step*

end PulseResizableVec

end Aeneas.SLPoC
