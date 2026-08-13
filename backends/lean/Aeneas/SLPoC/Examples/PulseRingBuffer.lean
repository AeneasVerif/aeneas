import Aeneas.SLPoC.Examples.PulseArrayTests

/-!
# Pulse ring buffers

A Lean SLPoC port of
[`Pulse.Lib.RingBuffer`](https://github.com/FStarLang/FStar/blob/master/pulse/lib/pulse/lib/Pulse.Lib.RingBuffer.fst)
and its interface.  As upstream, the representation has fixed positive
capacity, a cell-wise backing array, and separately allocated mutable head,
tail, and count fields.

There are three deliberate modeling differences.  Upstream stores a `vec α`
initialized by a caller-supplied value, whereas this port stores `Option α`
cells and initializes them to `none`, so `new` needs no initializer.  Upstream
also gives `pop_front : α` (and `peek_front : α`) non-empty preconditions;
this port totalizes both operations with `Option α`.  Occupied circular slots
contain `some x`; unoccupied slots may retain stale values, exactly as the
upstream `pop_front` leaves the backing vector unchanged.

The owning predicate retains the complete physical array and all three mutable
cells.  Its circular-layout equation extracts the FIFO view by walking from
`head`, with one-wrap arithmetic justified by `count ≤ capacity`.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace PulseRingBuffer

/-! # Executable definitions -/

/-- The concrete ring-buffer representation from Pulse. -/
structure RingBuffer (α : Type) where
  buffer : PulseArray.Array (Option α)
  head : Ptr Nat
  tail : Ptr Nat
  count : Ptr Nat
  cap : Nat

/-- The physical index `offset` slots after `head`.

Under the ring-buffer bounds `head < cap` and `offset ≤ cap`, the sum crosses
the end at most once, so this is equal to `(head + offset) % cap`. -/
def circularIndex (head offset cap : Nat) : Nat :=
  if head + offset < cap then head + offset else head + offset - cap

/-- Advance one physical slot, wrapping from the last slot to zero. -/
def nextIndex (index cap : Nat) : Nat :=
  circularIndex index 1 cap

/-- Read the optional value stored at a pure physical index. -/
def cellAt (cells : List (Option α)) (index : Nat) : Option α :=
  (cells[index]?).join

/-- Extract `count` physical cells in FIFO order, starting at `head`. -/
def contentsOfBuffer (cells : List (Option α)) (head cap : Nat) :
    Nat → List (Option α)
  | 0 => []
  | count + 1 =>
      contentsOfBuffer cells head cap count ++
        [cellAt cells (circularIndex head count cap)]

/-- Allocate an empty ring buffer of fixed positive capacity. -/
def new (capacity : Nat) (_ : 0 < capacity) : St (RingBuffer α) := do
  let buffer ← PulseArray.alloc capacity none
  let head ← Aeneas.SLPoC.alloc 0
  let tail ← Aeneas.SLPoC.alloc 0
  let count ← Aeneas.SLPoC.alloc 0
  pure { buffer, head, tail, count, cap := capacity }

/-- Read the current number of queued elements. -/
def length (rb : RingBuffer α) : St Nat :=
  Aeneas.SLPoC.read rb.count

/-- Return the immutable capacity. -/
def capacity (rb : RingBuffer α) : St Nat :=
  pure rb.cap

/-- Test whether the FIFO view is empty. -/
def isEmpty (rb : RingBuffer α) : St Bool := do
  let count ← Aeneas.SLPoC.read rb.count
  if count = 0 then pure true else pure false

/-- Test whether the FIFO view occupies the complete fixed capacity. -/
def isFull (rb : RingBuffer α) : St Bool := do
  let count ← Aeneas.SLPoC.read rb.count
  if count = rb.cap then pure true else pure false

/-- Append unless the buffer is full; a full buffer is left unchanged. -/
def pushBack (rb : RingBuffer α) (value : α) : St Bool := do
  let count ← Aeneas.SLPoC.read rb.count
  if count = rb.cap then
    pure false
  else
    let tail ← Aeneas.SLPoC.read rb.tail
    let _ ← PulseArray.writeAt rb.buffer tail (some value)
    Aeneas.SLPoC.update rb.tail (nextIndex tail rb.cap)
    Aeneas.SLPoC.update rb.count (count + 1)
    pure true

/-- Remove and return the FIFO front, or return `none` when empty.

As in Pulse, a successful pop does not clear the old array slot. -/
def popFront (rb : RingBuffer α) : St (Option α) := do
  let count ← Aeneas.SLPoC.read rb.count
  if count = 0 then
    pure none
  else
    let head ← Aeneas.SLPoC.read rb.head
    let slot ← PulseArray.readAt rb.buffer head
    Aeneas.SLPoC.update rb.head (nextIndex head rb.cap)
    Aeneas.SLPoC.update rb.count (count - 1)
    pure slot.join

/-- Return the FIFO front without mutation, or `none` when empty. -/
def peekFront (rb : RingBuffer α) : St (Option α) := do
  let count ← Aeneas.SLPoC.read rb.count
  if count = 0 then
    pure none
  else
    let head ← Aeneas.SLPoC.read rb.head
    let slot ← PulseArray.readAt rb.buffer head
    pure slot.join

/-- Deallocate the backing array and all three metadata cells. -/
def free (rb : RingBuffer α) : St Unit := do
  PulseArray.free rb.buffer
  Aeneas.SLPoC.free rb.head
  Aeneas.SLPoC.free rb.tail
  Aeneas.SLPoC.free rb.count

/-! # Ghost state, specifications and proofs -/

/-- The one-wrap formula is always in bounds. -/
theorem circularIndex_lt (hhead : head < cap) (hoffset : offset ≤ cap) :
    circularIndex head offset cap < cap := by
  unfold circularIndex
  split <;> omega

/-- The bounded one-wrap formula is exactly the modulo arithmetic used by Pulse. -/
theorem circularIndex_eq_mod (hhead : head < cap) (hoffset : offset ≤ cap) :
    circularIndex head offset cap = (head + offset) % cap := by
  unfold circularIndex
  split
  · rename_i hsmall
    exact (Nat.mod_eq_of_lt hsmall).symm
  · rename_i hwrap
    have hle : cap ≤ head + offset := by omega
    have hsubLt : head + offset - cap < cap := by omega
    rw [← Nat.mod_eq_of_lt hsubLt]
    symm
    rw [Nat.mod_eq_sub_mod]
    exact hle

/-- Offset zero denotes the head itself. -/
@[simp] theorem circularIndex_zero (hhead : head < cap) :
    circularIndex head 0 cap = head := by
  simp [circularIndex, hhead]

/-- Distinct offsets before one complete revolution denote distinct cells. -/
theorem circularIndex_ne (ha : a < b) (hb : b < cap) :
    circularIndex head a cap ≠ circularIndex head b cap := by
  unfold circularIndex
  split <;> split <;> omega

/-- Advancing a circular index is the next offset from the same head. -/
theorem nextIndex_circularIndex (hcap : 0 < cap) (hhead : head < cap)
    (hoffset : offset < cap) :
    nextIndex (circularIndex head offset cap) cap =
      circularIndex head (offset + 1) cap := by
  unfold nextIndex circularIndex
  split <;> split <;> split <;> omega

/-- Moving the head first shifts every subsequent circular offset by one. -/
theorem circularIndex_nextIndex (hcap : 0 < cap) (hhead : head < cap)
    (hoffset : offset + 1 ≤ cap) :
    circularIndex (nextIndex head cap) offset cap =
      circularIndex head (offset + 1) cap := by
  unfold nextIndex circularIndex
  split <;> split <;> split <;> omega

/-- A one-step wrapped index is in bounds. -/
theorem nextIndex_lt (hcap : 0 < cap) (hindex : index < cap) :
    nextIndex index cap < cap := by
  exact circularIndex_lt hindex (by omega)

/-- Reading a different cell is unaffected by a pure list update. -/
theorem cellAt_set_ne (cells : List (Option α)) (i j : Nat)
    (value : Option α) (hne : i ≠ j) :
    cellAt (cells.set i value) j = cellAt cells j := by
  simp [cellAt, hne]

/-- Reading the updated in-bounds cell returns the new optional value. -/
theorem cellAt_set_eq (cells : List (Option α)) (i : Nat)
    (value : Option α) (hi : i < cells.length) :
    cellAt (cells.set i value) i = value := by
  simp [cellAt, hi]

/-- An update outside the extracted circular positions preserves the view. -/
theorem contentsOfBuffer_set_outside (cells : List (Option α))
    (head cap count i : Nat) (value : Option α)
    (houtside : ∀ offset, offset < count →
      i ≠ circularIndex head offset cap) :
    contentsOfBuffer (cells.set i value) head cap count =
      contentsOfBuffer cells head cap count := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      change
        contentsOfBuffer (cells.set i value) head cap count ++
            [cellAt (cells.set i value) (circularIndex head count cap)] =
          contentsOfBuffer cells head cap count ++
            [cellAt cells (circularIndex head count cap)]
      rw [ih (fun offset hoffset => houtside offset (by omega))]
      rw [cellAt_set_ne]
      exact houtside count (by omega)

/-- Updating the next free circular slot preserves the occupied prefix. -/
theorem contentsOfBuffer_set_fresh (cells : List (Option α))
    (head cap count : Nat) (value : Option α)
    (hcount : count < cap) :
    contentsOfBuffer
        (cells.set (circularIndex head count cap) value) head cap count =
      contentsOfBuffer cells head cap count := by
  apply contentsOfBuffer_set_outside
  intro offset hoffset
  exact (circularIndex_ne hoffset hcount).symm

/-- Writing at tail appends exactly one cell to the extracted circular view. -/
theorem contentsOfBuffer_push (cells : List (Option α))
    (head cap count : Nat) (value : α)
    (hhead : head < cap) (hcount : count < cap)
    (hlength : cells.length = cap) :
    contentsOfBuffer
        (cells.set (circularIndex head count cap) (some value))
        head cap (count + 1) =
      contentsOfBuffer cells head cap count ++ [some value] := by
  simp only [contentsOfBuffer]
  rw [contentsOfBuffer_set_fresh cells head cap count (some value)
    hcount]
  rw [cellAt_set_eq]
  rw [hlength]
  exact circularIndex_lt hhead (by omega)

/-- Shifting the head removes exactly the first extracted circular cell. -/
theorem contentsOfBuffer_pop (cells : List (Option α))
    (head cap count : Nat) (hcap : 0 < cap) (hhead : head < cap)
    (hcount : count + 1 ≤ cap) :
    contentsOfBuffer cells head cap (count + 1) =
      cellAt cells head ::
        contentsOfBuffer cells (nextIndex head cap) cap count := by
  induction count with
  | zero =>
      change [cellAt cells (circularIndex head 0 cap)] =
        [cellAt cells head]
      rw [circularIndex_zero hhead]
  | succ count ih =>
      change
        (contentsOfBuffer cells head cap (count + 1) ++
            [cellAt cells (circularIndex head (count + 1) cap)]) =
          cellAt cells head ::
            (contentsOfBuffer cells (nextIndex head cap) cap count ++
              [cellAt cells
                (circularIndex (nextIndex head cap) count cap)])
      rw [ih (by omega)]
      rw [circularIndex_nextIndex hcap hhead (by omega)]
      simp only [List.cons_append]

/-- Circular extraction always visits exactly `count` slots. -/
@[simp] theorem contentsOfBuffer_length (cells : List (Option α))
    (head cap count : Nat) :
    (contentsOfBuffer cells head cap count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [contentsOfBuffer, ih]

/-- Exact ownership plus the concrete circular-layout relation to a FIFO list. -/
def isRingBuffer (rb : RingBuffer α) (items : List α) (cap : Nat) : SLProp :=
  hexists fun cells : List (Option α) =>
  hexists fun head : Nat =>
  hexists fun tail : Nat =>
  hexists fun count : Nat =>
    iprop(
      ⌜rb.cap = cap ∧
        0 < cap ∧
        cells.length = cap ∧
        head < cap ∧
        tail < cap ∧
        count ≤ cap ∧
        count = items.length ∧
        tail = circularIndex head count cap ∧
        contentsOfBuffer cells head cap count = items.map some⌝ ∗
      PulseArray.owns rb.buffer cells ∗
      rb.head ↦ head ∗
      rb.tail ↦ tail ∗
      rb.count ↦ count)

/-- The invariant itself exposes the fixed positive capacity and length bound. -/
theorem isRingBuffer.pure (rb : RingBuffer α) (items : List α) (cap : Nat) :
    isRingBuffer rb items cap ⊢
      iprop(isRingBuffer rb items cap ∗ ⌜0 < cap ∧ items.length ≤ cap⌝) := by
  unfold isRingBuffer
  sl_frame

/-! ## Constructor and observers -/

/-- Construction owns every array cell and all three freshly allocated boxes. -/
@[step]
theorem new.spec (capacity : Nat) (hcapacity : 0 < capacity) :
    ⦃ emp ⦄ (new capacity hcapacity : St (RingBuffer α))
      ⦃⇓ rb => isRingBuffer rb [] capacity⦄ := by
  unfold new
  sl_step as ⟨ buffer, hlength ⟩
  sl_step as ⟨ head ⟩
  sl_step as ⟨ tail ⟩
  sl_step as ⟨ count ⟩
  sl_pure
  have hcontents :
      contentsOfBuffer (List.replicate capacity (none : Option α))
        0 capacity 0 = [] := rfl
  unfold isRingBuffer
  sl_frame

/-- Reading the count returns the exact FIFO-view length and preserves ownership. -/
@[step]
theorem length.spec (rb : RingBuffer α) (items : List α) (cap : Nat) :
    ⦃ isRingBuffer rb items cap ⦄ length rb
      ⦃⇓ n => ⌜n = items.length⌝ ∗ isRingBuffer rb items cap⦄ := by
  sl_pull cells head tail count h
  unfold length
  sl_step

/-- Capacity is immutable and returned exactly, with all ownership preserved. -/
@[step]
theorem capacity.spec (rb : RingBuffer α) (items : List α) (cap : Nat) :
    ⦃ isRingBuffer rb items cap ⦄ capacity rb
      ⦃⇓ n => ⌜n = cap⌝ ∗ isRingBuffer rb items cap⦄ := by
  sl_pull cells head tail count h
  unfold capacity
  sl_step*

/-- Emptiness is characterized exactly by the logical FIFO sequence. -/
@[step]
theorem isEmpty.spec (rb : RingBuffer α) (items : List α) (cap : Nat) :
    ⦃ isRingBuffer rb items cap ⦄ isEmpty rb
      ⦃⇓ empty =>
        ⌜empty = decide (items = [])⌝ ∗ isRingBuffer rb items cap⦄ := by
  sl_pull cells head tail count h
  unfold isEmpty
  sl_step
  split <;> sl_step

/-- Fullness is characterized exactly by logical length equaling capacity. -/
@[step]
theorem isFull.spec (rb : RingBuffer α) (items : List α) (cap : Nat) :
    ⦃ isRingBuffer rb items cap ⦄ isFull rb
      ⦃⇓ full =>
        ⌜full = decide (items.length = cap)⌝ ∗
        isRingBuffer rb items cap⦄ := by
  sl_pull cells head tail count h
  unfold isFull
  sl_step
  split <;> sl_step

/-! ## Mutation -/

/-- Push has reject-on-full behavior and otherwise appends exactly at the FIFO back. -/
@[step]
theorem pushBack.spec (rb : RingBuffer α) (items : List α) (cap : Nat)
    (value : α) :
    ⦃ isRingBuffer rb items cap ⦄ pushBack rb value
      ⦃⇓ success =>
        isRingBuffer rb (if success then items ++ [value] else items) cap ∗
        ⌜success = decide (items.length < cap)⌝⦄ := by
  sl_pull cells head tail count h
  unfold pushBack
  sl_step
  split
  · rename_i hfull
    sl_step
  · rename_i hnotfull
    sl_step
    sl_step
    sl_step
    sl_step
    have hcountlt : count < cap := by omega
    have hnewTail :
        nextIndex tail rb.cap = circularIndex head (count + 1) cap := by
      rw [h.1, h.2.2.2.2.2.2.2.1]
      exact nextIndex_circularIndex h.2.1 h.2.2.2.1 hcountlt
    have hnewTailLt : nextIndex tail rb.cap < cap := by
      rw [h.1]
      exact nextIndex_lt h.2.1 h.2.2.2.2.1
    have hcontents :
        contentsOfBuffer (cells.set tail (some value)) head cap (count + 1) =
          (items ++ [value]).map some := by
      rw [h.2.2.2.2.2.2.2.1]
      rw [contentsOfBuffer_push cells head cap count value
        h.2.2.2.1 hcountlt h.2.2.1]
      rw [h.2.2.2.2.2.2.2.2]
      simp
    sl_step*

/-- Pop reports empty without mutation, or returns and removes exactly the FIFO front. -/
@[step]
theorem popFront.spec (rb : RingBuffer α) (items : List α) (cap : Nat) :
    ⦃ isRingBuffer rb items cap ⦄ popFront rb
      ⦃⇓ result =>
        isRingBuffer rb items.tail cap ∗
        ⌜result = items.head?⌝⦄ := by
  sl_pull cells head tail count h
  unfold popFront
  sl_step
  split
  · rename_i hEmpty
    have hitems : items = [] := by
      apply List.eq_nil_of_length_eq_zero
      omega
    subst items
    sl_step
  · rename_i hnonempty
    cases items with
    | nil =>
        simp_all
    | cons front rest =>
        sl_step
        sl_step
        sl_step
        sl_step
        have hcount : count = rest.length + 1 := by
          simpa using h.2.2.2.2.2.2.1
        have hrestBound : rest.length + 1 ≤ cap := by omega
        have hheadContents :
            cellAt cells head = some front ∧
            contentsOfBuffer cells (nextIndex head cap) cap rest.length =
              rest.map some := by
          have hpop := contentsOfBuffer_pop cells head cap rest.length
            h.2.1 h.2.2.2.1 hrestBound
          rw [← hcount] at hpop
          rw [h.2.2.2.2.2.2.2.2] at hpop
          have hpairs :
              some front = cellAt cells head ∧
              rest.map some =
                contentsOfBuffer cells (nextIndex head cap) cap rest.length := by
            simpa using hpop
          exact ⟨hpairs.1.symm, hpairs.2.symm⟩
        have hphysicalHead : cells[head] = some front := by
          have hheadBound : head < cells.length := by omega
          rw [← hheadContents.1]
          simp [cellAt, hheadBound]
        have hnewHeadLt : nextIndex head rb.cap < cap := by
          rw [h.1]
          exact nextIndex_lt h.2.1 h.2.2.2.1
        have htail :
            tail =
              circularIndex (nextIndex head rb.cap) (count - 1) cap := by
          calc
            tail = circularIndex head count cap :=
              h.2.2.2.2.2.2.2.1
            _ = circularIndex head (rest.length + 1) cap := by rw [hcount]
            _ = circularIndex (nextIndex head cap) rest.length cap :=
              (circularIndex_nextIndex h.2.1 h.2.2.2.1 hrestBound).symm
            _ = circularIndex (nextIndex head rb.cap) (count - 1) cap := by
              rw [h.1, hcount, Nat.add_sub_cancel]
        sl_step*

/-- Peek is total, returns exactly the logical front, and preserves all ownership. -/
@[step]
theorem peekFront.spec (rb : RingBuffer α) (items : List α) (cap : Nat) :
    ⦃ isRingBuffer rb items cap ⦄ peekFront rb
      ⦃⇓ result =>
        ⌜result = items.head?⌝ ∗ isRingBuffer rb items cap⦄ := by
  sl_pull cells head tail count h
  unfold peekFront
  sl_step
  split
  · rename_i hEmpty
    have hitems : items = [] := by
      apply List.eq_nil_of_length_eq_zero
      omega
    subst items
    sl_step
  · rename_i hnonempty
    cases items with
    | nil =>
        simp_all
    | cons front rest =>
        sl_step
        sl_step
        have hcount : count = rest.length + 1 := by
          simpa using h.2.2.2.2.2.2.1
        have hrestBound : rest.length + 1 ≤ cap := by omega
        have hfirst : cellAt cells head = some front := by
          have hpop := contentsOfBuffer_pop cells head cap rest.length
            h.2.1 h.2.2.2.1 hrestBound
          rw [← hcount] at hpop
          rw [h.2.2.2.2.2.2.2.2] at hpop
          have hpairs :
              some front = cellAt cells head ∧
              rest.map some =
                contentsOfBuffer cells (nextIndex head cap) cap rest.length := by
            simpa using hpop
          exact hpairs.1.symm
        have hphysicalHead : cells[head] = some front := by
          have hheadBound : head < cells.length := by omega
          rw [← hfirst]
          simp [cellAt, hheadBound]
        sl_step*

/-- Free consumes the backing array and each metadata allocation exactly once. -/
@[step]
theorem free.spec (rb : RingBuffer α) (items : List α) (cap : Nat) :
    ⦃ isRingBuffer rb items cap ⦄ free rb ⦃⇓ emp⦄ := by
  sl_pull cells head tail count h
  unfold free
  sl_step*

end PulseRingBuffer

end Aeneas.SLPoC
