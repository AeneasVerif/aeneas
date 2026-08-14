import Aeneas.SLPoC.Examples.PulseArrayTests

/-!
# Verus verified-vector fixed-capacity kernel

This module is an adapted SLPoC model of the post-resize, fixed-capacity kernel
inside
[`examples/verified_vec.rs`](https://github.com/verus-lang/verus/blob/main/examples/verified_vec.rs):
the initialized-prefix invariant, indexed observation, and the one-slot
ownership transition performed after `push` has established spare capacity.
It is not a direct port of the source's full `push`: upstream `empty` creates
capacity zero, and a full `push` calls the unfinished `resize` operation.  Here
`newFixed` starts with a campaign-supplied capacity and `pushNoResize` explicitly
rejects a full vector.  This isolates and proves the bounded operation requested
by the campaign without assigning behavior to the incomplete resize path or its
`assume(false)`.

The backing allocation reuses `PulseArray.Array`, whose cells are separately
allocated and owned.  `Option α` is only a typed initialization-state
abstraction: `some value` marks an initialized cell and `none` marks an
uninitialized cell.  The model does not represent source-level byte
uninitialization.  In particular, it omits:

* contiguous allocation and pointer/address arithmetic;
* alignment, layout, and `PointsToRaw.into_typed` conversion; and
* the allocation-wide `DeallocRaw` token and deallocation behavior.

The owning predicate spatially separates the initialized prefix from this
typed-uninitialized suffix.  A successful `pushNoResize` consumes exactly the
first suffix cell, writes `some value`, and adds that cell to the initialized
prefix.  A full vector returns `false` without changing ownership or contents.

Upstream `index` returns a borrowed `&V`.  Lean values in this SLPoC model do
not encode Rust borrow lifetimes, so `readValue` instead observes the stored
value and returns a copy while preserving all cell ownership.

This differs from `PulseResizableVec`: that module deliberately permits stale
values beyond its logical length (to support `pop` without clearing a slot),
whereas this bounded abstraction keeps every suffix marker equal to `none`.
-/

namespace Aeneas.SLPoC

open scoped SepLogic

namespace VerusVerifiedVec

/-! # Executable definitions -/

/-- A fixed-capacity vector backed by cell-wise `Option α` storage. -/
structure Vector (α : Type) where
  buffer : PulseArray.Array (Option α)
  lengthCell : Ptr Nat
  fixedCapacity : Nat

/-- Allocate an empty bounded abstraction with `capacity` uninitialized markers. -/
def newFixed (capacity : Nat) : St (Vector α) := do
  let buffer ← PulseArray.alloc capacity none
  let lengthCell ← Aeneas.SLPoC.alloc 0
  pure { buffer, lengthCell, fixedCapacity := capacity }

/-- Read the current number of initialized elements. -/
def length (v : Vector α) : St Nat :=
  Aeneas.SLPoC.read v.lengthCell

/-- Return the immutable capacity of the allocation. -/
def capacity (v : Vector α) : St Nat :=
  pure v.fixedCapacity

/-- Observe a copied value, returning `none` when the index is out of bounds. -/
def readValue (v : Vector α) (i : Nat) : St (Option α) := do
  let size ← length v
  if i < size then
    let slot ← PulseArray.readAt v.buffer i
    pure slot.join
  else
    pure none

/-- Run the post-resize append kernel, rejecting without change when full. -/
def pushNoResize (v : Vector α) (value : α) : St Bool := do
  let size ← length v
  let cap ← capacity v
  if size < cap then
    let _ ← PulseArray.writeAt v.buffer size (some value)
    Aeneas.SLPoC.update v.lengthCell (size + 1)
    pure true
  else
    pure false

/-! # Ghost state, specifications and proofs -/

/-- Ownership of the initialized prefix: each cell contains its exact value. -/
def initializedOwn : List (Ptr (Option α)) → List α → SLProp
  | [], [] => emp
  | cell :: cells, value :: values =>
      iprop(cell ↦ some value ∗ initializedOwn cells values)
  | _, _ => ⌜False⌝

/-- Ownership of the typed-uninitialized suffix: every marker is `none`. -/
def uninitializedOwn : List (Ptr (Option α)) → SLProp
  | [] => emp
  | cell :: cells => iprop(cell ↦ none ∗ uninitializedOwn cells)

/-- Ownership for the bounded typed abstraction.

`prefix` and `suffix` partition the physical backing cells.  Their lengths
record the initialized length and fixed allocation capacity, while their
separate spatial predicates abstract the source's `elems` map and `rest`
range.  This predicate makes no contiguous-layout or deallocation-token claim. -/
def owns (v : Vector α) (contents : List α) (cap : Nat) : SLProp :=
  hexists fun initCells : List (Ptr (Option α)) =>
    hexists fun suffix : List (Ptr (Option α)) =>
      iprop(
        ⌜v.buffer.cells = initCells ++ suffix⌝ ∗
        ⌜initCells.length = contents.length⌝ ∗
        ⌜initCells.length + suffix.length = cap⌝ ∗
        ⌜v.fixedCapacity = cap⌝ ∗
        initializedOwn initCells contents ∗
        uninitializedOwn suffix ∗
        v.lengthCell ↦ contents.length)

/-- Reassemble bounded-model ownership from an explicit cell partition. -/
theorem partition_entails_owns
    (v : Vector α) (contents : List α) (cap : Nat)
    (initCells suffix : List (Ptr (Option α)))
    (hcells : v.buffer.cells = initCells ++ suffix)
    (hinit : initCells.length = contents.length)
    (htotal : initCells.length + suffix.length = cap)
    (hcapacity : v.fixedCapacity = cap) :
    iprop(
      initializedOwn initCells contents ∗
      uninitializedOwn suffix ∗
      v.lengthCell ↦ contents.length) ⊢
      owns v contents cap := by
  unfold owns
  refine himpl_hexists_r initCells ?_
  refine himpl_hexists_r suffix ?_
  sl_frame

@[simp, sl_simps] theorem initializedOwn_nil :
    initializedOwn ([] : List (Ptr (Option α))) ([] : List α) = emp := rfl

@[simp, sl_simps] theorem initializedOwn_cons
    (cell : Ptr (Option α)) (cells : List (Ptr (Option α)))
    (value : α) (values : List α) :
    initializedOwn (cell :: cells) (value :: values) =
      iprop(cell ↦ some value ∗ initializedOwn cells values) := rfl

@[simp, sl_simps] theorem uninitializedOwn_nil :
    uninitializedOwn ([] : List (Ptr (Option α))) = emp := rfl

@[simp, sl_simps] theorem uninitializedOwn_cons
    (cell : Ptr (Option α)) (cells : List (Ptr (Option α))) :
    uninitializedOwn (cell :: cells) =
      iprop(cell ↦ none ∗ uninitializedOwn cells) := rfl

@[simp] theorem ownsCells_replicate_none
    (cells : List (Ptr (Option α))) :
    PulseArray.ownsCells cells (List.replicate cells.length none) =
      uninitializedOwn cells := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      simp only [List.length_cons, List.replicate_succ,
        PulseArray.ownsCells_cons, uninitializedOwn_cons, ih]

@[simp] theorem join_map_some (value : Option α) :
    (value.map some).join = value := by
  cases value <;> rfl

/-! ## Cell-wise prefix operations -/

/-- Reading inside the initialized prefix never touches the uninitialized suffix. -/
@[step]
theorem readInitialized.spec
    (initCells suffix : List (Ptr (Option α))) (contents : List α) (i : Nat)
    (hi : i < contents.length) :
    ⦃ initializedOwn initCells contents ∗ uninitializedOwn suffix ⦄
      PulseArray.readCells (initCells ++ suffix) i
    ⦃⇓ slot =>
      ⌜slot = contents[i]?.map some⌝ ∗
      initializedOwn initCells contents ∗ uninitializedOwn suffix⦄ := by
  induction initCells generalizing contents i with
  | nil =>
      cases contents with
      | nil => simp at hi
      | cons value values =>
          sl_pull
          contradiction
  | cons cell initCells ih =>
      cases contents with
      | nil =>
          sl_pull
          contradiction
      | cons value values =>
          cases i with
          | zero =>
              simp only [List.cons_append,
                PulseArray.readCells, List.getElem?_cons_zero, Option.map_some]
              sl_step*
          | succ i =>
              simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
              simp only [List.cons_append]
              rw [PulseArray.readCells, List.getElem?_cons_succ]
              sl_step with ih values i hi

/-- A successful write transfers one typed-uninitialized cell to the
initialized prefix. -/
@[step]
theorem initializeNext.spec
    (initCells suffix : List (Ptr (Option α))) (next : Ptr (Option α))
    (contents : List α) (value : α) :
    ⦃ initializedOwn initCells contents ∗ uninitializedOwn (next :: suffix) ⦄
      PulseArray.writeCells (initCells ++ next :: suffix) contents.length (some value)
    ⦃⇓ written =>
      ⌜written = true⌝ ∗
      initializedOwn (initCells ++ [next]) (contents ++ [value]) ∗
      uninitializedOwn suffix⦄ := by
  induction initCells generalizing contents with
  | nil =>
      cases contents with
      | nil =>
          simp only [List.nil_append, List.length_nil,
            PulseArray.writeCells, List.nil_append]
          sl_step*
      | cons old contents =>
          sl_pull
          contradiction
  | cons cell initCells ih =>
      cases contents with
      | nil =>
          sl_pull
          contradiction
      | cons old contents =>
          simp only [List.cons_append, List.length_cons,
            PulseArray.writeCells]
          sl_step with ih contents

/-! ## Construction and observations -/

/-- Allocation establishes an empty prefix and `capacity` uninitialized markers. -/
@[step]
theorem newFixed.spec (capacity : Nat) :
    ⦃ emp ⦄ newFixed (α := α) capacity
      ⦃⇓ v => owns v [] capacity⦄ := by
  unfold newFixed
  sl_step as ⟨ buffer, hlength ⟩
  sl_step as ⟨ lengthCell ⟩
  sl_pure
  unfold PulseArray.owns
  rw [← hlength, ownsCells_replicate_none]
  have htotal :
      ([] : List (Ptr (Option α))).length + buffer.cells.length = capacity := by
    simpa only [List.length_nil, Nat.zero_add] using hlength
  have hOwn := partition_entails_owns
    ({ buffer, lengthCell, fixedCapacity := capacity } : Vector α)
    [] capacity [] buffer.cells rfl rfl htotal rfl
  simp only [initializedOwn_nil, List.length_nil] at hOwn
  sl_xchange hOwn
  sl_frame

/-- Length returns the exact initialized-prefix length and preserves ownership. -/
@[step]
theorem length.spec (v : Vector α) (contents : List α) (cap : Nat) :
    ⦃ owns v contents cap ⦄ length v
      ⦃⇓ size => ⌜size = contents.length⌝ ∗ owns v contents cap⦄ := by
  unfold length
  sl_pull
  sl_step*

/-- Capacity returns the exact allocation capacity and preserves ownership. -/
@[step]
theorem capacity.spec (v : Vector α) (contents : List α) (cap : Nat) :
    ⦃ owns v contents cap ⦄ capacity v
      ⦃⇓ result => ⌜result = cap⌝ ∗ owns v contents cap⦄ := by
  unfold capacity
  sl_pull _ _ _ _ _ hcapacity
  simp only [hcapacity]
  sl_step*

/-- Exact value observation for the abstraction: in-bounds indices return the
logical element, out-of-bounds indices return `none`, and ownership is preserved. -/
@[step]
theorem readValue.spec (v : Vector α) (contents : List α) (cap i : Nat) :
    ⦃ owns v contents cap ⦄ readValue v i
      ⦃⇓ result => ⌜result = contents[i]?⌝ ∗ owns v contents cap⦄ := by
  unfold readValue length
  sl_pull initCells suffix hcells _ _ _
  sl_step
  split
  · rename_i hi
    unfold PulseArray.readAt
    rw [hcells]
    sl_step with readInitialized.spec initCells suffix contents i hi
    simp_all only [join_map_some]
    sl_step*
  · rename_i hi
    have hout : contents[i]? = none := List.getElem?_eq_none (by omega)
    simp only [hout]
    sl_step*

/-! ## Post-resize fixed-capacity append kernel -/

/-- The bounded kernel appends exactly one value and preserves capacity when
there is room.  When full it returns `false` and preserves the whole abstract
state; unlike upstream `push`, it does not attempt `resize`. -/
@[step]
theorem pushNoResize.spec
    (v : Vector α) (contents : List α) (cap : Nat) (value : α) :
    ⦃ owns v contents cap ⦄ pushNoResize v value
      ⦃⇓ pushed =>
        ⌜pushed = decide (contents.length < cap)⌝ ∗
        owns v
          (if contents.length < cap then contents ++ [value] else contents)
          cap⦄ := by
  unfold pushNoResize length capacity
  sl_pull initCells suffix hcells hprefix htotal hcapacity
  sl_step
  simp only [hcapacity]
  sl_step
  split
  · rename_i hroom
    have hsuffix : suffix ≠ [] := by
      intro hSuffixEmpty
      subst suffix
      simp only [List.length_nil, Nat.add_zero] at htotal
      omega
    cases suffix with
    | nil => contradiction
    | cons next suffix =>
        unfold PulseArray.writeAt
        rw [hcells]
        sl_step with initializeNext.spec initCells suffix next contents value
        sl_step
        have hcells' :
            v.buffer.cells = (initCells ++ [next]) ++ suffix := by
          simpa only [List.append_assoc, List.singleton_append] using hcells
        have hprefix' :
            (initCells ++ [next]).length = (contents ++ [value]).length := by
          simp only [List.length_append, List.length_cons, List.length_nil, hprefix]
        have htotal' :
            (initCells ++ [next]).length + suffix.length = cap := by
          simp only [List.length_cons] at htotal
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hroom, decide_true]
        sl_step*
  · rename_i hfull
    have hsuffixLength : suffix.length = 0 := by omega
    have hsuffix : suffix = [] := List.eq_nil_of_length_eq_zero hsuffixLength
    subst suffix
    simp only [hfull, decide_false]
    sl_pure
    sl_xchange (partition_entails_owns v contents cap initCells []
      hcells hprefix htotal hcapacity)
    sl_frame

end VerusVerifiedVec

end Aeneas.SLPoC
