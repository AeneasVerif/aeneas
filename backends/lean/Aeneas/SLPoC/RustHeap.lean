import Aeneas.SLPoC.ST

/-!
# The Rust view of the heap

A translated Rust program manipulates *pointers*, not the allocation
identifiers of `Aeneas.SLPoC.Heap`. This file introduces `Ptr α`, the pointer
to a value of type `α` such a program uses, together with its heap operations
and their separation-logic specifications.
-/

namespace Aeneas.SLPoC

/-- A Rust pointer to a value of type `α`. -/
abbrev Ptr (α : Type) := Ref α

/-- Pointers are inhabited, which is what makes the `unwrap`s of a translated
Rust program expressible as `Option.get!`. -/
instance instInhabitedPtr {α : Type} : Inhabited (Ptr α) :=
  inferInstanceAs (Inhabited (Ref α))

namespace Ptr

variable {α : Type}

/-! ## Operations -/

/-- The heap made of the single cell `p`, holding `value`. -/
abbrev singleton (p : Ptr α) (value : α) : Heap :=
  _root_.Aeneas.SLPoC.singleton p value

/-- `p` points to no cell of `h`. -/
def unallocated (h : Heap) (p : Ptr α) : Prop :=
  _root_.Aeneas.SLPoC.unallocated h p

/-- `h'` is `h` extended with a cell holding `value`, freshly allocated at
`p`. -/
def fresh (h : Heap) (p : Ptr α) (value : α) (h' : Heap) : Prop :=
  _root_.Aeneas.SLPoC.fresh h p value h'

/-- `h` has a cell at `p`, and it holds a value of type `α`. -/
def contains (h : Heap) (p : Ptr α) : Prop :=
  _root_.Aeneas.SLPoC.contains h p

/-- Read the value `p` points at. -/
def read (p : Ptr α) (h : Heap) (hContains : contains h p) : α :=
  Heap.read p h hContains

/-- Write `value` through `p`. -/
def update (p : Ptr α) (value : α) (h : Heap)
    (hContains : contains h p) : Heap :=
  Heap.update p value h hContains

/-- Deallocate the cell `p` points at. -/
def free (p : Ptr α) (h : Heap) (hContains : contains h p) : Heap :=
  Heap.free p h hContains

/-! ## Allocation -/

/-- The pointer the next allocation returns. Allocation is deterministic, so a
program can be run and not only related to its outcomes. -/
def freshPtr (α : Type) (h : Heap) : Ptr α :=
  _root_.Aeneas.SLPoC.freshRef α h

/-- The heap `freshPtr` allocates into. -/
def freshHeap {α : Type} (h : Heap) (value : α) : Heap :=
  _root_.Aeneas.SLPoC.freshHeap h value

theorem fresh_freshPtr (value : α) (h : Heap) :
    fresh h (freshPtr α h) value (freshHeap h value) :=
  _root_.Aeneas.SLPoC.fresh_freshRef value h

theorem exists_fresh (value : α) (h : Heap) :
    ∃ p h', fresh h p value h' :=
  _root_.Aeneas.SLPoC.exists_fresh value h

/-! ## How the operations interact with the union of two heaps

These are the lemmas that make the frame rule provable: an operation performed
on a sub-heap can equally be performed on the whole heap, and leaves the other
part of it untouched. -/

theorem contains_union_left {h₁ h₂ : Heap} {p : Ptr α}
    (hContains : contains h₁ p) : contains (h₁ ∪ h₂) p :=
  _root_.Aeneas.SLPoC.contains_union_left hContains

/-- A heap that extends the cell `p` contains it: this is what an affine
points-to assertion gives, the cells it does not describe being unconstrained. -/
theorem contains_of_sub {p : Ptr α} {value : α} {h : Heap}
    (hSub : Heap.Sub (singleton p value) h) : contains h p := by
  obtain ⟨rest, _, rfl⟩ := hSub
  exact contains_union_left (contains_singleton p value)

/-- Two disjoint heaps cannot both own the cell `p`. -/
theorem disjoint_contains_false {h₁ h₂ : Heap} {p : Ptr α}
    (hDisjoint : PartialCommMonoid.Compatible h₁ h₂)
    (hContains₁ : contains h₁ p)
    (hContains₂ : contains h₂ p) : False :=
  _root_.Aeneas.SLPoC.disjoint_contains_false hDisjoint hContains₁ hContains₂

theorem read_union_left {h₁ h₂ : Heap} {p : Ptr α}
    (hContains : contains h₁ p) :
    read p (h₁ ∪ h₂) (contains_union_left hContains) =
      read p h₁ hContains :=
  _root_.Aeneas.SLPoC.read_union_left hContains

theorem update_union_left {h₁ h₂ : Heap} (p : Ptr α) (value : α)
    (hContains : contains h₁ p) :
    update p value (h₁ ∪ h₂) (contains_union_left hContains) =
      update p value h₁ hContains ∪ h₂ :=
  _root_.Aeneas.SLPoC.update_union_left p value hContains

theorem free_union_left {h₁ h₂ : Heap} (p : Ptr α)
    (hDisjoint : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ p) :
    free p (h₁ ∪ h₂) (contains_union_left hContains) =
      free p h₁ hContains ∪ h₂ :=
  _root_.Aeneas.SLPoC.free_union_left p hDisjoint hContains

theorem fresh_frame {p : Ptr α} {value : α} {h₁ h₂ h : Heap}
    (hDisjoint : PartialCommMonoid.Compatible h₁ h₂)
    (hFresh : fresh (h₁ ∪ h₂) p value h) :
    ∃ h₁',
      fresh h₁ p value h₁' ∧
      PartialCommMonoid.Compatible h₁' h₂ ∧
      h = h₁' ∪ h₂ :=
  _root_.Aeneas.SLPoC.fresh_frame hDisjoint hFresh

theorem disjoint_update_left {p : Ptr α} {value : α} {h₁ h₂ : Heap}
    (hDisjoint : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ p) :
    PartialCommMonoid.Compatible (update p value h₁ hContains) h₂ :=
  _root_.Aeneas.SLPoC.disjoint_update_left hDisjoint hContains

theorem disjoint_free_left {p : Ptr α} {h₁ h₂ : Heap}
    (hDisjoint : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ p) :
    PartialCommMonoid.Compatible (free p h₁ hContains) h₂ :=
  _root_.Aeneas.SLPoC.disjoint_free_left hDisjoint hContains

/-! ## The operations on the heap of a single cell

These describe the effect of each operation on exactly the resources its
specification owns. -/

theorem fresh_empty_eq_singleton {p : Ptr α} {value : α} {h : Heap}
    (hFresh : fresh empty p value h) : h = singleton p value :=
  _root_.Aeneas.SLPoC.fresh_empty_eq_singleton hFresh

theorem fresh_eq_singleton_union {p : Ptr α} {value : α} {h h' : Heap}
    (hFresh : fresh h p value h') :
    PartialCommMonoid.Compatible (singleton p value) h ∧
      h' = singleton p value ∪ h := by
  have hUnion : empty ∪ h = h := Heap.empty_union h
  have hDisjointEmpty : PartialCommMonoid.Compatible empty h :=
    PartialCommMonoid.compatible_empty_left h
  have hFreshUnion : fresh (empty ∪ h) p value h' := by rw [hUnion]; exact hFresh
  obtain ⟨h₁, hFresh₁, hDisjoint, rfl⟩ := fresh_frame hDisjointEmpty hFreshUnion
  obtain rfl := fresh_empty_eq_singleton hFresh₁
  exact ⟨hDisjoint, rfl⟩

theorem contains_singleton (p : Ptr α) (value : α) :
    contains (singleton p value) p :=
  _root_.Aeneas.SLPoC.contains_singleton p value

/-- Two cells at different pointers are disjoint. -/
theorem disjoint_singleton {p q : Ptr α} {value₁ value₂ : α} (hNe : p ≠ q) :
    PartialCommMonoid.Compatible
      (singleton p value₁) (singleton q value₂) :=
  _root_.Aeneas.SLPoC.disjoint_singleton hNe

theorem read_singleton (p : Ptr α) (value : α)
    (hContains : contains (singleton p value) p) :
    read p (singleton p value) hContains = value :=
  _root_.Aeneas.SLPoC.read_singleton p value hContains

theorem update_singleton (p : Ptr α) (oldValue newValue : α)
    (hContains : contains (singleton p oldValue) p) :
    update p newValue (singleton p oldValue) hContains =
      singleton p newValue :=
  _root_.Aeneas.SLPoC.update_singleton p oldValue newValue hContains

theorem free_singleton (p : Ptr α) (value : α)
    (hContains : contains (singleton p value) p) :
    free p (singleton p value) hContains = empty :=
  _root_.Aeneas.SLPoC.free_singleton p value hContains

end Ptr


/-! ## Specified monadic operations -/

def guardedModify {α : Type} (pre : Heap → Prop)
    (modify : (h : Heap) → pre h → α × Heap) : St α :=
  trigger ⟨α, pre, modify⟩

/-- The specification of a guarded modification is what its denotation says. -/
theorem triple_guardedModify {α : Type} {pre : Heap → Prop}
    {modify : (h : Heap) → pre h → α × Heap} {P : IPre} {Q : IPost α}
    (hWp : P ⊢ theta_ev ⟨α, pre, modify⟩ Q) :
    triple P (guardedModify pre modify) Q :=
  triple_trigger hWp

def alloc {α : Type} (value : α) : St (Ptr α) :=
  guardedModify (fun _ => True) fun h _ =>
    (Ptr.freshPtr α h, Ptr.freshHeap h value)

@[step]
theorem alloc.spec (value : α) :
    ⦃ emp ⦄ alloc value ⦃⇓ p => p ↦ value⦄ := by
  apply triple_guardedModify
  intro h _ frame hDisjoint
  let p := Ptr.freshPtr α (h ∪ frame)
  have hFresh := Ptr.fresh_freshPtr value (h ∪ frame)
  obtain ⟨hDisjointFresh, hFreshHeap⟩ :=
    Ptr.fresh_eq_singleton_union hFresh
  obtain ⟨hDisjointFreshH, hDisjointFreshFrame⟩ :=
    (PartialCommMonoid.compatible_assoc
      (Ptr.singleton p value) h frame).mpr
        ⟨hDisjoint, hDisjointFresh⟩
  exact ⟨trivial, Ptr.singleton p value ∪ h,
    hDisjointFreshFrame,
    hFreshHeap.trans
      (PartialCommMonoid.union_assoc
        hDisjointFreshH hDisjointFreshFrame).symm,
    Heap.Sub.union_left hDisjointFreshH⟩

def read {α : Type} (p : Ptr α) : St α :=
  guardedModify (fun h => Ptr.contains h p) fun h hContains =>
    (Ptr.read p h hContains, h)

@[step]
theorem read.spec (p : Ptr α) (value : α) :
    ⦃ p ↦ value ⦄ read p
      ⦃⇓ result => ⌜result = value⌝ ∗ p ↦ value⦄ := by
  apply triple_guardedModify
  intro h hSingle
  have hContains := Ptr.contains_of_sub hSingle
  intro frame hDisjoint
  have hContainsFrame := Ptr.contains_union_left (h₂ := frame) hContains
  have hReadFrame :
      Ptr.read p (h ∪ frame) hContainsFrame = value := by
    rw [Ptr.read_union_left hContains]
    obtain ⟨rest, hDisjointRest, rfl⟩ := hSingle
    have hContainsCell := Ptr.contains_singleton p value
    rw [show (hContains :
          Ptr.contains (Ptr.singleton p value ∪ rest) p) =
        Ptr.contains_union_left hContainsCell from Subsingleton.elim _ _,
      Ptr.read_union_left hContainsCell, Ptr.read_singleton]
  refine ⟨hContainsFrame, h, hDisjoint, rfl, ?_⟩
  exact (sep_pure_l _ _ h).mpr ⟨hReadFrame, hSingle⟩

def update {α : Type} (p : Ptr α) (value : α) : St Unit :=
  guardedModify (fun h => Ptr.contains h p) fun h hContains =>
    ((), Ptr.update p value h hContains)

@[step]
theorem update.spec (p : Ptr α) (oldValue newValue : α) :
    ⦃ p ↦ oldValue ⦄ update p newValue ⦃⇓ p ↦ newValue⦄ := by
  apply triple_guardedModify
  intro h hSingle
  have hContains := Ptr.contains_of_sub hSingle
  intro frame hDisjoint
  have hContainsFrame := Ptr.contains_union_left (h₂ := frame) hContains
  have hUpdateFrame :
      Ptr.update p newValue (h ∪ frame) hContainsFrame =
        Ptr.update p newValue h hContains ∪ frame := by
    simpa only [Ptr.update_union_left] using
      Ptr.update_union_left (h₂ := frame) p newValue hContains
  have hDisjointUpdated :
      PartialCommMonoid.Compatible
        (Ptr.update p newValue h hContains) frame :=
    Ptr.disjoint_update_left hDisjoint hContains
  obtain ⟨rest, hDisjointRest, rfl⟩ := hSingle
  have hContainsCell := Ptr.contains_singleton p oldValue
  have hContainsUnion := Ptr.contains_union_left (h₂ := rest) hContainsCell
  have hUpdated :
      Ptr.update p newValue (Ptr.singleton p oldValue ∪ rest) hContainsUnion =
        Ptr.singleton p newValue ∪ rest := by
    rw [Ptr.update_union_left p newValue hContainsCell, Ptr.update_singleton]
  have hDisjointRest' :
      PartialCommMonoid.Compatible (Ptr.singleton p newValue) rest := by
    have := Ptr.disjoint_update_left (value := newValue) hDisjointRest hContainsCell
    rwa [Ptr.update_singleton] at this
  refine ⟨hContainsFrame,
    Ptr.update p newValue (Ptr.singleton p oldValue ∪ rest) hContainsUnion,
    ?_, ?_, ?_⟩
  · exact Ptr.disjoint_update_left hDisjoint hContainsUnion
  · simpa only [show hContainsFrame =
        Ptr.contains_union_left hContainsUnion from Subsingleton.elim _ _,
      show hContains = hContainsUnion from Subsingleton.elim _ _] using hUpdateFrame
  · rw [hUpdated]
    exact Heap.Sub.union_left hDisjointRest'

def free {α : Type} (p : Ptr α) : St Unit :=
  guardedModify (fun h => Ptr.contains h p) fun h hContains =>
    ((), Ptr.free p h hContains)

@[step]
theorem free.spec (p : Ptr α) (value : α) :
    ⦃ p ↦ value ⦄ free p ⦃⇓ emp⦄ := by
  apply triple_guardedModify
  intro h hSingle
  have hContains := Ptr.contains_of_sub hSingle
  intro frame hDisjoint
  have hContainsFrame := Ptr.contains_union_left (h₂ := frame) hContains
  refine ⟨hContainsFrame, Ptr.free p h hContains,
    Ptr.disjoint_free_left hDisjoint hContains, ?_, trivial⟩
  simpa only [show hContainsFrame =
      Ptr.contains_union_left hContains from Subsingleton.elim _ _] using
    Ptr.free_union_left p hDisjoint hContains

def mut_to_raw {α : Type} (value : α) : St (Ptr α) :=
  alloc value

@[step]
theorem mut_to_raw.spec {α : Type} (value : α) :
    ⦃ emp ⦄ mut_to_raw value ⦃⇓ p => p ↦ value⦄ := by
  exact alloc.spec value

def end_mut_to_raw {α : Type} (p : Ptr α) : St α := do
  let value ← read p
  free p
  pure value

@[step]
theorem end_mut_to_raw.spec {α : Type} {value : α} (p : Ptr α) :
    ⦃ p ↦ value ⦄ end_mut_to_raw p ⦃⇓ result => ⌜result = value⌝⦄ := by
  unfold end_mut_to_raw
  apply triple_bind (read.spec p value)
  intro result
  apply triple_ipure
  intro hResult
  apply triple_seq (free.spec p value)
  exact triple_pure fun _ _ => hResult

end Aeneas.SLPoC
