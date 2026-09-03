module

import Mathlib.Data.Finmap
public import Aeneas.SLPoC.PCM

public section

namespace Aeneas.SLPoC

/-!
# The heap

An **address** is an allocation identifier together with a slot index into that
allocation, and a heap is a finite map from addresses to the values they hold:

```text
Loc      = AllocId × Nat
HeapCell = (α : Type) × α
Heap     = Loc ⇀ HeapCell            (finitely supported)
```

Two heaps compose when the addresses they use are disjoint, so `∪` is a plain
disjoint union: it computes, and no type equality has to be decided.  Ownership
is *slot-granular*, which is what lets one allocation be owned a part at a
time — the `(α : Type) × List α` view of an allocation is what
`Ptr.pointsToRange` owns, the list of the values at consecutive addresses, and
it splits and joins by regrouping a separating conjunction.

`MutableData/` builds the Rust view on this, and is the only place a `Ref` is
visible: [`Ptr`](MutableData/Ptr.lean) allocates a run of slots and is the
interior pointer into it, [`Buffer`](MutableData/Buffer.lean) is a bounded view
of one, and [`Array`](MutableData/Array.lean) is the array whose length is part
of its type.
-/

/- An allocation identifier is fresh and behaves like a monotonic
   counter, not a concrete address in machine memory. -/
abbrev AllocId := Nat

/-- An address: the allocation, and the slot of it this address names. -/
abbrev Loc := AllocId × Nat

/- Heap entries store the Lean type and the value of one slot. -/
abbrev HeapCell := Σ α : Type, α

private abbrev HeapImpl := Finmap fun _ : Loc => HeapCell

/-- A finite collection of dynamically typed heap cells. -/
structure Heap where
  private mk ::
  private impl : HeapImpl

private instance : Coe Heap HeapImpl := ⟨Heap.impl⟩
private instance : Coe HeapImpl Heap := ⟨Heap.mk⟩

private def Heap.lookup (h : Heap) (address : Loc) :
    Option HeapCell :=
  h.impl.lookup address

private def Heap.insert (h : Heap) (address : Loc)
    (cell : HeapCell) : Heap :=
  ⟨h.impl.insert address cell⟩

private def Heap.erase (h : Heap) (address : Loc) : Heap :=
  ⟨h.impl.erase address⟩

private def Heap.keys (h : Heap) :=
  h.impl.keys

private theorem Heap.ext_impl {h₁ h₂ : Heap}
    (hEq : h₁.impl = h₂.impl) : h₁ = h₂ := by
  cases h₁
  cases h₂
  cases hEq
  rfl

def empty : Heap := ⟨∅⟩

instance Heap.instEmptyCollection : EmptyCollection Heap := ⟨empty⟩

def Heap.union (h₁ h₂ : Heap) : Heap := ⟨h₁.impl ∪ h₂.impl⟩

instance Heap.instUnion : Union Heap := ⟨Heap.union⟩

def Heap.mem (address : Loc) (h : Heap) : Prop :=
  address ∈ h.impl

instance Heap.instMembership : Membership Loc Heap :=
  ⟨fun h address => Heap.mem address h⟩

/-- The number of slots the heap owns. -/
def Heap.size (h : Heap) : Nat :=
  h.impl.keys.card

def Heap.compatible (h₁ h₂ : Heap) : Prop :=
  Finmap.Disjoint h₁.impl h₂.impl

private theorem Heap.mem_union {address : Loc} {h₁ h₂ : Heap} :
    address ∈ h₁ ∪ h₂ ↔ address ∈ h₁ ∨ address ∈ h₂ :=
  Finmap.mem_union

private theorem Heap.lookup_union_left {address : Loc}
    {h₁ h₂ : Heap} (hMem : address ∈ h₁) :
    (h₁ ∪ h₂).lookup address = h₁.lookup address :=
  Finmap.lookup_union_left hMem

private theorem Heap.mem_insert {address insertedAddress : Loc}
    {cell : HeapCell} {h : Heap} :
    address ∈ h.insert insertedAddress cell ↔
      address = insertedAddress ∨ address ∈ h :=
  Finmap.mem_insert

private theorem Heap.mem_erase {address erasedAddress : Loc} {h : Heap} :
    address ∈ h.erase erasedAddress ↔
      address ≠ erasedAddress ∧ address ∈ h :=
  Finmap.mem_erase

private theorem Heap.insert_union {address : Loc}
    {cell : HeapCell} {h₁ h₂ : Heap} :
    (h₁ ∪ h₂).insert address cell =
      h₁.insert address cell ∪ h₂ := by
  apply Heap.ext_impl
  exact Finmap.insert_union

private theorem Heap.union_assoc' (h₁ h₂ h₃ : Heap) :
    (h₁ ∪ h₂) ∪ h₃ = h₁ ∪ (h₂ ∪ h₃) := by
  apply Heap.ext_impl
  exact Finmap.union_assoc

@[simp]
theorem Heap.empty_union (h : Heap) : empty ∪ h = h := by
  apply Heap.ext_impl
  exact Finmap.empty_union

@[simp]
theorem Heap.union_empty (h : Heap) : h ∪ empty = h := by
  apply Heap.ext_impl
  exact Finmap.union_empty

/-- Heaps form a PCM under disjoint union. -/
instance Heap.instPartialCommMonoid : PartialCommMonoid Heap where
  Compatible := Heap.compatible
  compatible_comm hCompatible := by
    exact Finmap.Disjoint.symm _ _ hCompatible
  compatible_empty_left h := by
    exact Finmap.disjoint_empty h.impl
  compatible_assoc a b c := by
    change
      Finmap.Disjoint a.impl b.impl ∧
          Finmap.Disjoint (a.impl ∪ b.impl) c.impl ↔
        Finmap.Disjoint b.impl c.impl ∧
          Finmap.Disjoint a.impl (b.impl ∪ c.impl)
    rw [Finmap.disjoint_union_left, Finmap.disjoint_union_right]
    constructor
    · rintro ⟨hab, hac, hbc⟩
      exact ⟨hbc, hab, hac⟩
    · rintro ⟨hbc, hab, hac⟩
      exact ⟨hab, hac, hbc⟩
  union_assoc _ _ := by
    apply Heap.ext_impl
    exact Finmap.union_assoc
  empty_union _ := by
    apply Heap.ext_impl
    exact Finmap.empty_union
  union_empty _ := by
    apply Heap.ext_impl
    exact Finmap.union_empty
  union_comm_of_compatible hCompatible := by
    apply Heap.ext_impl
    exact Finmap.union_comm_of_disjoint hCompatible

/-- A reference to one slot: a bare address, the type being a phantom index
that constrains specifications only. -/
@[expose]
def Ref (_ : Type) := Loc

/-- Addresses are pairs of natural numbers, so references are inhabited. -/
instance instInhabitedRef {α : Type} : Inhabited (Ref α) := ⟨((0 : AllocId), 0)⟩

instance instDecidableEqRef {α : Type} : DecidableEq (Ref α) :=
  inferInstanceAs (DecidableEq Loc)

@[expose]
def Ref.addr {α : Type} (r : Ref α) : Loc := r

/-- The allocation `r` is interior to. -/
@[expose]
def Ref.base {α : Type} (r : Ref α) : AllocId := r.addr.1

/-- The slot of that allocation `r` names. -/
@[expose]
def Ref.offset {α : Type} (r : Ref α) : Nat := r.addr.2

/-- Pointer arithmetic: same allocation, later slot. -/
@[expose]
def Ref.add {α : Type} (r : Ref α) (i : Nat) : Ref α := (r.base, r.offset + i)

@[simp] theorem Ref.base_add {α : Type} (r : Ref α) (i : Nat) :
    (r.add i).base = r.base := rfl

@[simp] theorem Ref.offset_add {α : Type} (r : Ref α) (i : Nat) :
    (r.add i).offset = r.offset + i := rfl

@[simp] theorem Ref.add_zero {α : Type} (r : Ref α) : r.add 0 = r := rfl

theorem Ref.add_add {α : Type} (r : Ref α) (i j : Nat) :
    (r.add i).add j = r.add (i + j) := by
  simp [Ref.add, Ref.base, Ref.offset, Ref.addr, Nat.add_assoc]

/-- The heap of the single slot `r`, holding `value`. -/
def singleton {α : Type} (r : Ref α) (value : α) : Heap :=
  ⟨Finmap.singleton r.addr ⟨α, value⟩⟩

theorem mem_singleton {α : Type} {r : Ref α} {value : α} {address : Loc} :
    address ∈ singleton r value ↔ address = r.addr := by
  show address ∈ (Finmap.singleton r.addr (⟨α, value⟩ : HeapCell) : HeapImpl) ↔ _
  exact Finmap.mem_singleton _ _ _

/-- `h` has a slot at `r`, and it holds a value of type `α`.  This is the
definedness guard of every operation on `r`: it is what makes the value
available as a value of `α`, and a heap operation is *stuck* without it rather
than erroneous. -/
def contains {α : Type} (h : Heap) (r : Ref α) : Prop :=
  match h.lookup r.addr with
  | none => False
  | some ⟨β, _⟩ => β = α

@[simp]
theorem not_contains_empty {α : Type} (r : Ref α) :
    ¬ contains (∅ : Heap) r := by
  change ¬ match Finmap.lookup r.addr (∅ : HeapImpl) with
    | none => False
    | some ⟨β, _⟩ => β = α
  simp

/-! ### Runs of slots

An allocation is owned a slot at a time, so the heap of a whole run is the
union of the heaps of its slots.  This is what allocation produces and what a
range assertion owns. -/

/-- The heap of the run `values`, starting at `r`. -/
@[expose]
def rangeHeap {α : Type} (r : Ref α) : List α → Heap
  | [] => empty
  | value :: rest => singleton r value ∪ rangeHeap (r.add 1) rest

@[simp] theorem rangeHeap_nil {α : Type} (r : Ref α) :
    rangeHeap r ([] : List α) = empty := rfl

@[simp] theorem rangeHeap_cons {α : Type} (r : Ref α) (value : α)
    (rest : List α) :
    rangeHeap r (value :: rest) = singleton r value ∪ rangeHeap (r.add 1) rest :=
  rfl

theorem addr_add {α : Type} (r : Ref α) (i : Nat) :
    (r.add i).addr = (r.base, r.offset + i) := rfl

@[simp] theorem rangeHeap_singleton {α : Type} (r : Ref α) (value : α) :
    rangeHeap r [value] = singleton r value := by
  rw [rangeHeap_cons, rangeHeap_nil, Heap.union_empty]

theorem mem_rangeHeap {α : Type} {r : Ref α} {values : List α} {address : Loc} :
    address ∈ rangeHeap r values ↔
      ∃ i, i < values.length ∧ address = (r.add i).addr := by
  induction values generalizing r with
  | nil =>
      simp only [rangeHeap_nil, List.length_nil, Nat.not_lt_zero, false_and,
        exists_false, iff_false]
      intro hMem
      exact (Finmap.notMem_empty (a := address)) hMem
  | cons value rest ih =>
      have hShift : ∀ i : Nat, (r.add 1).add i = r.add (i + 1) := by
        intro i; rw [Ref.add_add, Nat.add_comm]
      rw [rangeHeap_cons, Heap.mem_union, mem_singleton, ih]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, by simp, rfl⟩
        · exact ⟨i + 1, by simpa using hi, by rw [hShift]⟩
      · rintro ⟨i, hi, rfl⟩
        cases i with
        | zero => exact Or.inl rfl
        | succ j => exact Or.inr ⟨j, by simpa using hi, by rw [hShift]⟩

/-- Splitting a run into two adjacent ones splits its heap. -/
theorem rangeHeap_append {α : Type} (r : Ref α) (xs ys : List α) :
    rangeHeap r (xs ++ ys) =
      rangeHeap r xs ∪ rangeHeap (r.add xs.length) ys := by
  induction xs generalizing r with
  | nil => simp
  | cons value rest ih =>
      have hShift : (r.add 1).add rest.length = r.add (rest.length + 1) := by
        rw [Ref.add_add, Nat.add_comm]
      rw [List.cons_append, rangeHeap_cons, rangeHeap_cons, ih, List.length_cons,
        hShift, Heap.union_assoc']

/-- The two halves of a split run own disjoint slots. -/
theorem compatible_rangeHeap_append {α : Type} (r : Ref α) (xs ys : List α) :
    PartialCommMonoid.Compatible (rangeHeap r xs)
      (rangeHeap (r.add xs.length) ys) := by
  intro address hLeft hRight
  obtain ⟨i, hi, hL⟩ := mem_rangeHeap.mp hLeft
  obtain ⟨j, -, hR⟩ := mem_rangeHeap.mp hRight
  rw [Ref.add_add, addr_add] at hR
  rw [addr_add] at hL
  have hOffset : r.offset + i = r.offset + (xs.length + j) :=
    (congrArg Prod.snd hL).symm.trans (congrArg Prod.snd hR)
  omega

/-! ## Allocation -/

/-- The allocation identifier this heap will hand out next: one past every
identifier it uses.  Allocation is deterministic, which is what lets a program
be *run* and not only related to its outcomes. -/
def freshBase (h : Heap) : AllocId :=
  (h.keys.image Prod.fst).sup id + 1

/-- The address the next allocation starts at. -/
def freshRef (α : Type) (h : Heap) : Ref α := (freshBase h, 0)

theorem not_mem_freshBase {h : Heap} {address : Loc}
    (hBase : address.1 = freshBase h) : address ∉ h := by
  intro hMem
  have hMemKeys : address ∈ h.keys := Finmap.mem_keys.mpr hMem
  have hImage : freshBase h ∈ h.keys.image Prod.fst :=
    Finset.mem_image.mpr ⟨_, hMemKeys, hBase⟩
  have hLe : freshBase h ≤ (h.keys.image Prod.fst).sup id :=
    Finset.le_sup (f := fun a : AllocId => a) hImage
  have hSucc : (h.keys.image Prod.fst).sup id + 1 ≤
      (h.keys.image Prod.fst).sup id := hLe
  exact Nat.not_succ_le_self _ hSucc

/-- The run a fresh allocation occupies is disjoint from everything the heap
already owns. -/
theorem compatible_freshRef {α : Type} (h : Heap) (values : List α) :
    PartialCommMonoid.Compatible (rangeHeap (freshRef α h) values) h := by
  intro address hFresh hMem
  obtain ⟨i, -, rfl⟩ := mem_rangeHeap.mp hFresh
  exact not_mem_freshBase (h := h) rfl hMem

/-- The heap `freshRef` allocates into. -/
def freshHeap {α : Type} (h : Heap) (values : List α) : Heap :=
  rangeHeap (freshRef α h) values ∪ h

/-! ## Sub-heaps

The assertions of `Aeneas.SLPoC.WP` are *affine*: they own the cells they
describe and say nothing about the rest of the heap.  Semantically that means
they are closed under the extension order below, the way Iris's `uPred` is
monotone in its resource. -/

/-- `Heap.Sub h h'`: `h'` is `h` extended with cells that `h` does not own. -/
def Heap.Sub (h h' : Heap) : Prop :=
  ∃ rest, PartialCommMonoid.Compatible h rest ∧ h' = h ∪ rest

namespace Heap.Sub

@[refl]
theorem refl (h : Heap) : Heap.Sub h h :=
  ⟨∅,
    PartialCommMonoid.compatible_comm
      (PartialCommMonoid.compatible_empty_left h),
    (PartialCommMonoid.union_empty h).symm⟩

theorem trans {h₁ h₂ h₃ : Heap} (hSub₁₂ : Heap.Sub h₁ h₂)
    (hSub₂₃ : Heap.Sub h₂ h₃) : Heap.Sub h₁ h₃ := by
  obtain ⟨rest₁, hCompatible₁, rfl⟩ := hSub₁₂
  obtain ⟨rest₂, hCompatible₂, rfl⟩ := hSub₂₃
  have ⟨_, hCompatible⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ rest₁ rest₂).mp
      ⟨hCompatible₁, hCompatible₂⟩
  exact ⟨rest₁ ∪ rest₂, hCompatible,
    PartialCommMonoid.union_assoc hCompatible₁ hCompatible₂⟩

theorem of_empty (h : Heap) : Heap.Sub empty h :=
  ⟨h, PartialCommMonoid.compatible_empty_left h,
    (PartialCommMonoid.empty_union h).symm⟩

theorem union_left {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Sub h₁ (h₁ ∪ h₂) :=
  ⟨h₂, hCompatible, rfl⟩

theorem union_right {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Sub h₂ (h₁ ∪ h₂) :=
  ⟨h₁, PartialCommMonoid.compatible_comm hCompatible,
    PartialCommMonoid.union_comm_of_compatible hCompatible⟩

/-- An extension of a split heap splits the same way, the extra cells going to
the right-hand side. -/
theorem split {h₁ h₂ h' : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hSub : Heap.Sub (h₁ ∪ h₂) h') :
    ∃ h₂', PartialCommMonoid.Compatible h₁ h₂' ∧
      h' = h₁ ∪ h₂' ∧ Heap.Sub h₂ h₂' := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hCompatible₂, hCompatible₁⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ h₂ rest).mp
      ⟨hCompatible, hCompatibleRest⟩
  exact ⟨h₂ ∪ rest, hCompatible₁,
    PartialCommMonoid.union_assoc hCompatible hCompatibleRest,
    ⟨rest, hCompatible₂, rfl⟩⟩

/-- A heap disjoint from an extension is disjoint from the heap extended. -/
theorem disjoint_of_sub {h h' frame : Heap} (hSub : Heap.Sub h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    PartialCommMonoid.Compatible h frame := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hRestFrame, hRestFrame'⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hCompatibleRest, hCompatible⟩
  have ⟨hFrame, _⟩ :=
    (PartialCommMonoid.compatible_assoc rest frame h).mp
      ⟨hRestFrame,
        PartialCommMonoid.compatible_comm hRestFrame'⟩
  exact PartialCommMonoid.compatible_comm hFrame

/-- Extending on one side of a union extends the union. -/
theorem union_mono_left {h h' frame : Heap} (hSub : Heap.Sub h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    Heap.Sub (h ∪ frame) (h' ∪ frame) := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hRestFrame, hRestFrame'⟩ :=
    (PartialCommMonoid.compatible_assoc h rest frame).mp
      ⟨hCompatibleRest, hCompatible⟩
  have hFrameRest := PartialCommMonoid.compatible_comm hRestFrame
  have hFrameRest' :
      PartialCommMonoid.Compatible h (frame ∪ rest) := by
    rw [← PartialCommMonoid.union_comm_of_compatible hRestFrame]
    exact hRestFrame'
  have ⟨hCompatibleFrame, hCompatibleCombined⟩ :=
    (PartialCommMonoid.compatible_assoc h frame rest).mpr
      ⟨hFrameRest, hFrameRest'⟩
  refine ⟨rest, hCompatibleCombined, ?_⟩
  calc
    (h ∪ rest) ∪ frame = h ∪ (rest ∪ frame) :=
      PartialCommMonoid.union_assoc hCompatibleRest hCompatible
    _ = h ∪ (frame ∪ rest) := congrArg (h ∪ ·)
      (PartialCommMonoid.union_comm_of_compatible hRestFrame)
    _ = (h ∪ frame) ∪ rest :=
      (PartialCommMonoid.union_assoc
        hCompatibleFrame hCompatibleCombined).symm

/-- Two extensions of compatible heaps extend their union. -/
theorem union_mono {A B h₁ h₂ : Heap}
    (hSub₁ : Heap.Sub A h₁) (hSub₂ : Heap.Sub B h₂)
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Sub (A ∪ B) (h₁ ∪ h₂) := by
  have hAh₂ : PartialCommMonoid.Compatible A h₂ :=
    Heap.Sub.disjoint_of_sub hSub₁ hCompatible
  have hAB : PartialCommMonoid.Compatible A B :=
    PartialCommMonoid.compatible_comm
      (Heap.Sub.disjoint_of_sub hSub₂
        (PartialCommMonoid.compatible_comm hAh₂))
  have hStep₁ : Heap.Sub (B ∪ A) (h₂ ∪ A) :=
    Heap.Sub.union_mono_left hSub₂ (PartialCommMonoid.compatible_comm hAh₂)
  have hStep₂ : Heap.Sub (A ∪ B) (A ∪ h₂) := by
    rw [PartialCommMonoid.union_comm_of_compatible hAB,
      PartialCommMonoid.union_comm_of_compatible hAh₂]
    exact hStep₁
  exact hStep₂.trans (Heap.Sub.union_mono_left hSub₁ hCompatible)

end Heap.Sub

namespace Heap

/-- The value the slot `r` holds.  The guard supplies the type equality, so no
default value has to be invented and this computes. -/
def read {α : Type} (r : Ref α) (h : Heap)
    (hContains : contains h r) : α :=
  match hlookup : h.lookup r.addr with
  | none => by simp [contains, hlookup] at hContains
  | some ⟨β, value⟩ => by
      have htype : β = α := by
        simpa [contains, hlookup] using hContains
      exact htype ▸ value

/-- Replace the value the slot `r` holds. -/
def update {α : Type} (r : Ref α) (value : α) (h : Heap)
    (_ : contains h r) : Heap :=
  h.insert r.addr ⟨α, value⟩

/-- Release the slot `r`: the address goes away, so what a heap still holds is
exactly what has not been freed. -/
def free {α : Type} (r : Ref α) (h : Heap)
    (_ : contains h r) : Heap :=
  h.erase r.addr

end Heap

theorem mem_of_contains {α : Type} {h : Heap} {r : Ref α}
    (hContains : contains h r) : r.addr ∈ h := by
  unfold contains at hContains
  split at hContains
  · contradiction
  · rename_i cell hLookup
    exact Finmap.mem_of_lookup_eq_some hLookup

/-- Two heaps that both contain the cell `r` are not disjoint. -/
theorem disjoint_contains_false {α : Type} {h₁ h₂ : Heap} {r : Ref α}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains₁ : contains h₁ r)
    (hContains₂ : contains h₂ r) : False :=
  hCompatible r.addr (mem_of_contains hContains₁)
    (mem_of_contains hContains₂)

theorem contains_union_left {α : Type} {h₁ h₂ : Heap} {r : Ref α}
    (hContains : contains h₁ r) : contains (h₁ ∪ h₂) r := by
  have hMem : r.addr ∈ h₁ := mem_of_contains hContains
  unfold contains at hContains ⊢
  rw [Heap.lookup_union_left hMem]
  exact hContains

theorem read_union_left {α : Type} {h₁ h₂ : Heap} {r : Ref α}
    (hContains : contains h₁ r) :
    Heap.read r (h₁ ∪ h₂) (contains_union_left hContains) =
      Heap.read r h₁ hContains := by
  have hMem : r.addr ∈ h₁ := by
    unfold contains at hContains
    split at hContains
    · contradiction
    · rename_i cell hLookup
      exact Finmap.mem_of_lookup_eq_some hLookup
  unfold Heap.read
  split
  · rename_i hLookup
    have hContainsUnion := contains_union_left (h₂ := h₂) hContains
    simp [contains, hLookup] at hContainsUnion
  · rename_i β value hLookup
    split
    · rename_i hLookup₁
      simp [contains, hLookup₁] at hContains
    · rename_i β₁ value₁ hLookup₁
      have hCells :
          (⟨β, value⟩ : HeapCell) = ⟨β₁, value₁⟩ := by
        apply Option.some.inj
        exact hLookup.symm.trans
          ((Finmap.lookup_union_left hMem).trans hLookup₁)
      cases hCells
      rfl

theorem update_union_left {α : Type} {h₁ h₂ : Heap}
    (r : Ref α) (value : α) (hContains : contains h₁ r) :
    Heap.update r value (h₁ ∪ h₂) (contains_union_left hContains) =
      Heap.update r value h₁ hContains ∪ h₂ := by
  exact Heap.insert_union

theorem disjoint_update_left {α : Type} {r : Ref α} {value : α}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ r) :
    PartialCommMonoid.Compatible
      (Heap.update r value h₁ hContains) h₂ := by
  have hUnallocated : r.addr ∉ h₂ := by
    intro hMem₂
    unfold contains at hContains
    split at hContains
    · contradiction
    · rename_i cell hLookup
      exact hCompatible r.addr
        (Finmap.mem_of_lookup_eq_some hLookup) hMem₂
  intro address hMem₁ hMem₂
  change address ∈ h₁.insert r.addr ⟨α, value⟩ at hMem₁
  rw [Heap.mem_insert] at hMem₁
  rcases hMem₁ with hEq | hMem₁
  · exact hUnallocated (hEq ▸ hMem₂)
  · exact hCompatible address hMem₁ hMem₂

theorem disjoint_free_left {α : Type} {r : Ref α}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ r) :
    PartialCommMonoid.Compatible (Heap.free r h₁ hContains) h₂ := by
  intro address hMem₁ hMem₂
  change address ∈ h₁.erase r.addr at hMem₁
  exact hCompatible address (Heap.mem_erase.mp hMem₁).right hMem₂

theorem free_union_left {α : Type} {h₁ h₂ : Heap}
    (r : Ref α) (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ r) :
    Heap.free r (h₁ ∪ h₂) (contains_union_left hContains) =
      Heap.free r h₁ hContains ∪ h₂ := by
  have hMem : r.addr ∈ h₁ := by
    unfold contains at hContains
    split at hContains
    · contradiction
    · rename_i cell hLookup
      exact Finmap.mem_of_lookup_eq_some hLookup
  have hNotMem : r.addr ∉ h₂ :=
    fun hMem₂ => hCompatible r.addr hMem hMem₂
  unfold Heap.free
  apply Heap.ext_impl
  apply Finmap.ext_lookup
  intro address
  change
    Finmap.lookup address (h₁.impl ∪ h₂.impl |>.erase r.addr) =
      Finmap.lookup address (h₁.impl.erase r.addr ∪ h₂.impl)
  by_cases hEq : address = r.addr
  · subst address
    rw [Finmap.lookup_erase, Finmap.lookup_union_right
      Finmap.notMem_erase_self]
    exact Finmap.lookup_eq_none.mpr hNotMem |>.symm
  · rw [Finmap.lookup_erase_ne hEq]
    by_cases hMem₁ : address ∈ h₁
    · rw [Finmap.lookup_union_left hMem₁,
        Finmap.lookup_union_left (Finmap.mem_erase.mpr ⟨hEq, hMem₁⟩),
        Finmap.lookup_erase_ne hEq]
    · rw [Finmap.lookup_union_right hMem₁,
        Finmap.lookup_union_right
          (fun hMem => hMem₁ (Finmap.mem_erase.mp hMem).right)]

/-- Two cells at different references are disjoint. -/
theorem disjoint_singleton {α : Type} {r s : Ref α} {value₁ value₂ : α}
    (hNe : r ≠ s) :
    PartialCommMonoid.Compatible
      (singleton r value₁) (singleton s value₂) := by
  intro address hMem₁ hMem₂
  change address ∈
    (Finmap.singleton r.addr ⟨α, value₁⟩ : HeapImpl) at hMem₁
  change address ∈
    (Finmap.singleton s.addr ⟨α, value₂⟩ : HeapImpl) at hMem₂
  rw [Finmap.mem_singleton] at hMem₁
  rw [Finmap.mem_singleton] at hMem₂
  exact hNe (hMem₁.symm.trans hMem₂)

theorem contains_singleton {α : Type} (r : Ref α) (value : α) :
    contains (singleton r value) r := by
  simp [contains, singleton, Heap.lookup]

theorem read_singleton {α : Type} (r : Ref α) (value : α)
    (hContains : contains (singleton r value) r) :
    Heap.read r (singleton r value) hContains = value := by
  unfold Heap.read
  split
  · rename_i hLookup
    change
      Finmap.lookup r.addr
          (Finmap.singleton r.addr ⟨α, value⟩ : HeapImpl) =
        none at hLookup
    rw [Finmap.lookup_singleton_eq] at hLookup
    contradiction
  · rename_i β stored hLookup
    change
      Finmap.lookup r.addr
          (Finmap.singleton r.addr ⟨α, value⟩ : HeapImpl) =
        some (⟨β, stored⟩ : HeapCell) at hLookup
    rw [Finmap.lookup_singleton_eq] at hLookup
    cases hLookup
    rfl

theorem update_singleton {α : Type} (r : Ref α)
    (oldValue newValue : α)
    (hContains : contains (singleton r oldValue) r) :
    Heap.update r newValue (singleton r oldValue) hContains =
      singleton r newValue := by
  apply Heap.ext_impl
  simp [Heap.update, singleton, Heap.insert]

theorem free_singleton {α : Type} (r : Ref α) (value : α)
    (hContains : contains (singleton r value) r) :
    Heap.free r (singleton r value) hContains = empty := by
  unfold Heap.free
  apply Heap.ext_impl
  apply Finmap.ext_lookup
  intro address
  change
    Finmap.lookup address
        ((Finmap.singleton r.addr ⟨α, value⟩ : HeapImpl).erase
          r.addr) =
      Finmap.lookup address (∅ : HeapImpl)
  by_cases hEq : address = r.addr
  · subst address
    simp
  · rw [Finmap.lookup_erase_ne hEq]
    simp only [Finmap.lookup_empty]
    apply Finmap.lookup_eq_none.mpr
    simpa [singleton, Finmap.mem_singleton] using hEq

/-! ## What a points-to assertion gives

An affine assertion owns the slots it describes and says nothing about the
others, so it is closed under `Heap.Sub`.  These are the lemmas that turn such
an assertion into the guard of an operation, and back. -/

/-- A heap that extends a slot owns that slot: this is what an affine points-to
assertion gives, the rest of the heap being unconstrained. -/
theorem contains_of_sub {α : Type} {r : Ref α} {value : α} {h : Heap}
    (hSub : Heap.Sub (singleton r value) h) : contains h r := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact contains_union_left (contains_singleton r value)

/-- The value a heap extending `singleton r value` holds at `r` is `value`
itself: slots compose by disjoint union, so nothing else can hold that slot and
the points-to assertion is exact. -/
theorem read_of_sub {α : Type} {r : Ref α} {value : α} {h : Heap}
    (hSub : Heap.Sub (singleton r value) h)
    (hContains : contains h r) : Heap.read r h hContains = value := by
  obtain ⟨rest, hCompatible, rfl⟩ := hSub
  have hContainsSingleton := contains_singleton r value
  rw [show hContains = contains_union_left hContainsSingleton from
      Subsingleton.elim _ _,
    read_union_left hContainsSingleton, read_singleton]

end Aeneas.SLPoC
