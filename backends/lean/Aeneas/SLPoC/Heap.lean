module

public import Aeneas.SLPoC.PCM

@[expose] public section

namespace Aeneas.SLPoC

/-!
# The heap

Following Pulse, a heap cell stores a *partial commutative monoid* together
with a value of its carrier, and heaps compose by composing the cells they
share.  A reference is a bare address indexed by the carrier and the PCM, and
two heaps may own different fragments of the same cell — which is what lets a
single allocation be split into non-overlapping ranges.
-/

/- An allocation identifier is fresh and behaves like a monotonic
   counter, not a concrete address in machine memory. -/
abbrev AllocId := Nat

/-! ## Cells -/

/-- A heap cell: its carrier type, the PCM its fragments compose with, and the
value it currently holds. -/
structure Cell : Type 1 where
  Carrier : Type
  pcm : PCM Carrier
  value : Carrier

namespace Cell

/-- Two cells compose only when their carriers and PCMs agree and their values
compose. -/
inductive Composable : Cell → Cell → Prop where
  | intro {α : Type} {p : PCM α} {x y : α} (hComposable : p.Composable x y) :
      Composable ⟨α, p, x⟩ ⟨α, p, y⟩

theorem Composable.carrier_eq {c₁ c₂ : Cell} (hComposable : Composable c₁ c₂) :
    c₁.Carrier = c₂.Carrier := by
  cases hComposable; rfl

/-- Composability with a cell of known carrier and PCM pins down the other
cell. -/
theorem composable_left_iff {α : Type} {p : PCM α} {x : α} {c : Cell} :
    Composable ⟨α, p, x⟩ c ↔ ∃ y : α, c = ⟨α, p, y⟩ ∧ p.Composable x y := by
  constructor
  · intro hComposable
    cases hComposable with
    | intro h => exact ⟨_, rfl, h⟩
  · rintro ⟨y, rfl, h⟩
    exact .intro h

theorem composable_comm {c₁ c₂ : Cell} (hComposable : Composable c₁ c₂) :
    Composable c₂ c₁ := by
  cases hComposable with
  | intro h => exact .intro (PCM.composable_comm _ h)

/-- Composition of two cells; junk outside `Composable`, as `op` is in a PCM. -/
noncomputable def op (c₁ c₂ : Cell) : Cell :=
  open Classical in
  if hComposable : Composable c₁ c₂ then
    ⟨c₁.Carrier, c₁.pcm,
      c₁.pcm.op c₁.value (cast hComposable.carrier_eq.symm c₂.value)⟩
  else c₁

theorem op_mk {α : Type} {p : PCM α} {x y : α} (hComposable : p.Composable x y) :
    op ⟨α, p, x⟩ ⟨α, p, y⟩ = ⟨α, p, p.op x y⟩ := by
  rw [op, dif_pos (Composable.intro hComposable)]
  exact congrArg (fun value => (⟨α, p, p.op x value⟩ : Cell))
    (eq_of_heq (cast_heq _ _))

theorem op_comm {c₁ c₂ : Cell} (hComposable : Composable c₁ c₂) :
    op c₁ c₂ = op c₂ c₁ := by
  cases hComposable with
  | intro h =>
      rw [op_mk h, op_mk (PCM.composable_comm _ h), PCM.op_comm _ h]

theorem composable_assoc (c₁ c₂ c₃ : Cell) :
    (Composable c₁ c₂ ∧ Composable (op c₁ c₂) c₃) ↔
      (Composable c₂ c₃ ∧ Composable c₁ (op c₂ c₃)) := by
  constructor
  · rintro ⟨h₁₂, h₁₂₃⟩
    cases h₁₂ with
    | @intro α p x y hxy =>
        rw [op_mk hxy, composable_left_iff] at h₁₂₃
        obtain ⟨z, rfl, hz⟩ := h₁₂₃
        obtain ⟨hyz, hxyz, -⟩ := p.assoc_right hxy hz
        exact ⟨.intro hyz, by rw [op_mk hyz]; exact .intro hxyz⟩
  · rintro ⟨h₂₃, h₁₂₃⟩
    cases h₂₃ with
    | @intro α p y z hyz =>
        rw [op_mk hyz] at h₁₂₃
        obtain ⟨x, rfl, hx⟩ := composable_left_iff.mp (composable_comm h₁₂₃)
        obtain ⟨hxy, hxyz, -⟩ := p.assoc_left hyz (PCM.composable_comm _ hx)
        exact ⟨.intro hxy, by rw [op_mk hxy]; exact .intro hxyz⟩

/-- Whether this cell still owns anything. -/
def isOne (c : Cell) : Bool := c.pcm.isOne c.value

/-! ### Cells lifted to the empty slot

Composition of heaps is composition of cells, with the missing cell as the
unit. -/

def OComposable : Option Cell → Option Cell → Prop
  | some c₁, some c₂ => Composable c₁ c₂
  | _, _ => True

noncomputable def oop : Option Cell → Option Cell → Option Cell
  | some c₁, some c₂ => some (op c₁ c₂)
  | some c₁, none => some c₁
  | none, other => other

@[simp] theorem oop_none_left (o : Option Cell) : oop none o = o := rfl

@[simp] theorem oop_none_right (o : Option Cell) : oop o none = o := by
  cases o <;> rfl

@[simp] theorem oop_some_some (c₁ c₂ : Cell) :
    oop (some c₁) (some c₂) = some (op c₁ c₂) := rfl

@[simp] theorem oComposable_none_left (o : Option Cell) :
    OComposable none o := by cases o <;> trivial

@[simp] theorem oComposable_none_right (o : Option Cell) :
    OComposable o none := by cases o <;> trivial

@[simp] theorem oComposable_some_some (c₁ c₂ : Cell) :
    OComposable (some c₁) (some c₂) ↔ Composable c₁ c₂ := Iff.rfl

@[simp] theorem isSome_oop (o₁ o₂ : Option Cell) :
    (oop o₁ o₂).isSome = (o₁.isSome || o₂.isSome) := by
  cases o₁ <;> cases o₂ <;> rfl

theorem oComposable_comm {o₁ o₂ : Option Cell} (hComposable : OComposable o₁ o₂) :
    OComposable o₂ o₁ := by
  cases o₁ <;> cases o₂ <;> simp_all [composable_comm]

theorem oop_comm {o₁ o₂ : Option Cell} (hComposable : OComposable o₁ o₂) :
    oop o₁ o₂ = oop o₂ o₁ := by
  cases o₁ <;> cases o₂ <;> simp_all
  exact op_comm hComposable

theorem oComposable_assoc (o₁ o₂ o₃ : Option Cell) :
    (OComposable o₁ o₂ ∧ OComposable (oop o₁ o₂) o₃) ↔
      (OComposable o₂ o₃ ∧ OComposable o₁ (oop o₂ o₃)) := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;>
    simp_all [composable_assoc]

theorem oop_assoc {o₁ o₂ o₃ : Option Cell} (h₁₂ : OComposable o₁ o₂)
    (h₁₂₃ : OComposable (oop o₁ o₂) o₃) :
    oop (oop o₁ o₂) o₃ = oop o₁ (oop o₂ o₃) := by
  cases o₁ <;> cases o₂ <;> cases o₃ <;> simp_all
  rename_i c₁ c₂ c₃
  cases h₁₂ with
  | @intro α p x y hxy =>
      rw [op_mk hxy] at h₁₂₃ ⊢
      rw [composable_left_iff] at h₁₂₃
      obtain ⟨z, rfl, hz⟩ := h₁₂₃
      obtain ⟨hyz, hxyz, hEq⟩ := p.assoc_right hxy hz
      rw [op_mk hz, op_mk hyz, op_mk hxyz, hEq]

end Cell

/-! ## Heaps -/

/-- A finite collection of dynamically typed heap cells.  The support is
carried as data so that allocating a fresh address and counting the cells that
still own something both compute. -/
structure Heap : Type 1 where
  cell : AllocId → Option Cell
  support : Finset AllocId
  mem_support : ∀ a, a ∈ support ↔ (cell a).isSome

namespace Heap

@[ext]
theorem ext {h₁ h₂ : Heap} (hCell : ∀ a, h₁.cell a = h₂.cell a) : h₁ = h₂ := by
  obtain ⟨cell₁, support₁, hSupport₁⟩ := h₁
  obtain ⟨cell₂, support₂, hSupport₂⟩ := h₂
  have hEq : cell₁ = cell₂ := funext hCell
  subst hEq
  have : support₁ = support₂ := by
    apply Finset.ext
    intro a
    rw [hSupport₁ a, hSupport₂ a]
  subst this
  rfl

end Heap

def empty : Heap where
  cell _ := none
  support := ∅
  mem_support := by simp

instance Heap.instEmptyCollection : EmptyCollection Heap := ⟨empty⟩

@[simp]
theorem Heap.cell_empty (a : AllocId) : (empty : Heap).cell a = none := rfl

@[simp]
theorem Heap.emptyCollection_eq : ((∅ : Heap)) = empty := rfl

namespace Heap

/-- Replace the cell at `a`. -/
def insert (a : AllocId) (c : Cell) (h : Heap) : Heap where
  cell b := if b = a then some c else h.cell b
  support := Insert.insert a h.support
  mem_support := by
    intro b
    by_cases hb : b = a <;> simp [hb, h.mem_support]

@[simp]
theorem cell_insert (a : AllocId) (c : Cell) (h : Heap) (b : AllocId) :
    (h.insert a c).cell b = if b = a then some c else h.cell b := rfl

/-- The union of two heaps composes the cells they share. -/
noncomputable def union (h₁ h₂ : Heap) : Heap where
  cell a := Cell.oop (h₁.cell a) (h₂.cell a)
  support := h₁.support ∪ h₂.support
  mem_support := by
    intro a
    simp [h₁.mem_support a, h₂.mem_support a]

noncomputable instance instUnion : Union Heap := ⟨Heap.union⟩

@[simp]
theorem cell_union (h₁ h₂ : Heap) (a : AllocId) :
    (h₁ ∪ h₂).cell a = Cell.oop (h₁.cell a) (h₂.cell a) := rfl

/-- The left-biased union of heaps with disjoint addresses.  It agrees with `∪`
there, and unlike `∪` it computes: composing two cells has to decide whether
their carrier types agree. -/
def disjointUnion (h₁ h₂ : Heap) : Heap where
  cell a := match h₁.cell a with | some c => some c | none => h₂.cell a
  support := h₁.support ∪ h₂.support
  mem_support := by
    intro a
    simp only [Finset.mem_union, h₁.mem_support a, h₂.mem_support a]
    cases h₁.cell a <;> simp

def mem (a : AllocId) (h : Heap) : Prop := (h.cell a).isSome = true

instance instMembership : Membership AllocId Heap :=
  ⟨fun h a => Heap.mem a h⟩

theorem mem_iff {a : AllocId} {h : Heap} :
    a ∈ h ↔ (h.cell a).isSome = true := Iff.rfl

theorem cell_eq_none_of_not_mem {a : AllocId} {h : Heap} (hMem : a ∉ h) :
    h.cell a = none := by
  cases hCell : h.cell a with
  | none => rfl
  | some c => exact absurd (mem_iff.mpr (by rw [hCell]; rfl)) hMem

theorem disjointUnion_eq_union {h₁ h₂ : Heap}
    (hDisjoint : ∀ a, a ∈ h₁ → a ∉ h₂) : h₁.disjointUnion h₂ = h₁ ∪ h₂ := by
  apply Heap.ext
  intro a
  rw [cell_union]
  show (match h₁.cell a with | some c => some c | none => h₂.cell a) = _
  cases hCell₁ : h₁.cell a with
  | none => simp
  | some c₁ =>
      have : h₂.cell a = none :=
        cell_eq_none_of_not_mem (hDisjoint a (mem_iff.mpr (by rw [hCell₁]; rfl)))
      rw [this]
      simp

/-- The number of cells that still own something.  Deallocation releases the
fragment a cell holds instead of removing the address, exactly as in Pulse, so
this and not the number of addresses is what tells a leak from a clean run. -/
def size (h : Heap) : Nat :=
  (h.support.filter fun a =>
    (match h.cell a with | some c => !c.isOne | none => false) = true).card

def compatible (h₁ h₂ : Heap) : Prop :=
  ∀ a, Cell.OComposable (h₁.cell a) (h₂.cell a)

@[simp]
theorem empty_union (h : Heap) : empty ∪ h = h := by
  apply Heap.ext; intro a; simp

@[simp]
theorem union_empty (h : Heap) : h ∪ empty = h := by
  apply Heap.ext; intro a; simp

theorem union_comm_of_compatible {h₁ h₂ : Heap} (hCompatible : compatible h₁ h₂) :
    h₁ ∪ h₂ = h₂ ∪ h₁ :=
  Heap.ext fun a => by simpa using Cell.oop_comm (hCompatible a)

/-- Heaps form a PCM under composition of the cells they share. -/
noncomputable instance instPartialCommMonoid : PartialCommMonoid Heap where
  Compatible := Heap.compatible
  compatible_comm hCompatible a := Cell.oComposable_comm (hCompatible a)
  compatible_empty_left h a := by simp
  compatible_assoc a b c := by
    constructor
    · rintro ⟨hab, habc⟩
      refine ⟨fun addr => ?_, fun addr => ?_⟩
      · exact ((Cell.oComposable_assoc (a.cell addr) (b.cell addr)
          (c.cell addr)).mp ⟨hab addr, by simpa using habc addr⟩).1
      · simpa using ((Cell.oComposable_assoc (a.cell addr) (b.cell addr)
          (c.cell addr)).mp ⟨hab addr, by simpa using habc addr⟩).2
    · rintro ⟨hbc, habc⟩
      refine ⟨fun addr => ?_, fun addr => ?_⟩
      · exact ((Cell.oComposable_assoc (a.cell addr) (b.cell addr)
          (c.cell addr)).mpr ⟨hbc addr, by simpa using habc addr⟩).1
      · simpa using ((Cell.oComposable_assoc (a.cell addr) (b.cell addr)
          (c.cell addr)).mpr ⟨hbc addr, by simpa using habc addr⟩).2
  union_assoc {a b c} hab habc :=
    Heap.ext fun addr => by
      simpa using Cell.oop_assoc (hab addr) (by simpa using habc addr)
  empty_union := empty_union
  union_empty := union_empty
  union_comm_of_compatible := union_comm_of_compatible

theorem compatible_iff {h₁ h₂ : Heap} :
    PartialCommMonoid.Compatible h₁ h₂ ↔
      ∀ a, Cell.OComposable (h₁.cell a) (h₂.cell a) := Iff.rfl

end Heap

/-! ## References -/

/-- A reference to a cell with carrier `α` whose fragments compose with `p`.
Every reference is a bare address: the carrier and the PCM are phantom indices
that constrain specifications only. -/
def Ref (_α : Type) (_p : PCM _α) := AllocId

/-- Allocation identifiers are natural numbers, so references are inhabited. -/
instance instInhabitedRef {α : Type} {p : PCM α} : Inhabited (Ref α p) :=
  ⟨(0 : AllocId)⟩

instance instDecidableEqRef {α : Type} {p : PCM α} : DecidableEq (Ref α p) :=
  inferInstanceAs (DecidableEq AllocId)

def Ref.addr {α : Type} {p : PCM α} (r : Ref α p) : AllocId := r

variable {α : Type} {p : PCM α}

/-- The heap made of the single cell `r`, holding the fragment `x`. -/
def singleton (r : Ref α p) (x : α) : Heap :=
  Heap.insert r.addr ⟨α, p, x⟩ empty

@[simp]
theorem cell_singleton (r : Ref α p) (x : α) (a : AllocId) :
    (singleton r x).cell a = if a = r.addr then some ⟨α, p, x⟩ else none := rfl

def unallocated (h : Heap) (r : Ref α p) : Prop := r.addr ∉ h

def fresh (h : Heap) (r : Ref α p) (x : α) (h' : Heap) : Prop :=
  unallocated h r ∧ h' = h.insert r.addr ⟨α, p, x⟩

/-- `h` has a cell at `r`, made with the carrier and the PCM `r` is indexed by.
This is the definedness guard of every operation on `r`: it is what makes the
value of the cell available as a value of `α`, and a heap operation is *stuck*
without it rather than erroneous. -/
def contains (h : Heap) (r : Ref α p) : Prop :=
  match h.cell r.addr with
  | none => False
  | some c => c.Carrier = α ∧ HEq c.pcm p

@[simp]
theorem not_contains_empty (r : Ref α p) : ¬ contains (∅ : Heap) r := by
  simp [contains]

theorem mem_of_contains {h : Heap} {r : Ref α p} (hContains : contains h r) :
    r.addr ∈ h := by
  unfold contains at hContains
  split at hContains
  · contradiction
  · rename_i hCell
    simp [Heap.mem_iff, hCell]

namespace Heap

/-- Read the fragment the cell `r` holds.  The guard supplies the carrier
equality, so no default value has to be invented and this computes. -/
def select (r : Ref α p) (h : Heap) (hContains : contains h r) : α :=
  match hCell : h.cell r.addr with
  | none => by rw [contains, hCell] at hContains; exact hContains.elim
  | some c => by
      have hCarrier : c.Carrier = α := by
        rw [contains, hCell] at hContains; exact hContains.1
      exact cast hCarrier c.value

/-- The fragment the cell `r` holds, or the unit when there is no such cell.
Unlike `select` this needs no guard, at the price of deciding an equality of
types: it is used to state the laws, never to run a program. -/
noncomputable def get (r : Ref α p) (h : Heap) : α :=
  open Classical in
  if hContains : contains h r then h.select r hContains else p.one

theorem get_eq_select (r : Ref α p) (h : Heap) (hContains : contains h r) :
    h.get r = h.select r hContains :=
  dif_pos hContains

theorem get_of_not_contains {r : Ref α p} {h : Heap}
    (hContains : ¬ contains h r) : h.get r = p.one :=
  dif_neg hContains

theorem get_of_cell {r : Ref α p} {h : Heap} {x : α}
    (hCell : h.cell r.addr = some ⟨α, p, x⟩) : h.get r = x := by
  have hContains : contains h r := by rw [contains, hCell]; exact ⟨rfl, HEq.rfl⟩
  rw [get_eq_select r h hContains, select]
  split
  · rename_i hCell'; rw [hCell] at hCell'; exact absurd hCell' (by simp)
  · rename_i c hCell'
    rw [hCell] at hCell'
    cases hCell'
    rfl

/-- Update the fragment the cell `r` holds. -/
def upd (r : Ref α p) (f : α → α) (h : Heap) (hContains : contains h r) :
    Heap :=
  h.insert r.addr ⟨α, p, f (h.select r hContains)⟩

theorem cell_upd (r : Ref α p) (f : α → α) (h : Heap)
    (hContains : contains h r) (a : AllocId) :
    (h.upd r f hContains).cell a =
      if a = r.addr then some ⟨α, p, f (h.get r)⟩ else h.cell a := by
  rw [upd, cell_insert, get_eq_select r h hContains]

end Heap

/-! ## Allocation -/

/-- The address the next allocation returns: one past every address in use.
Allocation is deterministic, which is what lets a program be *run* and not only
related to its outcomes. -/
def freshRef (α : Type) (p : PCM α) (h : Heap) : Ref α p :=
  h.support.sup id + 1

/-- The heap `freshRef` allocates into. -/
def freshHeap {α : Type} {p : PCM α} (h : Heap) (x : α) : Heap :=
  h.insert (freshRef α p h).addr ⟨α, p, x⟩

theorem fresh_freshRef (x : α) (h : Heap) :
    fresh h (freshRef α p h) x (freshHeap (p := p) h x) := by
  refine ⟨?_, rfl⟩
  intro hMem
  have hMemSupport : h.support.sup id + 1 ∈ h.support :=
    (h.mem_support _).mpr hMem
  have hLe : h.support.sup id + 1 ≤ h.support.sup id :=
    Finset.le_sup (f := fun a : Nat => a) hMemSupport
  exact Nat.not_succ_le_self _ hLe

theorem exists_fresh (x : α) (h : Heap) :
    ∃ (r : Ref α p) (h' : Heap), fresh h r x h' :=
  ⟨freshRef α p h, freshHeap h x, fresh_freshRef x h⟩

/-! ## Sub-heaps

The assertions of `Aeneas.SLPoC.WP` are *affine*: they own the fragments they
describe and say nothing about the rest of the heap.  Semantically that means
they are closed under the extension order below, the way Iris's `uPred` is
monotone in its resource. -/

/-- `Heap.Sub h h'`: `h'` is `h` extended with resources `h` does not own. -/
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

/-- An extension of a split heap splits the same way, the extra resources going
to the right-hand side. -/
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

/-- A heap compatible with an extension is compatible with the heap extended. -/
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

end Heap.Sub


/-! ## How the operations interact with the union of two heaps

These are the lemmas that make the frame rule provable: an operation performed
on a fragment can equally be performed on the whole heap, and leaves the rest of
it untouched. -/

theorem Cell.composable_mk_iff {α : Type} {p : PCM α} {x y : α} :
    Cell.Composable ⟨α, p, x⟩ ⟨α, p, y⟩ ↔ p.Composable x y := by
  constructor
  · intro hComposable
    obtain ⟨y', hEq, hy⟩ := Cell.composable_left_iff.mp hComposable
    have : y = y' := by simpa using hEq
    exact this ▸ hy
  · exact Cell.Composable.intro

theorem contains_iff {h : Heap} {r : Ref α p} :
    contains h r ↔ ∃ x : α, h.cell r.addr = some ⟨α, p, x⟩ := by
  constructor
  · intro hContains
    unfold contains at hContains
    split at hContains
    · exact hContains.elim
    · rename_i c hCell
      obtain ⟨β, q, value⟩ := c
      obtain ⟨hCarrier, hPcm⟩ := hContains
      subst hCarrier
      cases hPcm
      exact ⟨value, hCell⟩
  · rintro ⟨x, hCell⟩
    rw [contains, hCell]
    exact ⟨rfl, HEq.rfl⟩

theorem not_contains_of_cell {h : Heap} {r : Ref α p} {β : Type} {q : PCM β}
    {u : β} (hCell : h.cell r.addr = some ⟨β, q, u⟩)
    (hTyped : ¬ (β = α ∧ HEq q p)) : ¬ contains h r := by
  simp only [contains, hCell]
  exact hTyped

theorem contains_singleton (r : Ref α p) (x : α) : contains (singleton r x) r :=
  contains_iff.mpr ⟨x, by simp⟩

@[simp]
theorem get_singleton (r : Ref α p) (x : α) : (singleton r x).get r = x :=
  Heap.get_of_cell (by simp)

/-- Two cells at different references are compatible. -/
theorem disjoint_singleton {r s : Ref α p} {x y : α} (hNe : r ≠ s) :
    PartialCommMonoid.Compatible (singleton r x) (singleton s y) := by
  intro a
  rw [cell_singleton, cell_singleton]
  by_cases ha : a = r.addr
  · rw [if_pos ha, if_neg (fun hEq : a = s.addr => hNe (ha.symm.trans hEq))]
    simp
  · rw [if_neg ha]
    simp

theorem contains_union_left {h₁ h₂ : Heap} {r : Ref α p}
    (hContains : contains h₁ r) : contains (h₁ ∪ h₂) r := by
  obtain ⟨x, hCell⟩ := contains_iff.mp hContains
  cases hCell₂ : h₂.cell r.addr with
  | none => exact contains_iff.mpr ⟨x, by simp [hCell, hCell₂]⟩
  | some c₂ =>
      by_cases hComposable : Cell.Composable ⟨α, p, x⟩ c₂
      · obtain ⟨y, rfl, hy⟩ := Cell.composable_left_iff.mp hComposable
        exact contains_iff.mpr ⟨p.op x y, by simp [hCell, hCell₂, Cell.op_mk hy]⟩
      · refine contains_iff.mpr ⟨x, ?_⟩
        simp only [Heap.cell_union, hCell, hCell₂, Cell.oop_some_some]
        rw [Cell.op, dif_neg hComposable]

/-- A heap that extends a fragment owns a fragment of the same cell: this is
what an affine points-to assertion gives, the rest of the heap being
unconstrained. -/
theorem contains_of_sub {r : Ref α p} {x : α} {h : Heap}
    (hSub : Heap.Sub (singleton r x) h) : contains h r := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact contains_union_left (contains_singleton r x)

/-- The fragment a cell holds depends on that cell only. -/
theorem Heap.get_congr {h h' : Heap} (r : Ref α p)
    (hEq : h.cell r.addr = h'.cell r.addr) : h.get r = h'.get r := by
  by_cases hContains : contains h r
  · obtain ⟨x, hCell⟩ := contains_iff.mp hContains
    rw [get_of_cell hCell, get_of_cell (by rw [← hEq]; exact hCell)]
  · have hContains' : ¬ contains h' r := by
      intro hC
      obtain ⟨x, hCell⟩ := contains_iff.mp hC
      exact hContains (contains_iff.mpr ⟨x, by rw [hEq]; exact hCell⟩)
    rw [get_of_not_contains hContains, get_of_not_contains hContains']

/-- What a heap compatible with a fragment may hold at that cell. -/
theorem composable_get_of_compatible {h₁ h₂ : Heap} {r : Ref α p} {x : α}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hCell : h₁.cell r.addr = some ⟨α, p, x⟩) :
    p.Composable x (h₂.get r) := by
  by_cases hContains : contains h₂ r
  · obtain ⟨y, hCell₂⟩ := contains_iff.mp hContains
    have hComposable := hCompatible r.addr
    rw [hCell, hCell₂] at hComposable
    rw [Heap.get_of_cell hCell₂]
    exact Cell.composable_mk_iff.mp hComposable
  · rw [Heap.get_of_not_contains hContains]
    exact p.composable_one x

theorem Heap.get_union {h₁ h₂ : Heap} (r : Ref α p)
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    (h₁ ∪ h₂).get r = p.op (h₁.get r) (h₂.get r) := by
  cases hCell₁ : h₁.cell r.addr with
  | none =>
      rw [get_of_not_contains (r := r) (h := h₁)
          (by simp only [contains, hCell₁]; exact id), p.one_op]
      exact get_congr r (by simp [hCell₁])
  | some c₁ =>
      cases hCell₂ : h₂.cell r.addr with
      | none =>
          rw [get_of_not_contains (r := r) (h := h₂)
              (by simp only [contains, hCell₂]; exact id), p.op_one]
          exact get_congr r (by simp [hCell₁, hCell₂])
      | some c₂ =>
          have hComposable := hCompatible r.addr
          rw [hCell₁, hCell₂] at hComposable
          cases hComposable with
          | @intro β q u v huv =>
              have hUnion : (h₁ ∪ h₂).cell r.addr = some ⟨β, q, q.op u v⟩ := by
                simp [hCell₁, hCell₂, Cell.op_mk huv]
              by_cases hTyped : β = α ∧ HEq q p
              · obtain ⟨rfl, hq⟩ := hTyped
                cases hq
                rw [get_of_cell hCell₁, get_of_cell hCell₂, get_of_cell hUnion]
              · rw [get_of_not_contains (not_contains_of_cell hCell₁ hTyped),
                  get_of_not_contains (not_contains_of_cell hCell₂ hTyped),
                  get_of_not_contains (not_contains_of_cell hUnion hTyped),
                  p.op_one]

/-- Reading through an affine points-to assertion returns a value the owned
fragment is compatible with: this is Pulse's `read` contract. -/
theorem compatible_get_of_sub {r : Ref α p} {x : α} {h : Heap}
    (hSub : Heap.Sub (singleton r x) h) : p.Compatible x (h.get r) := by
  obtain ⟨rest, hCompatible, rfl⟩ := hSub
  rw [Heap.get_union r hCompatible, get_singleton]
  exact ⟨rest.get r, composable_get_of_compatible hCompatible (by simp), rfl⟩

/-- Two fragments of one cell whose values do not compose cannot be owned by
compatible heaps: this is what makes a points-to assertion exclusive whenever
its PCM says so. -/
theorem not_composable_incompatible {h₁ h₂ : Heap} {r : Ref α p} {x y : α}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hSub₁ : Heap.Sub (singleton r x) h₁) (hSub₂ : Heap.Sub (singleton r y) h₂)
    (hNotComposable : ¬ p.Composable x y) : False := by
  obtain ⟨u, hCellU⟩ := contains_iff.mp (contains_of_sub hSub₁)
  have hComposable : p.Composable (h₁.get r) (h₂.get r) := by
    rw [Heap.get_of_cell hCellU]
    exact composable_get_of_compatible hCompatible hCellU
  exact hNotComposable
    (PCM.Compatible.composable (compatible_get_of_sub hSub₁)
      (compatible_get_of_sub hSub₂) hComposable)

/-! ## Freshness -/

theorem fresh_empty_eq_singleton {r : Ref α p} {x : α} {h : Heap}
    (hFresh : fresh empty r x h) : h = singleton r x := by
  obtain ⟨-, rfl⟩ := hFresh
  rfl

theorem fresh_frame {r : Ref α p} {x : α} {h₁ h₂ h : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hFresh : fresh (h₁ ∪ h₂) r x h) :
    ∃ h₁',
      fresh h₁ r x h₁' ∧
      PartialCommMonoid.Compatible h₁' h₂ ∧
      h = h₁' ∪ h₂ := by
  obtain ⟨hUnallocated, rfl⟩ := hFresh
  have hCell : Cell.oop (h₁.cell r.addr) (h₂.cell r.addr) = none :=
    Heap.cell_eq_none_of_not_mem hUnallocated
  have hSome : ((h₁.cell r.addr).isSome || (h₂.cell r.addr).isSome) = false := by
    rw [← Cell.isSome_oop, hCell]
    rfl
  have hCell₁ : h₁.cell r.addr = none := by
    cases hC₁ : h₁.cell r.addr with
    | none => rfl
    | some c => rw [hC₁] at hSome; simp at hSome
  have hCell₂ : h₂.cell r.addr = none := by
    cases hC₂ : h₂.cell r.addr with
    | none => rfl
    | some c => rw [hC₂] at hSome; simp at hSome
  refine ⟨h₁.insert r.addr ⟨α, p, x⟩,
    ⟨by simp [unallocated, Heap.mem_iff, hCell₁], rfl⟩, ?_, ?_⟩
  · intro b
    rw [Heap.cell_insert]
    by_cases hb : b = r.addr
    · rw [if_pos hb, hb, hCell₂]; simp
    · rw [if_neg hb]; exact hCompatible b
  · apply Heap.ext
    intro b
    rw [Heap.cell_insert, Heap.cell_union, Heap.cell_union, Heap.cell_insert]
    by_cases hb : b = r.addr
    · rw [if_pos hb, if_pos hb, hb, hCell₂]; simp
    · rw [if_neg hb, if_neg hb]

theorem fresh_eq_singleton_union {r : Ref α p} {x : α} {h h' : Heap}
    (hFresh : fresh h r x h') :
    PartialCommMonoid.Compatible (singleton r x) h ∧ h' = singleton r x ∪ h := by
  have hFreshUnion : fresh (empty ∪ h) r x h' := by
    rwa [Heap.empty_union]
  obtain ⟨h₁, hFresh₁, hCompatible, rfl⟩ :=
    fresh_frame (PartialCommMonoid.compatible_empty_left h) hFreshUnion
  obtain rfl := fresh_empty_eq_singleton hFresh₁
  exact ⟨hCompatible, rfl⟩

/-! ## Splitting and joining one cell -/

theorem compatible_singleton_self {r : Ref α p} {x y : α}
    (hComposable : p.Composable x y) :
    PartialCommMonoid.Compatible (singleton r x) (singleton r y) := by
  intro a
  rw [cell_singleton, cell_singleton]
  by_cases ha : a = r.addr
  · rw [if_pos ha, if_pos ha]; exact Cell.composable_mk_iff.mpr hComposable
  · rw [if_neg ha, if_neg ha]; trivial

theorem singleton_union_singleton {r : Ref α p} {x y : α}
    (hComposable : p.Composable x y) :
    singleton r x ∪ singleton r y = singleton r (p.op x y) := by
  apply Heap.ext
  intro a
  rw [Heap.cell_union, cell_singleton, cell_singleton, cell_singleton]
  by_cases ha : a = r.addr
  · rw [if_pos ha, if_pos ha, if_pos ha, Cell.oop_some_some,
      Cell.op_mk hComposable]
  · rw [if_neg ha, if_neg ha, if_neg ha]
    rfl

/-- Two extensions of compatible heaps extend their union. -/
theorem Heap.Sub.union_mono {A B h₁ h₂ : Heap}
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

/-! ## Updating a cell

Every heap-modifying operation but allocation is a frame-preserving update of
one cell, deallocation included: releasing the fragment a buffer owns is the
update that makes its indices unowned again.  Nothing removes an address, so
`Heap.size`, which counts the cells that still own something, is what tells a
leak from a clean run. -/

namespace Heap

theorem cell_upd_self (r : Ref α p) (f : α → α) (h : Heap)
    (hContains : contains h r) :
    (h.upd r f hContains).cell r.addr = some ⟨α, p, f (h.get r)⟩ := by
  rw [cell_upd, if_pos rfl]

theorem contains_upd (r : Ref α p) (f : α → α) (h : Heap)
    (hContains : contains h r) : contains (h.upd r f hContains) r :=
  contains_iff.mpr ⟨f (h.get r), cell_upd_self r f h hContains⟩

@[simp]
theorem get_upd (r : Ref α p) (f : α → α) (h : Heap)
    (hContains : contains h r) :
    (h.upd r f hContains).get r = f (h.get r) :=
  get_of_cell (cell_upd_self r f h hContains)

theorem upd_singleton (r : Ref α p) (f : α → α) (x : α)
    (hContains : contains (singleton r x) r) :
    (singleton r x).upd r f hContains = singleton r (f x) := by
  apply Heap.ext
  intro b
  rw [cell_upd, cell_singleton, cell_singleton]
  by_cases hb : b = r.addr
  · rw [if_pos hb, if_pos hb, get_singleton]
  · rw [if_neg hb, if_neg hb, if_neg hb]

variable {Owns : α → Prop} {f : α → α}

theorem disjoint_upd_left {r : Ref α p} {h₁ h₂ : Heap}
    (hFramePreserving : p.FramePreserving Owns f)
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ r) (hOwns : Owns (h₁.get r)) :
    PartialCommMonoid.Compatible (h₁.upd r f hContains) h₂ := by
  obtain ⟨x, hCell₁⟩ := contains_iff.mp hContains
  have hGet₁ : h₁.get r = x := get_of_cell hCell₁
  intro b
  rw [cell_upd]
  by_cases hb : b = r.addr
  · rw [if_pos hb, hb, hGet₁]
    rw [hGet₁] at hOwns
    cases hCell₂ : h₂.cell r.addr with
    | none => simp
    | some c₂ =>
        have hComposable := hCompatible r.addr
        rw [hCell₁, hCell₂] at hComposable
        obtain ⟨y, rfl, hy⟩ := Cell.composable_left_iff.mp hComposable
        exact Cell.composable_mk_iff.mpr (hFramePreserving.composable hOwns hy)
  · rw [if_neg hb]; exact hCompatible b

theorem upd_union_left {r : Ref α p} {h₁ h₂ : Heap}
    (hFramePreserving : p.FramePreserving Owns f)
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ r) (hOwns : Owns (h₁.get r)) :
    (h₁ ∪ h₂).upd r f (contains_union_left hContains) =
      h₁.upd r f hContains ∪ h₂ := by
  obtain ⟨x, hCell₁⟩ := contains_iff.mp hContains
  have hGet₁ : h₁.get r = x := get_of_cell hCell₁
  rw [hGet₁] at hOwns
  apply Heap.ext
  intro b
  rw [cell_upd, cell_union, cell_union, cell_upd]
  by_cases hb : b = r.addr
  · rw [if_pos hb, if_pos hb, hb, get_union r hCompatible, hGet₁]
    cases hCell₂ : h₂.cell r.addr with
    | none =>
        rw [get_of_not_contains (by simp only [contains, hCell₂]; exact id),
          p.op_one]
        simp
    | some c₂ =>
        have hComposable := hCompatible r.addr
        rw [hCell₁, hCell₂] at hComposable
        obtain ⟨y, rfl, hy⟩ := Cell.composable_left_iff.mp hComposable
        rw [get_of_cell hCell₂, Cell.oop_some_some,
          Cell.op_mk (hFramePreserving.composable hOwns hy),
          hFramePreserving.op hOwns hy]
  · rw [if_neg hb, if_neg hb]

end Heap

/-- A frame-preserving update of a cell turns an affine points-to assertion for
the old fragment into one for the new fragment. -/
theorem sub_upd {r : Ref α p} {x : α} {h : Heap} {Owns : α → Prop} {f : α → α}
    (hFramePreserving : p.FramePreserving Owns f)
    (hSub : Heap.Sub (singleton r x) h) (hOwns : Owns x)
    (hContains : contains h r) :
    Heap.Sub (singleton r (f x)) (h.upd r f hContains) := by
  obtain ⟨rest, hCompatible, rfl⟩ := hSub
  have hContainsSingle : contains (singleton r x) r := contains_singleton r x
  have hOwns' : Owns ((singleton r x).get r) := by rwa [get_singleton]
  have hEq :=
    Heap.upd_union_left hFramePreserving hCompatible hContainsSingle hOwns'
  have hCompatible' :=
    Heap.disjoint_upd_left hFramePreserving hCompatible hContainsSingle hOwns'
  rw [Heap.upd_singleton] at hEq hCompatible'
  exact ⟨rest, hCompatible', hEq⟩

end Aeneas.SLPoC
