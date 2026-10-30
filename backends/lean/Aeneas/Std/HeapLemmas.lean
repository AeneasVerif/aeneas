module

public import Aeneas.Std.Heap
import all Aeneas.Std.Heap

/-! An affine separation logic for the memory model of `Aeneas.Std.Heap`.

Assertions describe fragments (`Heap`), while programs run on the whole memory (`State`).
`Triple P c Q` states that `c` runs safely from any memory containing a fragment satisfying `P`,
whatever the rest of the memory (the frame), and that `Q` then holds of a part of the resulting
fragment. The rest of the fragment is leaked: it stays in the memory, so its allocation ids are never
reused, but nobody can access it anymore (`Triple.drop`). The only invariant of the whole memory is
`State.Inv`: the allocation ids from `next` on are unused. -/

@[expose] public section

namespace Aeneas.Std

universe u v w w'

namespace RawPtr

@[simp] theorem allocId_shift (q : RawPtr T M) (i : Nat) : (q.shift i).allocId = q.allocId := rfl

@[simp] theorem offset_shift (q : RawPtr T M) (i : Nat) : (q.shift i).offset = q.offset + i := rfl

@[simp] theorem shift_zero (q : RawPtr T M) : q.shift 0 = q := rfl

theorem shift_shift (q : RawPtr T M) (i j : Nat) : (q.shift i).shift j = q.shift (i + j) := by
  simp [shift, Nat.add_assoc]

@[simp] theorem allocId_loc (q : RawPtr T M) : q.loc.allocId = q.allocId := rfl

@[simp] theorem offset_loc (q : RawPtr T M) : q.loc.offset = q.offset := rfl

end RawPtr

/-! ### Heap algebra -/

namespace Heap

@[simp] theorem cells_empty (l : Loc) : (∅ : Heap.{v}).cells l = none := rfl

@[simp] theorem allocs_empty (a : AllocId) : (∅ : Heap.{v}).allocs a = none := rfl

@[simp] theorem cells_union (h₁ h₂ : Heap.{v}) (l : Loc) :
    (h₁ ∪ h₂).cells l = (h₁.cells l).or (h₂.cells l) := rfl

@[simp] theorem allocs_union (h₁ h₂ : Heap.{v}) (a : AllocId) :
    (h₁ ∪ h₂).allocs a = (h₁.allocs a).or (h₂.allocs a) := rfl

@[simp] theorem cells_setCell (h : Heap.{v}) (l l' : Loc) (c : Cell.{v}) :
    (h.setCell l c).cells l' = if l' = l then some c else h.cells l' := rfl

@[simp] theorem allocs_setCell (h : Heap.{v}) (l : Loc) (c : Cell.{v}) (a : AllocId) :
    (h.setCell l c).allocs a = h.allocs a := rfl

@[simp] theorem empty_union (h : Heap.{v}) : ∅ ∪ h = h := rfl

@[simp] theorem union_empty (h : Heap.{v}) : h ∪ ∅ = h := by
  ext1 <;> funext _ <;> simp

theorem union_assoc (a b c : Heap.{v}) : a ∪ b ∪ c = a ∪ (b ∪ c) := by
  ext1 <;> funext _ <;> simp [Option.or_assoc]

theorem Disjoint.symm {a b : Heap.{v}} (h : a.Disjoint b) : b.Disjoint a :=
  ⟨fun l => (h.1 l).symm, fun x => (h.2 x).symm⟩

theorem disjoint_comm {a b : Heap.{v}} : a.Disjoint b ↔ b.Disjoint a :=
  ⟨Disjoint.symm, Disjoint.symm⟩

@[simp] theorem disjoint_empty_left (h : Heap.{v}) : (∅ : Heap).Disjoint h :=
  ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩

@[simp] theorem disjoint_empty_right (h : Heap.{v}) : h.Disjoint ∅ :=
  ⟨fun _ => Or.inr rfl, fun _ => Or.inr rfl⟩

theorem union_comm {a b : Heap.{v}} (h : a.Disjoint b) : a ∪ b = b ∪ a := by
  ext1
  · funext l; rcases h.1 l with e | e <;> simp [e]
  · funext x; rcases h.2 x with e | e <;> simp [e]

theorem disjoint_union_left {a b c : Heap.{v}} :
    (a ∪ b).Disjoint c ↔ a.Disjoint c ∧ b.Disjoint c := by
  constructor
  · rintro ⟨hc, ha⟩
    refine ⟨⟨fun l => ?_, fun x => ?_⟩, ⟨fun l => ?_, fun x => ?_⟩⟩
    · rcases hc l with e | e <;> cases h1 : a.cells l <;> simp_all
    · rcases ha x with e | e <;> cases h1 : a.allocs x <;> simp_all
    · rcases hc l with e | e <;> cases h1 : a.cells l <;> simp_all
    · rcases ha x with e | e <;> cases h1 : a.allocs x <;> simp_all
  · rintro ⟨⟨ac, aa⟩, ⟨bc, ba⟩⟩
    refine ⟨fun l => ?_, fun x => ?_⟩
    · rcases ac l with e | e <;> rcases bc l with e' | e' <;> simp_all
    · rcases aa x with e | e <;> rcases ba x with e' | e' <;> simp_all

theorem disjoint_union_right {a b c : Heap.{v}} :
    a.Disjoint (b ∪ c) ↔ a.Disjoint b ∧ a.Disjoint c := by
  rw [disjoint_comm, disjoint_union_left, disjoint_comm (a := b), disjoint_comm (a := c)]

/-- Replacing a cell owned by the left fragment commutes with the union. -/
theorem setCell_union {h F : Heap.{v}} {l : Loc} (c : Cell.{v}) (hl : (h.cells l).isSome) :
    (h ∪ F).setCell l c = h.setCell l c ∪ F := by
  ext1
  · funext l'
    by_cases e : l' = l
    · subst e; simp
    · simp [e]
  · rfl

theorem disjoint_setCell {h F : Heap.{v}} {l : Loc} (c : Cell.{v}) (hl : (h.cells l).isSome)
    (hDisjoint : h.Disjoint F) : (h.setCell l c).Disjoint F := by
  refine ⟨fun l' => ?_, hDisjoint.2⟩
  by_cases e : l' = l
  · subst e
    rcases hDisjoint.1 l' with e' | e'
    · simp [e'] at hl
    · exact Or.inr e'
  · simpa [e] using hDisjoint.1 l'

end Heap

/-! ### The invariant of the whole memory -/

namespace State

/-- The allocation ids from `next` on are unused. -/
def Inv (s : State.{v}) : Prop :=
  ∀ a ≥ s.next, s.heap.allocs a = none ∧ ∀ o, s.heap.cells ⟨a, o⟩ = none

theorem inv_empty : Inv empty.{v} := fun _ _ => ⟨rfl, fun _ => rfl⟩

/-- Replacing an existing cell preserves the invariant. -/
theorem Inv.setCell {h : Heap.{v}} {next : AllocId} {l : Loc} (c : Cell.{v})
    (hl : (h.cells l).isSome) (hInv : Inv ⟨h, next⟩) : Inv ⟨h.setCell l c, next⟩ := by
  intro a ha
  obtain ⟨h1, h2⟩ := hInv a ha
  refine ⟨h1, fun o => ?_⟩
  by_cases e : (⟨a, o⟩ : Loc) = l
  · subst e
    have h2' : h.cells ⟨a, o⟩ = none := h2 o
    simp [h2'] at hl
  · simpa [e] using h2 o

@[simp] theorem heap_setCell (s : State.{v}) (l : Loc) (c : Cell.{v}) :
    (s.setCell l c).heap = s.heap.setCell l c := rfl

@[simp] theorem next_setCell (s : State.{v}) (l : Loc) (c : Cell.{v}) :
    (s.setCell l c).next = s.next := rfl

end State

/-! ### Assertions and triples -/

namespace SepLogic

/-- An assertion on a fragment of the memory. -/
abbrev Assertion := Heap.{v} → Prop

/-- The empty fragment. -/
def emp : Assertion.{v} := fun h => h = ∅

/-- Separating conjunction: the fragment splits into two disjoint parts satisfying `P` and `Q`. -/
def sep (P Q : Assertion.{v}) : Assertion.{v} :=
  fun h => ∃ h₁ h₂, h₁.Disjoint h₂ ∧ h = h₁ ∪ h₂ ∧ P h₁ ∧ Q h₂

theorem sep_comm (P Q : Assertion.{v}) (h : Heap.{v}) : sep P Q h ↔ sep Q P h := by
  constructor <;>
  · rintro ⟨h₁, h₂, hd, hEq, h1, h2⟩
    exact ⟨h₂, h₁, hd.symm, hEq.trans (Heap.union_comm hd), h2, h1⟩

theorem sep_mono {P P' Q Q' : Assertion.{v}} {h : Heap.{v}} (hP : ∀ h, P h → P' h)
    (hQ : ∀ h, Q h → Q' h) : sep P Q h → sep P' Q' h := by
  rintro ⟨h₁, h₂, hd, hEq, h1, h2⟩
  exact ⟨h₁, h₂, hd, hEq, hP _ h1, hQ _ h2⟩

theorem sep_and_left (φ : Prop) (P Q : Assertion.{v}) (h : Heap.{v}) :
    sep (fun h => φ ∧ P h) Q h ↔ φ ∧ sep P Q h := by
  constructor
  · rintro ⟨h₁, h₂, hd, hEq, ⟨hφ, h1⟩, h2⟩
    exact ⟨hφ, h₁, h₂, hd, hEq, h1, h2⟩
  · rintro ⟨hφ, h₁, h₂, hd, hEq, h1, h2⟩
    exact ⟨h₁, h₂, hd, hEq, ⟨hφ, h1⟩, h2⟩

/-- A program on the whole memory, as a relation between the initial state, the result and the final
state (as in `Result.guardedModify`). It is undefined behaviour in the states without successor. -/
abbrev Cmd (α : Type w) : Type (max w (v + 1)) := State.{v} → α → State.{v} → Prop

def Cmd.pure (x : α) : Cmd.{v, w} α := fun s y s' => y = x ∧ s' = s

def Cmd.bind (c : Cmd.{v, w} α) (k : α → Cmd.{v, w'} β) : Cmd.{v, w'} β :=
  fun s y s'' => ∃ x s', c s x s' ∧ k x s' y s''

/-- An affine Hoare triple. The program runs on the whole memory: `P` describes the fragment `h`
and `F` is the frame. The program must have a successor, and for every successor (the semantics
is demonic), the frame is untouched and `Q` describes a part `hq` of the final fragment `h'`: the
rest `g` is leaked. -/
def Triple (P : Assertion.{v}) (c : Cmd.{v, w} α) (Q : α → Assertion.{v}) : Prop :=
  ∀ h F next, P h → h.Disjoint F → State.Inv ⟨h ∪ F, next⟩ →
    (∃ x s', c ⟨h ∪ F, next⟩ x s') ∧
    ∀ x s', c ⟨h ∪ F, next⟩ x s' →
      ∃ h' next', s' = ⟨h' ∪ F, next'⟩ ∧ h'.Disjoint F ∧ State.Inv s' ∧
        ∃ hq g, hq.Disjoint g ∧ h' = hq ∪ g ∧ Q x hq

theorem frame {P R : Assertion.{v}} {c : Cmd.{v, w} α} {Q : α → Assertion.{v}}
    (hT : Triple P c Q) : Triple (sep P R) c (fun x => sep (Q x) R) := by
  intro h F next ⟨h₁, h₂, hc12, hEq, hP, hR⟩ hcF hInv
  subst hEq
  obtain ⟨hc1F, hc2F⟩ := Heap.disjoint_union_left.mp hcF
  have hc1 : h₁.Disjoint (h₂ ∪ F) := Heap.disjoint_union_right.mpr ⟨hc12, hc1F⟩
  rw [Heap.union_assoc h₁ h₂ F] at hInv ⊢
  obtain ⟨hSafe, hPost⟩ := hT h₁ (h₂ ∪ F) next hP hc1 hInv
  refine ⟨hSafe, fun x s' hrun => ?_⟩
  obtain ⟨h', next', hs', hc', hInv', hq, g, hqg, hh', hQ⟩ := hPost x s' hrun
  subst hh' hs'
  obtain ⟨hc'2, hc'F⟩ := Heap.disjoint_union_right.mp hc'
  obtain ⟨hq2, hg2⟩ := Heap.disjoint_union_left.mp hc'2
  refine ⟨hq ∪ g ∪ h₂, next', by rw [Heap.union_assoc (hq ∪ g) h₂ F],
    Heap.disjoint_union_left.mpr ⟨hc'F, hc2F⟩, hInv', hq ∪ h₂, g,
    Heap.disjoint_union_left.mpr ⟨hqg, hg2.symm⟩, ?_, hq, h₂, hq2, rfl, hQ, hR⟩
  rw [Heap.union_assoc, Heap.union_comm hg2, ← Heap.union_assoc]

/-- Affinity: any part of the postcondition can be dropped. -/
theorem Triple.drop {P R : Assertion.{v}} {c : Cmd.{v, w} α} {Q : α → Assertion.{v}}
    (hT : Triple P c (fun x => sep (Q x) R)) : Triple P c Q := by
  intro h F next hp hc hInv
  obtain ⟨hSafe, hPost⟩ := hT h F next hp hc hInv
  refine ⟨hSafe, fun x s' hrun => ?_⟩
  obtain ⟨h', next', hs', hc', hInv', hq, g, hqg, hh', q, r, hqr, hqe, hQ, _⟩ := hPost x s' hrun
  subst hqe
  exact ⟨h', next', hs', hc', hInv', q, r ∪ g,
    Heap.disjoint_union_right.mpr ⟨hqr, (Heap.disjoint_union_left.mp hqg).1⟩,
    by rw [hh', Heap.union_assoc], hQ⟩

theorem Triple.conseq {P P' : Assertion.{v}} {c : Cmd.{v, w} α} {Q Q' : α → Assertion.{v}}
    (hP : ∀ h, P h → P' h) (hQ : ∀ x h, Q' x h → Q x h) (hT : Triple P' c Q') :
    Triple P c Q := by
  intro h F next hp hc hInv
  obtain ⟨hSafe, hPost⟩ := hT h F next (hP h hp) hc hInv
  refine ⟨hSafe, fun x s' hrun => ?_⟩
  obtain ⟨h', next', hs', hc', hInv', hq, g, hqg, hh', hq'⟩ := hPost x s' hrun
  exact ⟨h', next', hs', hc', hInv', hq, g, hqg, hh', hQ x hq hq'⟩

/-- Facts that hold in the precondition can be assumed. -/
theorem Triple.of_pre {P : Assertion.{v}} {c : Cmd.{v, w} α} {Q : α → Assertion.{v}}
    (hT : ∀ h, P h → Triple (fun h' => h' = h) c Q) : Triple P c Q :=
  fun h F next hp hc hInv => hT h hp h F next rfl hc hInv

/-- Pure facts of the precondition can be assumed. -/
theorem Triple.pure_pre {φ : Prop} {P : Assertion.{v}} {c : Cmd.{v, w} α} {Q : α → Assertion.{v}}
    (hT : φ → Triple P c Q) : Triple (fun h => φ ∧ P h) c Q :=
  fun h F next ⟨hφ, hp⟩ hc hInv => hT hφ h F next hp hc hInv

theorem Triple.pure {P : Assertion.{v}} (x : α) :
    Triple P (Cmd.pure.{v, w} x) (fun y h => y = x ∧ P h) := by
  intro h F next hp hc hInv
  refine ⟨⟨x, _, rfl, rfl⟩, ?_⟩
  rintro y s' ⟨rfl, rfl⟩
  exact ⟨h, next, rfl, hc, hInv, h, ∅, by simp, by simp, rfl, hp⟩

theorem Triple.bind {P : Assertion.{v}} {c : Cmd.{v, w} α} {k : α → Cmd.{v, w'} β}
    {Q : α → Assertion.{v}} {R : β → Assertion.{v}}
    (hc : Triple P c Q) (hk : ∀ x, Triple (Q x) (k x) R) : Triple P (c.bind k) R := by
  intro h F next hp hcF hInv
  obtain ⟨⟨x₀, s₀, hrun₀⟩, hPost⟩ := hc h F next hp hcF hInv
  /- After `c`, the continuation runs on the part `hq` described by `Q`, framing the garbage `g`
  of `c` together with `F`. -/
  have hAfter : ∀ x s', c ⟨h ∪ F, next⟩ x s' →
      ∃ hq g next', s' = ⟨hq ∪ (g ∪ F), next'⟩ ∧ g.Disjoint F ∧
        (∃ y s'', k x s' y s'') ∧
        ∀ y s'', k x s' y s'' →
          ∃ h'' next'', s'' = ⟨h'' ∪ (g ∪ F), next''⟩ ∧ h''.Disjoint (g ∪ F) ∧ State.Inv s'' ∧
            ∃ hr g₂, hr.Disjoint g₂ ∧ h'' = hr ∪ g₂ ∧ R y hr := by
    intro x s' hrun
    obtain ⟨h', next', hs', hc', hInv', hq, g, hqg, hh', hQ⟩ := hPost x s' hrun
    subst hh' hs'
    obtain ⟨hqF, hgF⟩ := Heap.disjoint_union_left.mp hc'
    rw [Heap.union_assoc hq g F] at hInv' ⊢
    exact ⟨hq, g, next', rfl, hgF,
      hk x hq (g ∪ F) next' hQ (Heap.disjoint_union_right.mpr ⟨hqg, hqF⟩) hInv'⟩
  refine ⟨?_, fun y s'' ⟨x, s', hrun, hkrun⟩ => ?_⟩
  · obtain ⟨-, -, -, -, -, ⟨y, s'', hk₀⟩, -⟩ := hAfter x₀ s₀ hrun₀
    exact ⟨y, s'', x₀, s₀, hrun₀, hk₀⟩
  · obtain ⟨hq, g, next', -, hgF, -, hkPost⟩ := hAfter x s' hrun
    obtain ⟨h'', next'', hs'', hc'', hInv'', hr, g₂, hrg, hh'', hR⟩ := hkPost y s'' hkrun
    subst hh'' hs''
    obtain ⟨hr'g, hr'F⟩ := Heap.disjoint_union_right.mp hc''
    obtain ⟨hrg', -⟩ := Heap.disjoint_union_left.mp hr'g
    exact ⟨hr ∪ g₂ ∪ g, next'', by rw [Heap.union_assoc (hr ∪ g₂) g F],
      Heap.disjoint_union_left.mpr ⟨hr'F, hgF⟩, hInv'', hr, g₂ ∪ g,
      Heap.disjoint_union_right.mpr ⟨hrg, hrg'⟩, by rw [Heap.union_assoc], hR⟩

/-! ### Points-to assertions -/

/-- The fragment owning exactly the `Allocation` entry of block `a`. -/
def allocHeap (kind : AllocKind) (a : AllocId) (n : Nat) : Heap.{v} :=
  ⟨fun _ => none, fun b => if b = a then some ⟨kind, n⟩ else none⟩

/-- The fragment owning exactly the `n` cells from `l` on, with contents `f` (indexed from `l`). -/
def cellsHeap (l : Loc) (n : Nat) (f : Nat → Cell.{v}) : Heap.{v} :=
  ⟨fun l' => if l'.allocId = l.allocId ∧ l.offset ≤ l'.offset ∧ l'.offset < l.offset + n
            then some (f (l'.offset - l.offset)) else none,
   fun _ => none⟩

/-- `l` starts a block of kind `kind` and `n` cells, and we own its `Allocation` entry, i.e., the
right to deallocate it. This doesn't give any cell. -/
def alloc (kind : AllocKind) (l : Loc) (n : Nat) : Assertion.{v} :=
  fun h => l.offset = 0 ∧ h = allocHeap kind l.allocId n

/-- We own the `n` cells from `l` on (`l` can be an interior pointer), with contents `f`. -/
def block (l : Loc) (n : Nat) (f : Nat → Cell.{v}) : Assertion.{v} :=
  fun h => h = cellsHeap l n f

/-- We own the cell at `l`, with content `c`. -/
abbrev cellAt (l : Loc) (c : Cell.{v}) : Assertion.{v} := block l 1 fun _ => c

/-- `q` points to the (initialized) value `value`. -/
abbrev pointsTo {α : Type v} (q : RawPtr α M) (value : α) : Assertion.{v} :=
  cellAt q.loc (.owned α (some value))

@[simp] theorem cells_allocHeap (kind : AllocKind) (a : AllocId) (n : Nat) (l : Loc) :
    (allocHeap.{v} kind a n).cells l = none := rfl

@[simp] theorem allocs_cellsHeap (l : Loc) (n : Nat) (f : Nat → Cell.{v}) (a : AllocId) :
    (cellsHeap l n f).allocs a = none := rfl

theorem cells_cellsHeap_one (l l' : Loc) (f : Nat → Cell.{v}) :
    (cellsHeap l 1 f).cells l' = if l' = l then some (f 0) else none := by
  by_cases e : l' = l
  · subst e; simp [cellsHeap]
  · have : ¬ (l'.allocId = l.allocId ∧ l.offset ≤ l'.offset ∧ l'.offset < l.offset + 1) := by
      intro ⟨h1, h2, h3⟩
      exact e (Loc.ext h1 (by omega))
    simp [cellsHeap, this, e]

theorem disjoint_allocHeap_cellsHeap (kind : AllocKind) (a : AllocId) (n : Nat) (l : Loc) (k : Nat)
    (f : Nat → Cell.{v}) : (allocHeap kind a n).Disjoint (cellsHeap l k f) :=
  ⟨fun _ => Or.inl rfl, fun _ => Or.inr rfl⟩

theorem disjoint_cellsHeap_add (l : Loc) (n k : Nat) (f : Nat → Cell.{v}) :
    (cellsHeap l n f).Disjoint (cellsHeap ⟨l.allocId, l.offset + n⟩ k fun i => f (i + n)) := by
  refine ⟨fun l' => ?_, fun _ => Or.inl rfl⟩
  by_cases h : l'.offset < l.offset + n
  · right
    have : ¬ (l'.allocId = l.allocId ∧ l.offset + n ≤ l'.offset ∧ l'.offset < l.offset + n + k) := by
      omega
    simp [cellsHeap, this]
  · left
    have : ¬ (l'.allocId = l.allocId ∧ l.offset ≤ l'.offset ∧ l'.offset < l.offset + n) := by grind
    simp [cellsHeap, this]

theorem cellsHeap_add (l : Loc) (n k : Nat) (f : Nat → Cell.{v}) :
    cellsHeap l (n + k) f =
      cellsHeap l n f ∪ cellsHeap ⟨l.allocId, l.offset + n⟩ k fun i => f (i + n) := by
  ext1
  · funext l'
    by_cases h1 : l'.allocId = l.allocId ∧ l.offset ≤ l'.offset ∧ l'.offset < l.offset + n
    · have : l'.allocId = l.allocId ∧ l.offset ≤ l'.offset ∧ l'.offset < l.offset + (n + k) := by
        grind
      simp [cellsHeap, h1, this]
    · by_cases h2 : l'.allocId = l.allocId ∧ l.offset + n ≤ l'.offset ∧
          l'.offset < l.offset + n + k
      · have : l'.allocId = l.allocId ∧ l.offset ≤ l'.offset ∧ l'.offset < l.offset + (n + k) := by
          grind
        have hn : ¬ l'.offset < l.offset + n := by grind
        have e : l'.offset - (l.offset + n) + n = l'.offset - l.offset := by omega
        simp [cellsHeap, h2, this, hn, e]
      · have : ¬ (l'.allocId = l.allocId ∧ l.offset ≤ l'.offset ∧
            l'.offset < l.offset + (n + k)) := by grind
        simp [cellsHeap, h1, h2, this]
  · rfl

theorem cellsHeap_congr {l : Loc} {n : Nat} {f g : Nat → Cell.{v}} (hfg : ∀ i < n, f i = g i) :
    cellsHeap l n f = cellsHeap l n g := by
  ext1
  · funext l'
    by_cases hl : l'.allocId = l.allocId ∧ l.offset ≤ l'.offset ∧ l'.offset < l.offset + n
    · simp [cellsHeap, hl, hfg (l'.offset - l.offset) (by omega)]
    · simp [cellsHeap, hl]
  · rfl

theorem block_congr {l : Loc} {n : Nat} {f g : Nat → Cell.{v}} (hfg : ∀ i < n, f i = g i)
    {h : Heap.{v}} : block l n f h ↔ block l n g h := by
  simp [block, cellsHeap_congr hfg]

/-- A block splits into two consecutive blocks: this is how a pointer to a list is split into two
pointers (e.g., `split_at_mut`). -/
theorem block_add (l : Loc) (n k : Nat) (f : Nat → Cell.{v}) (h : Heap.{v}) :
    block l (n + k) f h ↔
      sep (block l n f) (block ⟨l.allocId, l.offset + n⟩ k fun i => f (i + n)) h := by
  constructor
  · intro hb
    exact ⟨_, _, disjoint_cellsHeap_add l n k f, hb.trans (cellsHeap_add l n k f), rfl, rfl⟩
  · rintro ⟨h₁, h₂, -, hEq, h1, h2⟩
    rw [hEq, h1, h2]
    exact (cellsHeap_add l n k f).symm

/-! ### Specifications of the operations -/

theorem setCell_same {s : State.{v}} {l : Loc} {c : Cell.{v}} (hl : s.heap.cells l = some c) :
    s.setCell l c = s := by
  obtain ⟨⟨cells, allocs⟩, next⟩ := s
  simp only [State.setCell, Heap.setCell, State.mk.injEq, Heap.mk.injEq, and_true]
  funext l'
  by_cases e : l' = l
  · subst e; simpa using hl.symm
  · simp [e]

/-- The generic specification of the operations which act on the cell at `l`. -/
theorem triple_setCell {op : Cmd.{v, w} α} {l : Loc} {c c' : Cell.{v}} {P : α → Prop}
    (hSafe : ∀ s : State.{v}, s.heap.cells l = some c → ∃ x, op s x (s.setCell l c'))
    (hOp : ∀ s x s', s.heap.cells l = some c → op s x s' → P x ∧ s' = s.setCell l c') :
    Triple (cellAt l c) op (fun x h => P x ∧ cellAt l c' h) := by
  intro h F next hh hc hInv
  subst hh
  have hl : (cellsHeap l 1 (fun _ => c) ∪ F).cells l = some c := by
    simp [cells_cellsHeap_one]
  have hl' : ((cellsHeap l 1 fun _ => c).cells l).isSome := by simp [cells_cellsHeap_one]
  refine ⟨(hSafe _ hl).imp fun x hx => ⟨_, hx⟩, fun x s' hrun => ?_⟩
  obtain ⟨hP, rfl⟩ := hOp _ x s' hl hrun
  refine ⟨(cellsHeap l 1 fun _ => c).setCell l c', next, ?_, Heap.disjoint_setCell c' hl' hc,
    State.Inv.setCell c' (by simp [hl]) hInv, _, ∅, by simp, (Heap.union_empty _).symm, hP, ?_⟩
  · simp [State.setCell, Heap.setCell_union c' hl']
  · show _ = _
    ext1
    · funext l'
      by_cases e : l' = l <;> simp [e, cells_cellsHeap_one]
    · rfl

private theorem eq_of_cell {s : State.{v}} {q : RawPtr α M} {x y : α}
    (hx : s.cell q = some (.owned α (some x))) (hy : s.heap.cells q.loc = some (.owned α (some y))) :
    x = y := by
  have := hx.symm.trans hy
  simpa using this

/-- `{q ↦ v} read q {x => ⌜x = v⌝ ∗ q ↦ v}` -/
theorem read_spec {α : Type v} (q : RawPtr α M) (value : α) :
    Triple (pointsTo q value) (State.read q) (fun x h => x = value ∧ pointsTo q value h) :=
  triple_setCell (fun _ hl => ⟨value, hl, setCell_same hl⟩)
    fun _ _ _ hl ⟨hx, hs'⟩ => ⟨eq_of_cell hx hl, hs'.trans (setCell_same hl).symm⟩

/-- `{q ↦ _} write q v {q ↦ v}`, where the cell of `q` can be uninitialized. -/
theorem write_spec {α : Type v} (q : RawPtr α M) (old : Option α) (value : α) :
    Triple (cellAt q.loc (.owned α old)) (State.write q value) (fun _ => pointsTo q value) :=
  Triple.conseq (fun _ h => h) (fun _ _ h => h.2)
    (triple_setCell (P := fun _ => True) (fun _ hl => ⟨(), ⟨old, hl⟩, rfl⟩)
      fun _ _ _ _ ⟨_, hs'⟩ => ⟨trivial, hs'⟩)

/-- `{q ↦ v} borrow q {x => ⌜x = v⌝ ∗ q ↦ borrowed}` -/
theorem borrow_spec {α : Type v} (q : RawPtr α M) (value : α) :
    Triple (pointsTo q value) (State.borrow q) (fun x h => x = value ∧ cellAt q.loc .borrowed h) :=
  triple_setCell (fun _ hl => ⟨value, hl, rfl⟩)
    fun _ _ _ hl ⟨hx, hs'⟩ => ⟨eq_of_cell hx hl, hs'⟩

/-- `{q ↦ borrowed} endBorrow q v {q ↦ v}` -/
theorem endBorrow_spec {α : Type v} (q : RawPtr α M) (value : α) :
    Triple (cellAt q.loc .borrowed) (State.endBorrow q value) (fun _ => pointsTo q value) :=
  Triple.conseq (fun _ h => h) (fun _ _ h => h.2)
    (triple_setCell (P := fun _ => True) (fun _ hl => ⟨(), hl, rfl⟩)
      fun _ _ _ _ ⟨_, hs'⟩ => ⟨trivial, hs'⟩)

/-- `add`: shifting a pointer over owned cells. -/
theorem add_spec (q : RawPtr T M) (n : Nat) (f : Nat → Cell.{v})
    (hOwned : ∀ i < n, ∃ (ty : Type v) (value : Option ty), f i = .owned ty value) :
    Triple (block q.loc n f) (State.add q n) (fun r h => r = q.shift n ∧ block q.loc n f h) := by
  intro h F next hh hc hInv
  subst hh
  have hIn : State.InBounds ⟨cellsHeap q.loc n f ∪ F, next⟩ q n := by
    intro i hi
    obtain ⟨ty, value, hf⟩ := hOwned i hi
    refine ⟨ty, value, ?_⟩
    have : q.allocId = q.allocId ∧ q.offset ≤ q.offset + i ∧ q.offset + i < q.offset + n := by
      grind
    simp [State.cell, RawPtr.loc, RawPtr.shift, cellsHeap, this, hf]
  refine ⟨⟨_, _, hIn, rfl, rfl⟩, ?_⟩
  rintro r s' ⟨-, rfl, rfl⟩
  exact ⟨_, next, rfl, hc, hInv, _, ∅, by simp, (Heap.union_empty _).symm, rfl, rfl⟩

/-- `{emp} newBlock values kind {p => alloc kind p n ∗ block p n values}` -/
theorem newBlock_spec {α : Type v} (values : List α) (kind : AllocKind) :
    Triple emp (State.newBlock values kind)
      (fun p => sep (alloc kind p.loc values.length)
        (block p.loc values.length fun o => .owned α values[o]?)) := by
  intro h F next hemp hc hInv
  subst hemp
  simp only [Heap.empty_union] at hInv ⊢
  have hFa : F.allocs next = none := (hInv next (Nat.le_refl _)).1
  have hFc : ∀ o, F.cells ⟨next, o⟩ = none := (hInv next (Nat.le_refl _)).2
  refine ⟨⟨_, _, rfl⟩, ?_⟩
  rintro p s' hrun
  simp only [State.newBlock, State.allocBlock, Prod.mk.injEq] at hrun
  obtain ⟨rfl, rfl⟩ := hrun
  refine ⟨allocHeap kind next values.length ∪
      cellsHeap ⟨next, 0⟩ values.length (fun o => .owned α values[o]?), next + 1,
    ?_, ?_, ?_, _, ∅, by simp, (Heap.union_empty _).symm,
    _, _, disjoint_allocHeap_cellsHeap _ _ _ _ _ _, rfl, ⟨rfl, rfl⟩, rfl⟩
  · simp only [State.mk.injEq, and_true]
    ext1
    · funext l
      by_cases hl : l.allocId = next ∧ l.offset < values.length
      · simp [hl, cellsHeap, allocHeap]
      · simp [cellsHeap, hl]
    · funext b
      by_cases hb : b = next <;> simp [hb, allocHeap, hFa]
  · refine Heap.disjoint_union_left.mpr ⟨⟨fun _ => Or.inl rfl, fun b => ?_⟩,
      ⟨fun l => ?_, fun _ => Or.inl rfl⟩⟩
    · by_cases hb : b = next
      · subst hb; exact Or.inr hFa
      · left; simp [allocHeap, hb]
    · by_cases hl : l.allocId = next
      · obtain ⟨a, o⟩ := l
        simp only at hl
        subst hl
        exact Or.inr (hFc o)
      · left; simp [cellsHeap, hl]
  · intro b hb
    have hb' : next + 1 ≤ b := hb
    have hne : b ≠ next := Nat.ne_of_gt (Nat.lt_of_succ_le hb')
    obtain ⟨h1, h2⟩ := hInv b (Nat.le_of_succ_le hb')
    have h1' : F.allocs b = none := h1
    refine ⟨by simp [hne, h1'], fun o => ?_⟩
    have h2' : F.cells ⟨b, o⟩ = none := h2 o
    simp [hne, h2']

/-- `{alloc kind p n ∗ block p n f} freeBlock p n kind {emp}`, if no cell is borrowed. -/
theorem freeBlock_spec (q : RawPtr α M) (n : Nat) (kind : AllocKind) (f : Nat → Cell.{v})
    (hOwned : ∀ i < n, ∃ (ty : Type v) (value : Option ty), f i = .owned ty value) :
    Triple (sep (alloc kind q.loc n) (block q.loc n f)) (State.freeBlock q n kind)
      (fun _ => emp) := by
  intro h F next ⟨h₁, h₂, _, hEq, ⟨hoff, h1⟩, h2⟩ hc hInv
  subst hEq h1 h2
  simp only [RawPtr.offset_loc] at hoff
  simp only [RawPtr.allocId_loc] at hc hInv ⊢
  obtain ⟨hc1, hc2⟩ := Heap.disjoint_union_left.mp hc
  have hFa : F.allocs q.allocId = none := by
    rcases hc1.2 q.allocId with e | e
    · simp [allocHeap] at e
    · exact e
  have hFc : ∀ l : Loc, l.allocId = q.allocId → l.offset < n → F.cells l = none := by
    intro l hl ho
    rcases hc2.1 l with e | e
    · have : l.allocId = q.allocId ∧ q.offset ≤ l.offset ∧ l.offset < q.offset + n := by grind
      simp [cellsHeap, this] at e
    · exact e
  have hCan : State.CanDealloc ⟨allocHeap kind q.allocId n ∪ cellsHeap q.loc n f ∪ F, next⟩
      q n kind := by
    refine ⟨hoff, by simp [allocHeap], fun i hi => ?_⟩
    obtain ⟨ty, value, hf⟩ := hOwned i hi
    refine ⟨ty, value, ?_⟩
    have : q.allocId = q.allocId ∧ q.offset ≤ q.offset + i ∧ q.offset + i < q.offset + n := by
      grind
    simp [State.cell, RawPtr.loc, RawPtr.shift, cellsHeap, allocHeap, this, hf]
  have hState : State.removeBlock q.allocId n
      ⟨allocHeap kind q.allocId n ∪ cellsHeap q.loc n f ∪ F, next⟩ = ⟨∅ ∪ F, next⟩ := by
    simp only [State.removeBlock, Heap.empty_union, State.mk.injEq, and_true]
    ext1
    · funext l
      by_cases hl : l.allocId = q.allocId ∧ l.offset < n
      · simp [hl, hFc l hl.1 hl.2]
      · have : ¬ (l.allocId = q.allocId ∧ q.offset ≤ l.offset ∧ l.offset < q.offset + n) := by
          grind
        simp [hl, cellsHeap, allocHeap, this]
    · funext b
      by_cases hb : b = q.allocId
      · subst hb; simp [hFa]
      · simp [hb, allocHeap]
  refine ⟨⟨(), _, hCan, rfl⟩, ?_⟩
  rintro _ s' ⟨-, rfl⟩
  rw [hState]
  refine ⟨∅, next, rfl, by simp, ?_, ∅, ∅, by simp, by simp, rfl⟩
  intro b hb
  obtain ⟨h1, h2⟩ := hInv b hb
  simp only [Heap.allocs_union, Option.or_eq_none_iff, Heap.cells_union] at h1 h2
  exact ⟨h1.2, fun o => (h2 o).2⟩

end SepLogic

end Aeneas.Std
