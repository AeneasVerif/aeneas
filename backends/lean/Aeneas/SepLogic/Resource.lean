module

public import Aeneas.Std.Heap.Lemmas

/-! The resources of the byte heap (from fournet/wip-memory-model).
Separation splits indexed permission contributions, not physical addresses.
Distinct views may overlap numerically; `Heap.Inv` checks their byte compatibility.
An indexed contribution is linear, even when borrowed or positively shared.
Cleanup records layout, not absence of other views or safe return authority. -/

@[expose] public section

namespace Aeneas.SepLogic

open Aeneas.Std

universe w w'

inductive Resource where
  | cell (base : Nat) (index : Nat) (bptr : BasePtr) (value : Cell)
  | cleanup (base : Nat) (size : Nat) (bptr : BasePtr) (owned : Bool)

namespace Resource

def base : Resource → Nat
  | .cell base _ _ _ | .cleanup base _ _ _ => base

def key : Resource → Option Nat
  | .cell _ index _ _ => some index
  | .cleanup _ _ _ _ => none

def Compatible (a b : Resource) : Prop :=
  a.base ≠ b.base ∨ a.key ≠ b.key

theorem Compatible.symm {a b : Resource} (h : a.Compatible b) : b.Compatible a := by
  unfold Compatible at *
  grind

theorem not_compatible_self (a : Resource) : ¬ a.Compatible a := by
  simp [Compatible]

def Holds (s : Heap) : Resource → Prop
  | .cell base index bptr c =>
    ∃ block, s.allocations base = some block ∧ s.live block = true ∧
      block.bptr = bptr ∧ block.repr[index]? = some c
  | .cleanup base size bptr own =>
    ∃ block, s.allocations base = some block ∧ block.repr.length = size ∧
      s.live block = true ∧ block.bptr = bptr ∧ block.owned = own

theorem Holds.live {s : Heap} {r : Resource}
    (h : r.Holds s) : ∃ block, s.allocations r.base = some block := by
  cases r
  · exact h.imp fun _ hc => hc.1
  · exact h.imp fun _ hc => hc.1

/-- Logical separation of views does not imply physical separation. The heap
invariant enforces the actual permission algebra when their addresses coincide. -/
theorem Holds.overlapCompatible {s : Heap} {i j x y : Nat} {a b : BasePtr} {c d : Cell}
    (hinv : s.Inv) (different : i ≠ j)
    (left : Resource.Holds s (.cell i x a c))
    (right : Resource.Holds s (.cell j y b d))
    (address : a.val + x = b.val + y) : Cell.compatible c d = true := by
  obtain ⟨blk, hl, hlive, ha, hc⟩ := left
  obtain ⟨other, hr, hrive, hb, hd⟩ := right
  have compat := hinv.compatible hl hr different
  have active : blk.active = true := by
    simp only [Heap.live, Bool.and_eq_true] at hlive
    exact hlive.1
  have active' : other.active = true := by
    simp only [Heap.live, Bool.and_eq_true] at hrive
    exact hrive.1
  simp only [Heap.compatible, active, active', Bool.not_true, Bool.false_or] at compat
  have hm : (c, x) ∈ blk.repr.zipIdx := by
    apply List.mem_of_getElem? (i := x)
    simp [List.getElem?_zipIdx, hc]
  have hm' : (d, y) ∈ other.repr.zipIdx := by
    apply List.mem_of_getElem? (i := y)
    simp [List.getElem?_zipIdx, hd]
  have row := List.all_eq_true.mp compat (c, x) hm
  have entry := List.all_eq_true.mp row (d, y) hm'
  simpa [ha, hb, address] using entry

theorem Holds.noAliases_unique {s : Heap} {r : Resource} {owner root : Nat}
    {blk : Block} (hinv : s.Inv) (noAliases : s.noAliases owner root = true)
    (holds : Resource.Holds s r) (lookup : s.allocations r.base = some blk)
    (sameRoot : blk.root = root) : r.base = owner := by
  have hv : s.live blk = true := by
    cases r
    · obtain ⟨actual, hl, hv, _, _⟩ := holds
      have he := Option.some.inj (hl.symm.trans lookup)
      exact he ▸ hv
    · obtain ⟨actual, hl, _, hv, _, _⟩ := holds
      have he := Option.some.inj (hl.symm.trans lookup)
      exact he ▸ hv
  have active : blk.active = true := by
    simp only [Heap.live, Bool.and_eq_true] at hv
    exact hv.1
  exact hinv.noAliases_unique noAliases lookup active sameRoot

end Resource

abbrev Fragment := Resource → Prop

namespace Fragment

def empty : Fragment := fun _ => False
def union (a b : Fragment) : Fragment := fun r => a r ∨ b r
def single (r : Resource) : Fragment := fun r' => r' = r

instance : EmptyCollection Fragment := ⟨empty⟩
instance : Union Fragment := ⟨union⟩

def Disjoint (a b : Fragment) : Prop :=
  ∀ r, a r → ∀ r', b r' → r.Compatible r'

def Matches (s : Heap) (h : Fragment) : Prop :=
  ∀ r, h r → r.Holds s

@[simp] theorem empty_union (h : Fragment) : ∅ ∪ h = h := by
  funext r
  exact false_or _

@[simp] theorem union_empty (h : Fragment) : h ∪ ∅ = h := by
  funext r
  exact or_false _

theorem union_assoc (a b c : Fragment) : a ∪ b ∪ c = a ∪ (b ∪ c) := by
  funext r
  exact propext or_assoc

theorem union_comm (a b : Fragment) : a ∪ b = b ∪ a := by
  funext r
  exact propext or_comm

theorem Disjoint.symm {a b : Fragment} (h : a.Disjoint b) : b.Disjoint a :=
  fun _ hb _ ha => (h _ ha _ hb).symm

@[simp] theorem disjoint_empty_left (h : Fragment) : (∅ : Fragment).Disjoint h :=
  fun _ hf => hf.elim

@[simp] theorem disjoint_empty_right (h : Fragment) : h.Disjoint ∅ :=
  (disjoint_empty_left h).symm

theorem disjoint_union_left {a b c : Fragment} :
    (a ∪ b).Disjoint c ↔ a.Disjoint c ∧ b.Disjoint c := by
  constructor
  · intro h
    exact ⟨fun _ ha => h _ (.inl ha), fun _ hb => h _ (.inr hb)⟩
  · rintro ⟨ha, hb⟩ r (hr | hr)
    · exact ha r hr
    · exact hb r hr

theorem disjoint_union_right {a b c : Fragment} :
    a.Disjoint (b ∪ c) ↔ a.Disjoint b ∧ a.Disjoint c := by
  constructor
  · intro h
    exact ⟨fun _ ha _ hb => h _ ha _ (.inl hb),
      fun _ ha _ hc => h _ ha _ (.inr hc)⟩
  · rintro ⟨hb, hc⟩ r hr r' (hr' | hr')
    · exact hb r hr r' hr'
    · exact hc r hr r' hr'

@[simp] theorem matches_empty (s : Heap) :
    Matches s ∅ := fun _ h => h.elim

@[simp] theorem matches_union (s : Heap)
    (a b : Fragment) : Matches s (a ∪ b) ↔ Matches s a ∧ Matches s b := by
  constructor
  · intro h
    exact ⟨fun _ ha => h _ (.inl ha), fun _ hb => h _ (.inr hb)⟩
  · rintro ⟨ha, hb⟩ r (hr | hr)
    · exact ha r hr
    · exact hb r hr

@[simp] theorem matches_single (s : Heap) (r : Resource) :
    Matches s (single r) ↔ r.Holds s := by
  constructor
  · exact fun h => h r rfl
  · rintro h _ rfl
    exact h

end Fragment


end Aeneas.SepLogic
