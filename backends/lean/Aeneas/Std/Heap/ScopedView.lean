module

public import Aeneas.Std.Heap.ExclusiveReturn
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Lemmas
import all Aeneas.Std.Heap.Allocation
import all Aeneas.Std.Core.Ptr

@[expose] public section

namespace Aeneas.Std

namespace Heap

def StableExcept (id : Nat) (s₀ s₁ : Heap) : Prop :=
  s₁.next = s₀.next ∧ ∀ other, other ≠ id → s₁.allocations other = s₀.allocations other

theorem StableExcept.trans {id : Nat} (first : StableExcept id s₀ s₁)
    (second : StableExcept id s₁ s₂) : StableExcept id s₀ s₂ :=
  ⟨second.1.trans first.1, fun other different =>
    (second.2 other different).trans (first.2 other different)⟩

theorem modify_stable {repr : Repr T} {p : RawPtr T} {s₀ s₁ : Heap}
    {change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r)}
    (run : modify repr p change s₀ = some s₁) : StableExcept p.provenance s₀ s₁ := by
  unfold modify at run
  cases hl : s₀.allocations p.provenance
  · simp [hl] at run
  · simp only [hl, Bind.bind, Option.bind] at run
    split at run
    · rename_i blk guard
      cases changed : change blk.bytes (p.offsetFrom blk.bptr)
      · simp [changed] at run
      · simp only [changed] at run
        have final := (commit_success _ _ run).1
        subst s₁
        exact ⟨rfl, fun other different => by simp [storeRepr, update, different]⟩
    · contradiction

theorem retire_stable (s : Heap) (id : Nat) : StableExcept id s (s.retire id) :=
  ⟨rfl, fun other different => by simp [retire, update, different]⟩

def NewView (s₀ s₁ : Heap) : Prop :=
  s₁.next = s₀.next + 1 ∧
    ∀ other, other ≠ s₀.next → s₁.allocations other = s₀.allocations other

/-- Metadata relevant to return authority; contents may change independently. -/
def returnShape (blk : Block) : BasePtr × Nat × Nat × Bool :=
  (blk.bptr, blk.root, blk.repr.length, blk.active)

/-- A completed collection of scopes. Old views retain their return metadata,
    while every newly issued view is retired. Byte updates are unrestricted. -/
def ClosedViews (s₀ s₁ : Heap) : Prop :=
  s₀.next ≤ s₁.next ∧
    (∀ id, id < s₀.next →
      (s₁.allocations id).map returnShape = (s₀.allocations id).map returnShape) ∧
    (∀ id blk, s₀.next ≤ id → s₁.allocations id = some blk → blk.active = false)

theorem ClosedViews.trans (first : ClosedViews s₀ s₁) (second : ClosedViews s₁ s₂) :
    ClosedViews s₀ s₂ := by
  refine ⟨first.1.trans second.1, ?_, ?_⟩
  · intro id bound
    exact (second.2.1 id (Nat.lt_of_lt_of_le bound first.1)).trans
      (first.2.1 id bound)
  · intro id blk bound lookup
    by_cases old : id < s₁.next
    · have shape := second.2.1 id old
      rw [lookup] at shape
      cases hl : s₁.allocations id
      · simp [hl] at shape
      · rename_i prior
        have eq := Option.some.inj (by simpa [hl] using shape)
        have active := congrArg (fun x : BasePtr × Nat × Nat × Bool => x.2.2.2) eq
        exact active.trans (first.2.2 id prior bound hl)
    · exact second.2.2 id blk (Nat.le_of_not_gt old) lookup

theorem newBlock_newView {repr : Repr T} {data : List (Vector Byte repr.size)}
    {bptr : BasePtr} {root : Option Nat} {s₀ s₁ : Heap} {p : RawPtr T}
    (run : newBlock repr data false bptr root s₀ = some (p, s₁)) :
    p.provenance = s₀.next ∧ NewView s₀ s₁ := by
  unfold newBlock at run
  simp only [Bool.not_false, Bool.true_or, Bool.and_true] at run
  split at run
  · obtain ⟨⟨id, next⟩, created, eq⟩ := Option.map_eq_some_iff.mp run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    obtain ⟨rfl, rfl⟩ := createRepr.success created
    exact ⟨rfl, rfl, fun other different => by simp [update, different]⟩
  · contradiction

theorem NewView.modify (created : NewView s₀ s₁)
    (changed : StableExcept s₀.next s₁ s₂) : NewView s₀ s₂ :=
  ⟨changed.1.trans created.1, fun other different =>
    (changed.2 other different).trans (created.2 other different)⟩

theorem endExposure_retire {repr : Repr T} {p : RawPtr T} {count : Nat} {s₀ s₁ : Heap}
    (run : endExposureAt repr p count 0 s₀ = some s₁) : s₁ = s₀.retire p.provenance := by
  unfold endExposureAt at run
  cases hl : s₀.allocations p.provenance
  · simp [hl] at run
  · simp only [hl, Bind.bind, Option.bind] at run
    split at run
    · exact (commit_success _ _ run).1
    · contradiction

end Heap

namespace SepLogic

/-- Any number of retired child views may intervene, together with independent
    byte updates to old allocations. No heap equality is required. -/
theorem RootReturn.after_closed_views {s₀ s₁ : Heap} {base : Nat}
    (hi : s₀.Inv) (bound : base < s₀.next) (authority : RootReturn s₀ base)
    (scope : Heap.ClosedViews s₀ s₁) : RootReturn s₁ base := by
  intro blk lookup
  have shape := scope.2.1 base bound
  rw [lookup] at shape
  cases oldLookup : s₀.allocations base
  · simp [oldLookup] at shape
  · rename_i old
    have same := Option.some.inj (by simpa [oldLookup] using shape)
    have hb := congrArg Prod.fst same
    have hr : blk.root = old.root :=
      congrArg (fun x : BasePtr × Nat × Nat × Bool => x.2.1) same
    have hlen := congrArg (fun x : BasePtr × Nat × Nat × Bool => x.2.2.1) same
    obtain ⟨root, rootLookup, baseEq, lengthEq, aliases⟩ := authority old oldLookup
    have rootShape := scope.2.1 old.root (hi.base_lt rootLookup)
    rw [rootLookup] at rootShape
    cases newRootLookup : s₁.allocations old.root
    · simp [newRootLookup] at rootShape
    · rename_i newRoot
      have rootSame := Option.some.inj (by simpa [newRootLookup] using rootShape)
      refine ⟨newRoot, by simpa [hr] using newRootLookup, ?_, ?_, ?_⟩
      · exact hb.trans (baseEq.trans (congrArg Prod.fst rootSame).symm)
      · exact hlen.trans (lengthEq.trans
          (congrArg (fun x : BasePtr × Nat × Nat × Bool => x.2.2.1) rootSame).symm)
      · apply List.all_eq_true.mpr
        intro id member
        by_cases prior : id < s₀.next
        · have entry := List.all_eq_true.mp aliases id (List.mem_range.mpr prior)
          have eq := scope.2.1 id prior
          cases before : s₀.allocations id
          · cases after : s₁.allocations id
            · simp
            · simp [before, after] at eq
          · rename_i beforeBlock
            cases after : s₁.allocations id
            · simp [before, after] at eq
            · rename_i afterBlock
              have same := Option.some.inj (by simpa [before, after] using eq)
              have roots : afterBlock.root = beforeBlock.root :=
                congrArg (fun x : BasePtr × Nat × Nat × Bool => x.2.1) same
              have active : afterBlock.active = beforeBlock.active :=
                congrArg (fun x : BasePtr × Nat × Nat × Bool => x.2.2.2) same
              simpa [before, after, roots, active, hr] using entry
        · cases after : s₁.allocations id
          · simp
          · simp [scope.2.2 id _ (Nat.le_of_not_gt prior) after]

/-- Retiring a nested exposure restores the outer root's no-alias authority;
    new metadata is retained, not erased or equated with the original heap. -/
theorem RootReturn.after_scoped_view {s₀ s₁ : Heap} {base : Nat}
    (hi : s₀.Inv) (bound : base < s₀.next) (authority : RootReturn s₀ base)
    (scope : Heap.NewView s₀ s₁)
    (inactive : ∀ blk, s₁.allocations s₀.next = some blk → blk.active = false) :
    RootReturn s₁ base := by
  intro blk lookup
  have original : s₀.allocations base = some blk := by
    rw [← scope.2 base (Nat.ne_of_lt bound)]
    exact lookup
  obtain ⟨root, hr, hb, hlen, aliases⟩ := authority blk original
  have rootDifferent : blk.root ≠ s₀.next := Nat.ne_of_lt (hi.base_lt hr)
  refine ⟨root, by rw [scope.2 _ rootDifferent]; exact hr, hb, hlen, ?_⟩
  apply List.all_eq_true.mpr
  intro id member
  by_cases fresh : id = s₀.next
  · subst id
    cases hl : s₁.allocations s₀.next
    · simp
    · simp [inactive _ hl]
  · have old : id < s₀.next := by
      have bound' := List.mem_range.mp member
      rw [scope.1] at bound'
      agrind
    have entry := List.all_eq_true.mp aliases id (List.mem_range.mpr old)
    simpa only [scope.2 id fresh] using entry

end SepLogic

end Aeneas.Std
