module

public import Aeneas.Std.Heap
import all Aeneas.Std.Heap

public section

namespace Aeneas

/-- A partial commutative monoid: a total `∪`, meaningful on `Compatible` inputs. -/
class PartialCommMonoid (α : Type u) [EmptyCollection α] [Union α] where
  Compatible : α → α → Prop
  compatible_comm {a b : α} : Compatible a b → Compatible b a
  compatible_empty_left (a : α) : Compatible ∅ a
  compatible_assoc (a b c : α) :
    Compatible a b ∧ Compatible (a ∪ b) c ↔
      Compatible b c ∧ Compatible a (b ∪ c)
  union_assoc {a b c : α} :
    Compatible a b → Compatible (a ∪ b) c →
      a ∪ b ∪ c = a ∪ (b ∪ c)
  empty_union (a : α) : ∅ ∪ a = a
  union_empty (a : α) : a ∪ ∅ = a
  union_comm_of_compatible {a b : α} :
    Compatible a b → a ∪ b = b ∪ a

end Aeneas

namespace Aeneas.Std

namespace Loc

@[simp] theorem allocId_add (l : Loc) (i : Nat) : (l.add i).allocId = l.allocId := rfl

@[simp] theorem offset_add (l : Loc) (i : Nat) : (l.add i).offset = l.offset + i := rfl

@[simp] theorem add_zero (l : Loc) : l.add 0 = l := rfl

theorem add_add (l : Loc) (i j : Nat) :
    (l.add i).add j = l.add (i + j) := by
  simp [Loc.add, Loc.allocId, Loc.offset, Nat.add_assoc]

end Loc

namespace Heap

private instance : Coe Heap HeapImpl := ⟨Heap.impl⟩
private instance : Coe HeapImpl Heap := ⟨Heap.mk⟩

private theorem ext_impl {h₁ h₂ : Heap}
    (hEq : h₁.impl = h₂.impl) : h₁ = h₂ := by
  cases h₁
  cases h₂
  cases hEq
  rfl

private theorem mem_union {address : Loc} {h₁ h₂ : Heap} :
    address ∈ h₁ ∪ h₂ ↔ address ∈ h₁ ∨ address ∈ h₂ :=
  Finmap.mem_union

private theorem lookup_union_left {address : Loc}
    {h₁ h₂ : Heap} (hMem : address ∈ h₁) :
    (h₁ ∪ h₂).lookup address = h₁.lookup address :=
  congrArg (Option.bind · Slot.cell?) (Finmap.lookup_union_left hMem)

private theorem mem_of_lookup_eq_some {address : Loc} {h : Heap} {cell : HeapCell}
    (hLookup : h.lookup address = some cell) : address ∈ h := by
  obtain ⟨slot, hSlot, -⟩ := Option.bind_eq_some_iff.mp hLookup
  exact Finmap.mem_of_lookup_eq_some hSlot

private theorem mem_insert {address insertedAddress : Loc}
    {cell : Slot} {h : Heap} :
    address ∈ h.insert insertedAddress cell ↔
      address = insertedAddress ∨ address ∈ h :=
  Finmap.mem_insert

private theorem insert_union {address : Loc}
    {cell : Slot} {h₁ h₂ : Heap} :
    (h₁ ∪ h₂).insert address cell =
      h₁.insert address cell ∪ h₂ := by
  apply Heap.ext_impl
  exact Finmap.insert_union

private theorem union_assoc' (h₁ h₂ h₃ : Heap) :
    (h₁ ∪ h₂) ∪ h₃ = h₁ ∪ (h₂ ∪ h₃) := by
  apply Heap.ext_impl
  exact Finmap.union_assoc

@[simp]
theorem empty_union (h : Heap) : empty ∪ h = h := by
  apply Heap.ext_impl
  exact Finmap.empty_union

@[simp]
theorem union_empty (h : Heap) : h ∪ empty = h := by
  apply Heap.ext_impl
  exact Finmap.union_empty

instance instPartialCommMonoid : PartialCommMonoid Heap where
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

theorem union_right_cancel {h₁ h₂ frame : Heap}
    (hCompatible₁ : PartialCommMonoid.Compatible h₁ frame)
    (hCompatible₂ : PartialCommMonoid.Compatible h₂ frame)
    (hEq : h₁ ∪ frame = h₂ ∪ frame) : h₁ = h₂ := by
  apply Heap.ext_impl
  exact (Finmap.union_cancel hCompatible₁ hCompatible₂).mp (congrArg Heap.impl hEq)

theorem mem_singleton {α : Type} {q : RawPtr α M} {value : α} {address : Loc} :
    address ∈ singleton q value ↔ address = q.addr := by
  show address ∈ (Finmap.singleton q.addr (Slot.live ⟨α, value⟩) : HeapImpl) ↔ _
  exact Finmap.mem_singleton _ _ _

theorem mem_endMarker {l address : Loc} {owned : Bool} :
    address ∈ endMarker l owned ↔ address = l := by
  show address ∈ (Finmap.singleton l (Slot.dead owned) : HeapImpl) ↔ _
  exact Finmap.mem_singleton _ _ _

private theorem lookup_singleton {α : Type} (q : RawPtr α M) (value : α) :
    (singleton q value).lookup q.addr = some ⟨α, value⟩ := by
  simp [singleton, Heap.lookup, Slot.cell?]

/-- The cell does not depend on the pointer's mutability. -/
theorem singleton_eq_of_addr {α : Type} {q : RawPtr α M} {r : RawPtr α M'}
    (hAddr : q.addr = r.addr) (value : α) : singleton q value = singleton r value := by
  unfold singleton
  rw [hAddr]

@[simp]
theorem not_contains_empty {α : Type} (q : RawPtr α M) :
    ¬ contains (∅ : Heap) q := by
  change ¬ match (Finmap.lookup q.addr (∅ : HeapImpl)).bind Slot.cell? with
    | none => False
    | some ⟨β, _⟩ => β = α
  simp

@[simp] theorem rangeHeap_nil {α : Type} (l : Loc) :
    rangeHeap l ([] : List α) = empty := rfl

@[simp] theorem rangeHeap_cons {α : Type} (q : RawPtr α M) (value : α)
    (rest : List α) :
    rangeHeap q.addr (value :: rest) = singleton q value ∪ rangeHeap (q.addr.add 1) rest := by
  show singleton (⟨q.addr⟩ : MutRawPtr α) value ∪ _ = _
  rw [singleton_eq_of_addr (q := (⟨q.addr⟩ : MutRawPtr α)) (r := q) rfl]

@[simp] theorem rangeHeap_singleton {α : Type} (q : RawPtr α M) (value : α) :
    rangeHeap q.addr [value] = singleton q value := by
  rw [rangeHeap_cons, rangeHeap_nil, Heap.union_empty]

theorem mem_rangeHeap {α : Type} {l : Loc} {values : List α} {address : Loc} :
    address ∈ rangeHeap l values ↔
      ∃ i, i < values.length ∧ address = l.add i := by
  induction values generalizing l with
  | nil =>
      simp only [rangeHeap_nil, List.length_nil, Nat.not_lt_zero, false_and,
        exists_false, iff_false]
      intro hMem
      exact (Finmap.notMem_empty (a := address)) hMem
  | cons value rest ih =>
      have hShift : ∀ i : Nat, (l.add 1).add i = l.add (i + 1) := by
        intro i; rw [Loc.add_add, Nat.add_comm]
      rw [rangeHeap_cons (⟨l⟩ : MutRawPtr α), Heap.mem_union, mem_singleton, ih]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, by simp, rfl⟩
        · exact ⟨i + 1, by simpa using hi, by rw [hShift]⟩
      · rintro ⟨i, hi, rfl⟩
        cases i with
        | zero => exact Or.inl rfl
        | succ j => exact Or.inr ⟨j, by simpa using hi, by rw [hShift]⟩

private theorem mem_deadRange {l address : Loc} {n : Nat} :
    address ∈ deadRange l n ↔ ∃ i, i < n ∧ address = l.add i := by
  induction n generalizing l with
  | zero =>
      simp only [Nat.not_lt_zero, false_and, exists_false, iff_false]
      intro hMem
      exact (Finmap.notMem_empty (a := address)) hMem
  | succ n ih =>
      have hShift : ∀ i : Nat, (l.add 1).add i = l.add (i + 1) := by
        intro i; rw [Loc.add_add, Nat.add_comm]
      have hSingle : address ∈ (⟨Finmap.singleton l (Slot.dead false)⟩ : Heap) ↔ address = l :=
        Finmap.mem_singleton _ _ _
      show address ∈ (⟨Finmap.singleton l (Slot.dead false)⟩ : Heap) ∪ deadRange (l.add 1) n ↔ _
      rw [Heap.mem_union, hSingle, ih]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, by omega, rfl⟩
        · exact ⟨i + 1, by omega, by rw [hShift]⟩
      · rintro ⟨i, hi, rfl⟩
        cases i with
        | zero => exact Or.inl rfl
        | succ j => exact Or.inr ⟨j, by omega, by rw [hShift]⟩

private theorem lookup_deadRange {l : Loc} {n i : Nat} (hi : i < n) :
    (deadRange l n).impl.lookup (l.add i) = some (.dead false) := by
  induction n generalizing l i with
  | zero => omega
  | succ n ih =>
      show Finmap.lookup (l.add i)
        ((Finmap.singleton l (Slot.dead false) : HeapImpl) ∪ (deadRange (l.add 1) n).impl) = _
      cases i with
      | zero =>
          show Finmap.lookup l ((Finmap.singleton l (Slot.dead false) : HeapImpl) ∪ _) = _
          rw [Finmap.lookup_union_left ((Finmap.mem_singleton _ _ _).mpr rfl)]
          exact Finmap.lookup_singleton_eq
      | succ j =>
          have hNotMem : l.add (j + 1) ∉ (Finmap.singleton l (Slot.dead false) : HeapImpl) := by
            rw [Finmap.mem_singleton]
            intro hEq
            have hOffset := congrArg Loc.offset hEq
            simp only [Loc.offset_add] at hOffset
            omega
          rw [Finmap.lookup_union_right hNotMem,
            show l.add (j + 1) = (l.add 1).add j by rw [Loc.add_add, Nat.add_comm]]
          exact ih (by omega)

theorem rangeHeap_append {α : Type} (l : Loc) (xs ys : List α) :
    rangeHeap l (xs ++ ys) =
      rangeHeap l xs ∪ rangeHeap (l.add xs.length) ys := by
  induction xs generalizing l with
  | nil => simp
  | cons value rest ih =>
      have hShift : (l.add 1).add rest.length = l.add (rest.length + 1) := by
        rw [Loc.add_add, Nat.add_comm]
      rw [List.cons_append, rangeHeap_cons (⟨l⟩ : MutRawPtr α), rangeHeap_cons (⟨l⟩ : MutRawPtr α), ih, List.length_cons,
        hShift, Heap.union_assoc']

theorem compatible_rangeHeap_append {α : Type} (l : Loc) (xs ys : List α) :
    PartialCommMonoid.Compatible (rangeHeap l xs)
      (rangeHeap (l.add xs.length) ys) := by
  intro address hLeft hRight
  obtain ⟨i, hi, hL⟩ := mem_rangeHeap.mp hLeft
  obtain ⟨j, -, hR⟩ := mem_rangeHeap.mp hRight
  rw [Loc.add_add] at hR
  have hOffset : l.offset + i = l.offset + (xs.length + j) :=
    (congrArg Loc.offset hL).symm.trans (congrArg Loc.offset hR)
  omega

theorem not_mem_freshBase {h : Heap} {address : Loc}
    (hBase : address.allocId = freshBase h) : address ∉ h := by
  intro hMem
  have hMemKeys : address ∈ h.keys := Finmap.mem_keys.mpr hMem
  have hImage : freshBase h ∈ h.keys.image Loc.allocId :=
    Finset.mem_image.mpr ⟨_, hMemKeys, hBase⟩
  have hLe : freshBase h ≤ (h.keys.image Loc.allocId).sup id :=
    Finset.le_sup (f := fun a : AllocId => a) hImage
  have hSucc : (h.keys.image Loc.allocId).sup id + 1 ≤
      (h.keys.image Loc.allocId).sup id := hLe
  exact Nat.not_succ_le_self _ hSucc

theorem compatible_freshLoc {α : Type} (h : Heap) (values : List α) (owned : Bool) :
    PartialCommMonoid.Compatible (allocation (freshLoc h) values owned) h := by
  intro address hFresh hMem
  apply not_mem_freshBase (h := h) _ hMem
  rcases Heap.mem_union.mp hFresh with hRange | hEnd
  · obtain ⟨i, -, rfl⟩ := mem_rangeHeap.mp hRange
    rfl
  · rw [mem_endMarker.mp hEnd]
    rfl

theorem compatible_rangeHeap_endMarker {α : Type} (l : Loc) (values : List α) (owned : Bool) :
    PartialCommMonoid.Compatible (rangeHeap l values) (endMarker (l.add values.length) owned) := by
  intro address hRange hEnd
  obtain ⟨i, hi, rfl⟩ := mem_rangeHeap.mp hRange
  have hOffset := congrArg Loc.offset (mem_endMarker.mp hEnd)
  simp only [Loc.offset_add] at hOffset
  omega

namespace Sub

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

end Sub

theorem mem_of_isLive {h : Heap} {l : Loc} (hLive : isLive h l) : l ∈ h := by
  obtain ⟨cell, hLookup⟩ := Option.isSome_iff_exists.mp hLive
  exact Heap.mem_of_lookup_eq_some hLookup

theorem isLive_of_contains {α : Type} {h : Heap} {q : RawPtr α M}
    (hContains : contains h q) : isLive h q.addr := by
  unfold contains at hContains
  unfold isLive
  split at hContains
  · contradiction
  · rename_i cell hLookup
    simp [hLookup]

theorem mem_of_contains {α : Type} {h : Heap} {q : RawPtr α M}
    (hContains : contains h q) : q.addr ∈ h :=
  mem_of_isLive (isLive_of_contains hContains)

theorem disjoint_contains_false {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains₁ : contains h₁ q)
    (hContains₂ : contains h₂ q) : False :=
  hCompatible q.addr (mem_of_contains hContains₁)
    (mem_of_contains hContains₂)

theorem contains_union_left {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hContains : contains h₁ q) : contains (h₁ ∪ h₂) q := by
  have hMem : q.addr ∈ h₁ := mem_of_contains hContains
  unfold contains at hContains ⊢
  rw [Heap.lookup_union_left hMem]
  exact hContains

theorem isLive_union_left {h₁ h₂ : Heap} {l : Loc}
    (hLive : isLive h₁ l) : isLive (h₁ ∪ h₂) l := by
  have hMem : l ∈ h₁ := mem_of_isLive hLive
  unfold isLive at hLive ⊢
  rw [Heap.lookup_union_left hMem]
  exact hLive

theorem read_union_left {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hContains : contains h₁ q) :
    (h₁ ∪ h₂).read q (contains_union_left hContains) =
      h₁.read q hContains := by
  have hMem : q.addr ∈ h₁ := mem_of_contains hContains
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
          ((Heap.lookup_union_left hMem).trans hLookup₁)
      cases hCells
      rfl

theorem update_union_left {α : Type} {h₁ h₂ : Heap}
    (q : RawPtr α M) (value : α) (hContains : contains h₁ q) :
    (h₁ ∪ h₂).update q value (contains_union_left hContains) =
      h₁.update q value hContains ∪ h₂ := by
  exact Heap.insert_union

private theorem disjoint_insert_left {l : Loc} {cell : Slot}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hMem : l ∈ h₁) :
    PartialCommMonoid.Compatible (h₁.insert l cell) h₂ := by
  intro address hMem₁ hMem₂
  rcases Heap.mem_insert.mp hMem₁ with rfl | hMem₁
  · exact hCompatible _ hMem hMem₂
  · exact hCompatible address hMem₁ hMem₂

theorem disjoint_update_left {α : Type} {q : RawPtr α M} {value : α}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ q) :
    PartialCommMonoid.Compatible
      (h₁.update q value hContains) h₂ :=
  disjoint_insert_left hCompatible (mem_of_contains hContains)

theorem isOwnedEnd_union_left {h₁ h₂ : Heap} {l : Loc} (hEnd : isOwnedEnd h₁ l) :
    isOwnedEnd (h₁ ∪ h₂) l := by
  show Finmap.lookup l (h₁.impl ∪ h₂.impl) = _
  rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hEnd)]
  exact hEnd

/-- An owned end marker holds no value. -/
theorem not_isLive_of_isOwnedEnd {h : Heap} {l : Loc} (hEnd : isOwnedEnd h l) :
    ¬ isLive h l := by
  unfold isOwnedEnd at hEnd
  simp [isLive, Heap.lookup, hEnd, Slot.cell?]

theorem canDealloc_union_left {h₁ h₂ : Heap} {l : Loc} {n : Nat} (hDealloc : canDealloc h₁ l n) :
    canDealloc (h₁ ∪ h₂) l n :=
  ⟨hDealloc.1, fun i hi => isLive_union_left (hDealloc.2.1 i hi),
    isOwnedEnd_union_left hDealloc.2.2⟩

/-- The slots that `dealloc` kills are already in the heap. -/
private theorem mem_of_canDealloc {h : Heap} {l : Loc} {n i : Nat} (hDealloc : canDealloc h l n)
    (hi : i < n + 1) : l.add i ∈ h := by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact mem_of_isLive (hDealloc.2.1 i hi)
  · exact Finmap.mem_of_lookup_eq_some hDealloc.2.2

theorem disjoint_dealloc_left {h₁ h₂ : Heap} {l : Loc} {n : Nat}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hDealloc : canDealloc h₁ l n) :
    PartialCommMonoid.Compatible (h₁.dealloc l n hDealloc) h₂ := by
  intro address hMem hMem₂
  change address ∈ deadRange l (n + 1) ∪ h₁ at hMem
  rcases Heap.mem_union.mp hMem with hDead | hMem₁
  · obtain ⟨i, hi, rfl⟩ := mem_deadRange.mp hDead
    exact hCompatible _ (mem_of_canDealloc hDealloc hi) hMem₂
  · exact hCompatible _ hMem₁ hMem₂

theorem dealloc_union_left {h₁ h₂ : Heap} {l : Loc} {n : Nat} (hDealloc : canDealloc h₁ l n) :
    (h₁ ∪ h₂).dealloc l n (canDealloc_union_left hDealloc) = h₁.dealloc l n hDealloc ∪ h₂ :=
  (Heap.union_assoc' _ _ _).symm

/-- Deallocated slots stay in the heap, so their allocation id is never handed out again. -/
theorem mem_dealloc {h : Heap} {l : Loc} {n i : Nat} (hDealloc : canDealloc h l n) (hi : i ≤ n) :
    l.add i ∈ h.dealloc l n hDealloc :=
  Heap.mem_union.mpr (Or.inl (mem_deadRange.mpr ⟨i, by omega, rfl⟩))

private theorem lookup_dealloc {h : Heap} {l : Loc} {n i : Nat} (hDealloc : canDealloc h l n)
    (hi : i ≤ n) : (h.dealloc l n hDealloc).impl.lookup (l.add i) = some (.dead false) := by
  show Finmap.lookup (l.add i) ((deadRange l (n + 1)).impl ∪ h.impl) = _
  rw [Finmap.lookup_union_left (mem_deadRange.mpr ⟨i, by omega, rfl⟩)]
  exact lookup_deadRange (by omega)

/-- A deallocated slot cannot be read or written. -/
theorem not_isLive_dealloc {h : Heap} {l : Loc} {n i : Nat}
    (hDealloc : canDealloc h l n) (hi : i ≤ n) :
    ¬ isLive (h.dealloc l n hDealloc) (l.add i) := by
  simp [isLive, Heap.lookup, lookup_dealloc hDealloc hi, Slot.cell?]

/-- After `dealloc`, the end marker is dead, so the allocation cannot be deallocated again. -/
theorem not_isOwnedEnd_dealloc {h : Heap} {l : Loc} {n : Nat} (hDealloc : canDealloc h l n) :
    ¬ isOwnedEnd (h.dealloc l n hDealloc) (l.add n) := by
  simp [isOwnedEnd, lookup_dealloc hDealloc (Nat.le_refl n)]

/-- Allocation leaves the slots already in the heap untouched. -/
theorem isLive_freshHeap_of_mem {β : Type} {h : Heap} {values : List β} {owned : Bool}
    {l : Loc} (hMem : l ∈ h) : isLive (freshHeap h values owned) l ↔ isLive h l := by
  have hNotMem : l ∉ allocation (freshLoc h) values owned :=
    fun hFresh => compatible_freshLoc h values owned l hFresh hMem
  unfold isLive
  rw [show (freshHeap h values owned).lookup l = h.lookup l from
    congrArg (Option.bind · Slot.cell?) (Finmap.lookup_union_right hNotMem)]

/-- The end marker of an allocation is in the heap, so even an empty allocation reserves its id. -/
theorem mem_freshHeap_end {α : Type} {owned : Bool} (h : Heap) (values : List α) :
    (freshLoc h).add values.length ∈ freshHeap h values owned :=
  Heap.mem_union.mpr (Or.inl (Heap.mem_union.mpr (Or.inr (mem_endMarker.mpr rfl))))

private theorem lookup_freshHeap_end {α : Type} (h : Heap) (values : List α) (owned : Bool) :
    (freshHeap h values owned).impl.lookup ((freshLoc h).add values.length) =
      some (.dead owned) := by
  have hNotRange :
      (freshLoc h).add values.length ∉ (rangeHeap (freshLoc h) values).impl := by
    intro hRange
    obtain ⟨i, hi, hEq⟩ := mem_rangeHeap.mp hRange
    have hOffset := congrArg Loc.offset hEq
    simp only [Loc.offset_add] at hOffset
    omega
  have hEnd : (freshLoc h).add values.length ∈
      (endMarker ((freshLoc h).add values.length) owned).impl :=
    mem_endMarker.mpr rfl
  show Finmap.lookup _ (((rangeHeap (freshLoc h) values).impl ∪
    (endMarker ((freshLoc h).add values.length) owned).impl) ∪ h.impl) = _
  rw [Finmap.lookup_union_left (Finmap.mem_union.mpr (Or.inr hEnd)),
    Finmap.lookup_union_right hNotRange]
  simp [endMarker]

/-- The end marker of a fresh allocation holds no value. -/
theorem not_isLive_freshHeap_end {β : Type} {owned : Bool} (h : Heap) (values : List β) :
    ¬ isLive (freshHeap h values owned) ((freshLoc h).add values.length) := by
  simp [isLive, Heap.lookup, lookup_freshHeap_end, Slot.cell?]

/-- The end marker of a fresh allocation is owned exactly when the allocation is. -/
theorem isOwnedEnd_freshHeap_end_iff {α : Type} (h : Heap) (values : List α) (owned : Bool) :
    isOwnedEnd (freshHeap h values owned) ((freshLoc h).add values.length) ↔ owned = true := by
  simp [isOwnedEnd, lookup_freshHeap_end]

theorem disjoint_singleton {α : Type} {q : RawPtr α M} {r : RawPtr α M'} {value₁ value₂ : α}
    (hNe : q.addr ≠ r.addr) :
    PartialCommMonoid.Compatible
      (singleton q value₁) (singleton r value₂) := by
  intro address hMem₁ hMem₂
  exact hNe ((mem_singleton.mp hMem₁).symm.trans (mem_singleton.mp hMem₂))

theorem contains_singleton {α : Type} (q : RawPtr α M) (value : α) :
    contains (singleton q value) q := by
  simp [contains, singleton, Heap.lookup, Slot.cell?]

theorem read_singleton {α : Type} (q : RawPtr α M) (value : α)
    (hContains : contains (singleton q value) q) :
    (singleton q value).read q hContains = value := by
  unfold Heap.read
  split
  · rename_i hLookup
    rw [lookup_singleton] at hLookup
    contradiction
  · rename_i β stored hLookup
    rw [lookup_singleton] at hLookup
    cases hLookup
    rfl

theorem update_singleton {α : Type} (q : RawPtr α M)
    (oldValue newValue : α)
    (hContains : contains (singleton q oldValue) q) :
    (singleton q oldValue).update q newValue hContains =
      singleton q newValue := by
  apply Heap.ext_impl
  simp [Heap.update, singleton, Heap.insert]

theorem Sub.contains {α : Type} {A h : Heap} {q : RawPtr α M} (hSub : Heap.Sub A h)
    (hContains : contains A q) : contains h q := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact contains_union_left hContains

theorem Sub.isLive {A h : Heap} {l : Loc} (hSub : Heap.Sub A h)
    (hLive : isLive A l) : isLive h l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact isLive_union_left hLive

theorem Sub.isOwnedEnd {l : Loc} {h : Heap} (hSub : Heap.Sub (endMarker l true) h) :
    isOwnedEnd h l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  have hMem : l ∈ endMarker l true := mem_endMarker.mpr rfl
  show Finmap.lookup l ((endMarker l true).impl ∪ rest.impl) = _
  rw [Finmap.lookup_union_left hMem]
  simp [endMarker]

/-- The empty heap has no owned allocation. -/
@[simp] theorem not_isOwnedEnd_empty (l : Loc) : ¬ isOwnedEnd (∅ : Heap) l := by
  change ¬ Finmap.lookup l (∅ : HeapImpl) = some (Slot.dead true)
  simp

theorem isLive_rangeHeap {α : Type} {l : Loc} {values : List α} {i : Nat}
    (hIndex : i < values.length) : isLive (rangeHeap l values) (l.add i) := by
  induction values generalizing l i with
  | nil => simp at hIndex
  | cons value rest ih =>
    rw [rangeHeap_cons (⟨l⟩ : MutRawPtr α)]
    cases i with
    | zero => exact isLive_union_left (isLive_of_contains (contains_singleton _ value))
    | succ j =>
      have hCompatible : PartialCommMonoid.Compatible (singleton (⟨l⟩ : MutRawPtr α) value)
          (rangeHeap (l.add 1) rest) := by
        have hAppend := compatible_rangeHeap_append l [value] rest
        rwa [rangeHeap_singleton (⟨l⟩ : MutRawPtr α)] at hAppend
      rw [PartialCommMonoid.union_comm_of_compatible hCompatible,
        show l.add (j + 1) = (l.add 1).add j by rw [Loc.add_add, Nat.add_comm]]
      exact isLive_union_left (ih (by simpa using hIndex))

/-- The values of a fresh allocation are live. -/
theorem isLive_freshHeap {α : Type} {h : Heap} {values : List α} {owned : Bool} {i : Nat}
    (hIndex : i < values.length) :
    isLive (freshHeap h values owned) ((freshLoc h).add i) :=
  Sub.isLive ((Sub.union_left (compatible_rangeHeap_endMarker _ _ _)).trans
    (Sub.union_left (compatible_freshLoc _ _ _))) (isLive_rangeHeap hIndex)

theorem read_of_sub {α : Type} {q : RawPtr α M} {value : α} {h : Heap}
    (hSub : Heap.Sub (singleton q value) h)
    (hContains : contains h q) : h.read q hContains = value := by
  obtain ⟨rest, hCompatible, rfl⟩ := hSub
  have hContainsSingleton := contains_singleton q value
  rw [show hContains = contains_union_left hContainsSingleton from
      Subsingleton.elim _ _,
    read_union_left hContainsSingleton, read_singleton]

end Heap

end Aeneas.Std