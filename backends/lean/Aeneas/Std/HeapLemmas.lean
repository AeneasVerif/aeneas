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

@[simp] theorem allocId_shift (l : Loc) (i : Nat) : (l.shift i).allocId = l.allocId := by
  simp [Loc.shift]

@[simp] theorem offset_shift (l : Loc) (i : Nat) : (l.shift i).offset = l.offset + i := by
  simp [Loc.shift]

@[simp] theorem shift_zero (l : Loc) : l.shift 0 = l := by
  simp [Loc.shift]

theorem shift_shift (l : Loc) (i j : Nat) :
    (l.shift i).shift j = l.shift (i + j) := by
  simp [Loc.shift, Nat.add_assoc]

end Loc

namespace RawPtr

@[simp] theorem loc_shift (q : RawPtr T M) (i : Nat) : (q.shift i).loc = q.loc.shift i := by
  simp [RawPtr.shift]

end RawPtr

namespace Heap

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
theorem empty_union (h : Heap) : ∅ ∪ h = h := by
  apply Heap.ext_impl
  exact Finmap.empty_union

@[simp]
theorem union_empty (h : Heap) : h ∪ ∅ = h := by
  apply Heap.ext_impl
  exact Finmap.union_empty

instance instPartialCommMonoid : PartialCommMonoid Heap where
  Compatible := Heap.Compatible
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
    address ∈ singleton q value ↔ address = q.loc := by
  show address ∈ (Finmap.singleton q.loc (Slot.live ⟨α, value⟩) : HeapImpl) ↔ _
  exact Finmap.mem_singleton _ _ _

theorem mem_endMarker {l address : Loc} {freeable : Bool} :
    address ∈ endMarker l freeable ↔ address = l := by
  show address ∈ (Finmap.singleton l (Slot.endMarker freeable) : HeapImpl) ↔ _
  exact Finmap.mem_singleton _ _ _

private theorem lookup_singleton {α : Type} (q : RawPtr α M) (value : α) :
    (singleton q value).lookup q.loc = some ⟨α, value⟩ := by
  simp [singleton, Heap.lookup, Slot.cell?]

/-- The cell does not depend on the pointer's mutability. -/
theorem singleton_eq_of_loc {α : Type} {q : RawPtr α M} {r : RawPtr α M'}
    (hAddr : q.loc = r.loc) (value : α) : singleton q value = singleton r value := by
  unfold singleton
  rw [hAddr]

@[simp]
theorem not_isValid_empty {α : Type} (q : RawPtr α M) :
    ¬ IsValid (∅ : Heap) q := by
  change ¬ match (Finmap.lookup q.loc (∅ : HeapImpl)).bind Slot.cell? with
    | none => False
    | some ⟨β, _⟩ => β = α
  simp

@[simp] theorem array_nil {α : Type} (l : Loc) :
    array l ([] : List α) = ∅ := by
  rw [array]
  rfl

@[simp] theorem array_cons {α : Type} (l : Loc) (value : α) (rest : List α) :
    array l (value :: rest) = singleton (⟨l⟩ : MutRawPtr α) value ∪ array (l.shift 1) rest := by
  rw [array]

@[simp] theorem array_singleton {α : Type} (l : Loc) (value : α) :
    array l [value] = singleton (⟨l⟩ : MutRawPtr α) value := by
  rw [array_cons, array_nil, Heap.union_empty]

theorem mem_array {α : Type} {l : Loc} {values : List α} {address : Loc} :
    address ∈ array l values ↔
      ∃ i, i < values.length ∧ address = l.shift i := by
  induction values generalizing l with
  | nil =>
      simp only [array_nil, List.length_nil, Nat.not_lt_zero, false_and,
        exists_false, iff_false]
      intro hMem
      exact (Finmap.notMem_empty (a := address)) hMem
  | cons value rest ih =>
      have hShift : ∀ i : Nat, (l.shift 1).shift i = l.shift (i + 1) := by
        intro i; rw [Loc.shift_shift, Nat.add_comm]
      rw [array_cons, Heap.mem_union, mem_singleton, ih]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, by simp, rfl⟩
        · exact ⟨i + 1, by simpa using hi, by rw [hShift]⟩
      · rintro ⟨i, hi, rfl⟩
        cases i with
        | zero => exact Or.inl rfl
        | succ j => exact Or.inr ⟨j, by simpa using hi, by rw [hShift]⟩

private theorem mem_freedRange {l address : Loc} {n : Nat} :
    address ∈ freedRange l n ↔ ∃ i, i < n ∧ address = l.shift i := by
  induction n generalizing l with
  | zero =>
      simp only [Nat.not_lt_zero, false_and, exists_false, iff_false]
      intro hMem
      exact (Finmap.notMem_empty (a := address)) hMem
  | succ n ih =>
      have hShift : ∀ i : Nat, (l.shift 1).shift i = l.shift (i + 1) := by
        intro i; rw [Loc.shift_shift, Nat.add_comm]
      have hSingle : address ∈ (⟨Finmap.singleton l Slot.freed⟩ : Heap) ↔ address = l :=
        Finmap.mem_singleton _ _ _
      show address ∈ (⟨Finmap.singleton l Slot.freed⟩ : Heap) ∪ freedRange (l.shift 1) n ↔ _
      rw [Heap.mem_union, hSingle, ih]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, by omega, rfl⟩
        · exact ⟨i + 1, by omega, by rw [hShift]⟩
      · rintro ⟨i, hi, rfl⟩
        cases i with
        | zero => exact Or.inl rfl
        | succ j => exact Or.inr ⟨j, by omega, by rw [hShift]⟩

private theorem lookup_freedRange {l : Loc} {n i : Nat} (hi : i < n) :
    (freedRange l n).impl.lookup (l.shift i) = some .freed := by
  induction n generalizing l i with
  | zero => omega
  | succ n ih =>
      show Finmap.lookup (l.shift i)
        ((Finmap.singleton l Slot.freed : HeapImpl) ∪ (freedRange (l.shift 1) n).impl) = _
      cases i with
      | zero =>
          show Finmap.lookup l ((Finmap.singleton l Slot.freed : HeapImpl) ∪ _) = _
          rw [Finmap.lookup_union_left ((Finmap.mem_singleton _ _ _).mpr rfl)]
          exact Finmap.lookup_singleton_eq
      | succ j =>
          have hNotMem : l.shift (j + 1) ∉ (Finmap.singleton l Slot.freed : HeapImpl) := by
            rw [Finmap.mem_singleton]
            intro hEq
            have hOffset := congrArg Loc.offset hEq
            simp only [Loc.offset_shift] at hOffset
            omega
          rw [Finmap.lookup_union_right hNotMem,
            show l.shift (j + 1) = (l.shift 1).shift j by rw [Loc.shift_shift, Nat.add_comm]]
          exact ih (by omega)

theorem array_append {α : Type} (l : Loc) (xs ys : List α) :
    array l (xs ++ ys) =
      array l xs ∪ array (l.shift xs.length) ys := by
  induction xs generalizing l with
  | nil => simp
  | cons value rest ih =>
      have hShift : (l.shift 1).shift rest.length = l.shift (rest.length + 1) := by
        rw [Loc.shift_shift, Nat.add_comm]
      rw [List.cons_append, array_cons, array_cons, ih, List.length_cons,
        hShift, Heap.union_assoc']

theorem compatible_array_append {α : Type} (l : Loc) (xs ys : List α) :
    PartialCommMonoid.Compatible (array l xs)
      (array (l.shift xs.length) ys) := by
  intro address hLeft hRight
  obtain ⟨i, hi, hL⟩ := mem_array.mp hLeft
  obtain ⟨j, -, hR⟩ := mem_array.mp hRight
  rw [Loc.shift_shift] at hR
  have hOffset : l.offset + i = l.offset + (xs.length + j) :=
    (congrArg Loc.offset hL).symm.trans (congrArg Loc.offset hR)
  omega

theorem notMem_freshAllocId {h : Heap} {address : Loc}
    (hBase : address.allocId = freshAllocId h) : address ∉ h := by
  intro hMem
  have hMemKeys : address ∈ h.keys := Finmap.mem_keys.mpr hMem
  have hImage : freshAllocId h ∈ h.keys.image Loc.allocId :=
    Finset.mem_image.mpr ⟨_, hMemKeys, hBase⟩
  have hLe : freshAllocId h ≤ (h.keys.image Loc.allocId).sup id :=
    Finset.le_sup (f := fun a : AllocId => a) hImage
  have hSucc : (h.keys.image Loc.allocId).sup id + 1 ≤
      (h.keys.image Loc.allocId).sup id := hLe
  exact Nat.not_succ_le_self _ hSucc

@[simp] theorem freshLoc_allocId (h : Heap) : (freshLoc h).allocId = freshAllocId h := by
  rw [freshLoc]

@[simp] theorem freshLoc_offset (h : Heap) : (freshLoc h).offset = 0 := by
  rw [freshLoc]

/-- A fresh allocation sits next to the heap it was allocated in. -/
theorem alloc_eq {α : Type} (h : Heap) (values : List α) (freeable : Bool) :
    alloc h values freeable = allocation (freshLoc h) values freeable ∪ h := by
  rw [alloc]

/-- An allocation is its cells followed by its end marker. -/
theorem allocation_eq {α : Type} (l : Loc) (values : List α) (freeable : Bool) :
    allocation l values freeable = array l values ∪ endMarker (l.shift values.length) freeable := by
  rw [allocation]

theorem compatible_freshLoc {α : Type} (h : Heap) (values : List α) (freeable : Bool) :
    PartialCommMonoid.Compatible (allocation (freshLoc h) values freeable) h := by
  intro address hFresh hMem
  apply notMem_freshAllocId (h := h) _ hMem
  rcases Heap.mem_union.mp hFresh with hRange | hEnd
  · obtain ⟨i, -, rfl⟩ := mem_array.mp hRange
    rfl
  · rw [mem_endMarker.mp hEnd]
    rfl

theorem compatible_array_endMarker {α : Type} (l : Loc) (values : List α) (freeable : Bool) :
    PartialCommMonoid.Compatible (array l values) (endMarker (l.shift values.length) freeable) := by
  intro address hRange hEnd
  obtain ⟨i, hi, rfl⟩ := mem_array.mp hRange
  have hOffset := congrArg Loc.offset (mem_endMarker.mp hEnd)
  simp only [Loc.offset_shift] at hOffset
  omega

theorem subheap_iff {h h' : Heap} :
    Heap.Subheap h h' ↔ ∃ rest, PartialCommMonoid.Compatible h rest ∧ h' = h ∪ rest :=
  Iff.rfl

namespace Subheap

@[refl]
theorem refl (h : Heap) : Heap.Subheap h h :=
  ⟨∅,
    PartialCommMonoid.compatible_comm
      (PartialCommMonoid.compatible_empty_left h),
    (PartialCommMonoid.union_empty h).symm⟩

theorem trans {h₁ h₂ h₃ : Heap} (hSub₁₂ : Heap.Subheap h₁ h₂)
    (hSub₂₃ : Heap.Subheap h₂ h₃) : Heap.Subheap h₁ h₃ := by
  obtain ⟨rest₁, hCompatible₁, rfl⟩ := hSub₁₂
  obtain ⟨rest₂, hCompatible₂, rfl⟩ := hSub₂₃
  have ⟨_, hCompatible⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ rest₁ rest₂).mp
      ⟨hCompatible₁, hCompatible₂⟩
  exact ⟨rest₁ ∪ rest₂, hCompatible,
    PartialCommMonoid.union_assoc hCompatible₁ hCompatible₂⟩

theorem of_empty (h : Heap) : Heap.Subheap ∅ h :=
  ⟨h, PartialCommMonoid.compatible_empty_left h,
    (PartialCommMonoid.empty_union h).symm⟩

theorem union_left {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Subheap h₁ (h₁ ∪ h₂) :=
  ⟨h₂, hCompatible, rfl⟩

theorem union_right {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Subheap h₂ (h₁ ∪ h₂) :=
  ⟨h₁, PartialCommMonoid.compatible_comm hCompatible,
    PartialCommMonoid.union_comm_of_compatible hCompatible⟩

theorem split {h₁ h₂ h' : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hSub : Heap.Subheap (h₁ ∪ h₂) h') :
    ∃ h₂', PartialCommMonoid.Compatible h₁ h₂' ∧
      h' = h₁ ∪ h₂' ∧ Heap.Subheap h₂ h₂' := by
  obtain ⟨rest, hCompatibleRest, rfl⟩ := hSub
  have ⟨hCompatible₂, hCompatible₁⟩ :=
    (PartialCommMonoid.compatible_assoc h₁ h₂ rest).mp
      ⟨hCompatible, hCompatibleRest⟩
  exact ⟨h₂ ∪ rest, hCompatible₁,
    PartialCommMonoid.union_assoc hCompatible hCompatibleRest,
    ⟨rest, hCompatible₂, rfl⟩⟩

theorem compatible {h h' frame : Heap} (hSub : Heap.Subheap h h')
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

theorem union_mono_left {h h' frame : Heap} (hSub : Heap.Subheap h h')
    (hCompatible : PartialCommMonoid.Compatible h' frame) :
    Heap.Subheap (h ∪ frame) (h' ∪ frame) := by
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
    (hSub₁ : Heap.Subheap A h₁) (hSub₂ : Heap.Subheap B h₂)
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) :
    Heap.Subheap (A ∪ B) (h₁ ∪ h₂) := by
  have hAh₂ : PartialCommMonoid.Compatible A h₂ :=
    hSub₁.compatible hCompatible
  have hAB : PartialCommMonoid.Compatible A B :=
    PartialCommMonoid.compatible_comm
      (hSub₂.compatible
        (PartialCommMonoid.compatible_comm hAh₂))
  have hStep₁ : Heap.Subheap (B ∪ A) (h₂ ∪ A) :=
    Heap.Subheap.union_mono_left hSub₂ (PartialCommMonoid.compatible_comm hAh₂)
  have hStep₂ : Heap.Subheap (A ∪ B) (A ∪ h₂) := by
    rw [PartialCommMonoid.union_comm_of_compatible hAB,
      PartialCommMonoid.union_comm_of_compatible hAh₂]
    exact hStep₁
  exact hStep₂.trans (Heap.Subheap.union_mono_left hSub₁ hCompatible)

end Subheap

theorem mem_of_isLive {h : Heap} {l : Loc} (hLive : IsLive h l) : l ∈ h := by
  obtain ⟨cell, hLookup⟩ := Option.isSome_iff_exists.mp hLive
  exact Heap.mem_of_lookup_eq_some hLookup

theorem isLive_of_isValid {α : Type} {h : Heap} {q : RawPtr α M}
    (hValid : IsValid h q) : IsLive h q.loc := by
  unfold IsValid at hValid
  unfold IsLive
  split at hValid
  · contradiction
  · rename_i cell hLookup
    simp [hLookup]

theorem mem_of_isValid {α : Type} {h : Heap} {q : RawPtr α M}
    (hValid : IsValid h q) : q.loc ∈ h :=
  mem_of_isLive (isLive_of_isValid hValid)

theorem not_compatible_of_isValid {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hValid₁ : IsValid h₁ q) (hValid₂ : IsValid h₂ q) :
    ¬ PartialCommMonoid.Compatible h₁ h₂ :=
  fun hCompatible => hCompatible q.loc (mem_of_isValid hValid₁) (mem_of_isValid hValid₂)

theorem isValid_union_left {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hValid : IsValid h₁ q) : IsValid (h₁ ∪ h₂) q := by
  have hMem : q.loc ∈ h₁ := mem_of_isValid hValid
  unfold IsValid at hValid ⊢
  rw [Heap.lookup_union_left hMem]
  exact hValid

theorem isLive_union_left {h₁ h₂ : Heap} {l : Loc}
    (hLive : IsLive h₁ l) : IsLive (h₁ ∪ h₂) l := by
  have hMem : l ∈ h₁ := mem_of_isLive hLive
  unfold IsLive at hLive ⊢
  rw [Heap.lookup_union_left hMem]
  exact hLive

theorem read_union_left {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hValid : IsValid h₁ q) :
    (h₁ ∪ h₂).read q (isValid_union_left hValid) =
      h₁.read q hValid := by
  have hMem : q.loc ∈ h₁ := mem_of_isValid hValid
  unfold Heap.read
  split
  · rename_i hLookup
    have hValidUnion := isValid_union_left (h₂ := h₂) hValid
    simp [IsValid, hLookup] at hValidUnion
  · rename_i β value hLookup
    split
    · rename_i hLookup₁
      simp [IsValid, hLookup₁] at hValid
    · rename_i β₁ value₁ hLookup₁
      have hCells :
          (⟨β, value⟩ : HeapCell) = ⟨β₁, value₁⟩ := by
        apply Option.some.inj
        exact hLookup.symm.trans
          ((Heap.lookup_union_left hMem).trans hLookup₁)
      cases hCells
      rfl

theorem write_union_left {α : Type} {h₁ h₂ : Heap}
    (q : RawPtr α M) (value : α) (hValid : IsValid h₁ q) :
    (h₁ ∪ h₂).write q value (isValid_union_left hValid) =
      h₁.write q value hValid ∪ h₂ := by
  exact Heap.insert_union

private theorem compatible_insert_left {l : Loc} {cell : Slot}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hMem : l ∈ h₁) :
    PartialCommMonoid.Compatible (h₁.insert l cell) h₂ := by
  intro address hMem₁ hMem₂
  rcases Heap.mem_insert.mp hMem₁ with rfl | hMem₁
  · exact hCompatible _ hMem hMem₂
  · exact hCompatible address hMem₁ hMem₂

theorem compatible_write_left {α : Type} {q : RawPtr α M} {value : α}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hValid : IsValid h₁ q) :
    PartialCommMonoid.Compatible
      (h₁.write q value hValid) h₂ :=
  compatible_insert_left hCompatible (mem_of_isValid hValid)

theorem isFreeableEnd_union_left {h₁ h₂ : Heap} {l : Loc} (hEnd : IsFreeableEnd h₁ l) :
    IsFreeableEnd (h₁ ∪ h₂) l := by
  show Finmap.lookup l (h₁.impl ∪ h₂.impl) = _
  rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hEnd)]
  exact hEnd

/-- A freeable end marker holds no value. -/
theorem not_isLive_of_isFreeableEnd {h : Heap} {l : Loc} (hEnd : IsFreeableEnd h l) :
    ¬ IsLive h l := by
  unfold IsFreeableEnd at hEnd
  simp [IsLive, Heap.lookup, hEnd, Slot.cell?]

theorem canDealloc_iff {h : Heap} {l : Loc} {n : Nat} :
    CanDealloc h l n ↔
      l.offset = 0 ∧ (∀ i < n, IsLive h (l.shift i)) ∧ IsFreeableEnd h (l.shift n) := by
  rw [CanDealloc]

theorem canDealloc_union_left {h₁ h₂ : Heap} {l : Loc} {n : Nat} (hDealloc : CanDealloc h₁ l n) :
    CanDealloc (h₁ ∪ h₂) l n :=
  ⟨hDealloc.1, fun i hi => isLive_union_left (hDealloc.2.1 i hi),
    isFreeableEnd_union_left hDealloc.2.2⟩

/-- The slots that `dealloc` kills are already in the heap. -/
private theorem mem_of_canDealloc {h : Heap} {l : Loc} {n i : Nat} (hDealloc : CanDealloc h l n)
    (hi : i < n + 1) : l.shift i ∈ h := by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact mem_of_isLive (hDealloc.2.1 i hi)
  · exact Finmap.mem_of_lookup_eq_some hDealloc.2.2

theorem compatible_dealloc_left {h₁ h₂ : Heap} {l : Loc} {n : Nat}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hDealloc : CanDealloc h₁ l n) :
    PartialCommMonoid.Compatible (h₁.dealloc l n hDealloc) h₂ := by
  intro address hMem hMem₂
  change address ∈ freedRange l (n + 1) ∪ h₁ at hMem
  rcases Heap.mem_union.mp hMem with hFreed | hMem₁
  · obtain ⟨i, hi, rfl⟩ := mem_freedRange.mp hFreed
    exact hCompatible _ (mem_of_canDealloc hDealloc hi) hMem₂
  · exact hCompatible _ hMem₁ hMem₂

theorem dealloc_union_left {h₁ h₂ : Heap} {l : Loc} {n : Nat} (hDealloc : CanDealloc h₁ l n) :
    (h₁ ∪ h₂).dealloc l n (canDealloc_union_left hDealloc) = h₁.dealloc l n hDealloc ∪ h₂ :=
  (Heap.union_assoc' _ _ _).symm

/-- Deallocated slots stay in the heap, so their allocation id is never handed out again. -/
theorem mem_dealloc {h : Heap} {l : Loc} {n i : Nat} (hDealloc : CanDealloc h l n) (hi : i ≤ n) :
    l.shift i ∈ h.dealloc l n hDealloc :=
  Heap.mem_union.mpr (Or.inl (mem_freedRange.mpr ⟨i, by omega, rfl⟩))

private theorem lookup_dealloc {h : Heap} {l : Loc} {n i : Nat} (hDealloc : CanDealloc h l n)
    (hi : i ≤ n) : (h.dealloc l n hDealloc).impl.lookup (l.shift i) = some .freed := by
  show Finmap.lookup (l.shift i) ((freedRange l (n + 1)).impl ∪ h.impl) = _
  rw [Finmap.lookup_union_left (mem_freedRange.mpr ⟨i, by omega, rfl⟩)]
  exact lookup_freedRange (by omega)

/-- A deallocated slot cannot be read or written. -/
theorem not_isLive_dealloc {h : Heap} {l : Loc} {n i : Nat}
    (hDealloc : CanDealloc h l n) (hi : i ≤ n) :
    ¬ IsLive (h.dealloc l n hDealloc) (l.shift i) := by
  simp [IsLive, Heap.lookup, lookup_dealloc hDealloc hi, Slot.cell?]

/-- After `dealloc`, the allocation end is freed, so the allocation cannot be deallocated again. -/
theorem not_isFreeableEnd_dealloc {h : Heap} {l : Loc} {n : Nat} (hDealloc : CanDealloc h l n) :
    ¬ IsFreeableEnd (h.dealloc l n hDealloc) (l.shift n) := by
  simp [IsFreeableEnd, lookup_dealloc hDealloc (Nat.le_refl n)]

/-- Allocation leaves the slots already in the heap untouched. -/
theorem isLive_alloc_of_mem {β : Type} {h : Heap} {values : List β} {freeable : Bool}
    {l : Loc} (hMem : l ∈ h) : IsLive (alloc h values freeable) l ↔ IsLive h l := by
  have hNotMem : l ∉ allocation (freshLoc h) values freeable :=
    fun hFresh => compatible_freshLoc h values freeable l hFresh hMem
  unfold IsLive
  rw [show (alloc h values freeable).lookup l = h.lookup l from
    congrArg (Option.bind · Slot.cell?) (Finmap.lookup_union_right hNotMem)]

/-- The end marker of an allocation is in the heap, so even an empty allocation reserves its id. -/
theorem mem_alloc_end {α : Type} {freeable : Bool} (h : Heap) (values : List α) :
    (freshLoc h).shift values.length ∈ alloc h values freeable :=
  Heap.mem_union.mpr (Or.inl (Heap.mem_union.mpr (Or.inr (mem_endMarker.mpr rfl))))

private theorem lookup_alloc_end {α : Type} (h : Heap) (values : List α) (freeable : Bool) :
    (alloc h values freeable).impl.lookup ((freshLoc h).shift values.length) =
      some (.endMarker freeable) := by
  have hNotRange :
      (freshLoc h).shift values.length ∉ (array (freshLoc h) values).impl := by
    intro hRange
    obtain ⟨i, hi, hEq⟩ := mem_array.mp hRange
    have hOffset := congrArg Loc.offset hEq
    simp only [Loc.offset_shift] at hOffset
    omega
  have hEnd : (freshLoc h).shift values.length ∈
      (endMarker ((freshLoc h).shift values.length) freeable).impl :=
    mem_endMarker.mpr rfl
  show Finmap.lookup _ (((array (freshLoc h) values).impl ∪
    (endMarker ((freshLoc h).shift values.length) freeable).impl) ∪ h.impl) = _
  rw [Finmap.lookup_union_left (Finmap.mem_union.mpr (Or.inr hEnd)),
    Finmap.lookup_union_right hNotRange]
  simp [endMarker]

/-- The end marker of a fresh allocation holds no value. -/
theorem not_isLive_alloc_end {β : Type} {freeable : Bool} (h : Heap) (values : List β) :
    ¬ IsLive (alloc h values freeable) ((freshLoc h).shift values.length) := by
  simp [IsLive, Heap.lookup, lookup_alloc_end, Slot.cell?]

/-- The end marker of a fresh allocation is freeable exactly when the allocation is. -/
theorem isFreeableEnd_alloc_end_iff {α : Type} (h : Heap) (values : List α) (freeable : Bool) :
    IsFreeableEnd (alloc h values freeable) ((freshLoc h).shift values.length) ↔
      freeable = true := by
  simp [IsFreeableEnd, lookup_alloc_end]

theorem compatible_singleton {α : Type} {q : RawPtr α M} {r : RawPtr α M'} {value₁ value₂ : α}
    (hNe : q.loc ≠ r.loc) :
    PartialCommMonoid.Compatible
      (singleton q value₁) (singleton r value₂) := by
  intro address hMem₁ hMem₂
  exact hNe ((mem_singleton.mp hMem₁).symm.trans (mem_singleton.mp hMem₂))

theorem isValid_singleton {α : Type} (q : RawPtr α M) (value : α) :
    IsValid (singleton q value) q := by
  simp [IsValid, singleton, Heap.lookup, Slot.cell?]

theorem read_singleton {α : Type} (q : RawPtr α M) (value : α)
    (hValid : IsValid (singleton q value) q) :
    (singleton q value).read q hValid = value := by
  unfold Heap.read
  split
  · rename_i hLookup
    rw [lookup_singleton] at hLookup
    contradiction
  · rename_i β stored hLookup
    rw [lookup_singleton] at hLookup
    cases hLookup
    rfl

theorem write_singleton {α : Type} (q : RawPtr α M)
    (oldValue newValue : α)
    (hValid : IsValid (singleton q oldValue) q) :
    (singleton q oldValue).write q newValue hValid =
      singleton q newValue := by
  apply Heap.ext_impl
  simp [Heap.write, singleton, Heap.insert]

theorem Subheap.isValid {α : Type} {A h : Heap} {q : RawPtr α M} (hSub : Heap.Subheap A h)
    (hValid : IsValid A q) : IsValid h q := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact isValid_union_left hValid

theorem Subheap.isLive {A h : Heap} {l : Loc} (hSub : Heap.Subheap A h)
    (hLive : IsLive A l) : IsLive h l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact isLive_union_left hLive

theorem Subheap.isFreeableEnd {l : Loc} {h : Heap} (hSub : Heap.Subheap (endMarker l true) h) :
    IsFreeableEnd h l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  have hMem : l ∈ endMarker l true := mem_endMarker.mpr rfl
  show Finmap.lookup l ((endMarker l true).impl ∪ rest.impl) = _
  rw [Finmap.lookup_union_left hMem]
  simp [endMarker]

/-- The empty heap has no freeable allocation. -/
@[simp] theorem not_isFreeableEnd_empty (l : Loc) : ¬ IsFreeableEnd (∅ : Heap) l := by
  change ¬ Finmap.lookup l (∅ : HeapImpl) = some (Slot.endMarker true)
  simp

theorem isLive_array {α : Type} {l : Loc} {values : List α} {i : Nat}
    (hIndex : i < values.length) : IsLive (array l values) (l.shift i) := by
  induction values generalizing l i with
  | nil => simp at hIndex
  | cons value rest ih =>
    rw [array_cons]
    cases i with
    | zero => exact isLive_union_left (isLive_of_isValid (isValid_singleton _ value))
    | succ j =>
      have hCompatible : PartialCommMonoid.Compatible (singleton (⟨l⟩ : MutRawPtr α) value)
          (array (l.shift 1) rest) := by
        have hAppend := compatible_array_append l [value] rest
        rwa [array_singleton] at hAppend
      rw [PartialCommMonoid.union_comm_of_compatible hCompatible,
        show l.shift (j + 1) = (l.shift 1).shift j by rw [Loc.shift_shift, Nat.add_comm]]
      exact isLive_union_left (ih (by simpa using hIndex))

/-- The values of a fresh allocation are live. -/
theorem isLive_alloc {α : Type} {h : Heap} {values : List α} {freeable : Bool} {i : Nat}
    (hIndex : i < values.length) :
    IsLive (alloc h values freeable) ((freshLoc h).shift i) :=
  Subheap.isLive ((Subheap.union_left (compatible_array_endMarker _ _ _)).trans
    (Subheap.union_left (compatible_freshLoc _ _ _))) (isLive_array hIndex)

theorem read_of_subheap {α : Type} {q : RawPtr α M} {value : α} {h : Heap}
    (hSub : Heap.Subheap (singleton q value) h)
    (hValid : IsValid h q) : h.read q hValid = value := by
  obtain ⟨rest, hCompatible, rfl⟩ := hSub
  have hValidSingleton := isValid_singleton q value
  rw [show hValid = isValid_union_left hValidSingleton from
      Subsingleton.elim _ _,
    read_union_left hValidSingleton, read_singleton]

theorem isFreed_union_left {h₁ h₂ : Heap} {l : Loc} (hFreed : IsFreed h₁ l) :
    IsFreed (h₁ ∪ h₂) l := by
  show Finmap.lookup l (h₁.impl ∪ h₂.impl) = _
  rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hFreed)]
  exact hFreed

theorem mem_freedSlot {l address : Loc} : address ∈ freedSlot l ↔ address = l := by
  show address ∈ (Finmap.singleton l Slot.freed : HeapImpl) ↔ _
  exact Finmap.mem_singleton _ _ _

theorem isFreed_freedSlot (l : Loc) : IsFreed (freedSlot l) l := by
  simp [IsFreed, freedSlot]

theorem Subheap.isFreed {l : Loc} {h : Heap} (hSub : Heap.Subheap (freedSlot l) h) :
    IsFreed h l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact isFreed_union_left (isFreed_freedSlot l)

theorem free_union_left {α : Type} {h₁ h₂ : Heap} (q : RawPtr α M) (hValid : IsValid h₁ q) :
    (h₁ ∪ h₂).free q (isValid_union_left hValid) = h₁.free q hValid ∪ h₂ :=
  Heap.insert_union

theorem compatible_free_left {α : Type} {q : RawPtr α M} {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hValid : IsValid h₁ q) :
    PartialCommMonoid.Compatible (h₁.free q hValid) h₂ :=
  compatible_insert_left hCompatible (mem_of_isValid hValid)

theorem free_singleton {α : Type} (q : RawPtr α M) (value : α)
    (hValid : IsValid (singleton q value) q) :
    (singleton q value).free q hValid = freedSlot q.loc := by
  apply Heap.ext_impl
  simp [Heap.free, singleton, freedSlot, Heap.insert]

theorem revive_union_left {α : Type} {h₁ h₂ : Heap} (q : RawPtr α M) (value : α)
    (hFreed : IsFreed h₁ q.loc) :
    (h₁ ∪ h₂).revive q value (isFreed_union_left hFreed) = h₁.revive q value hFreed ∪ h₂ :=
  Heap.insert_union

theorem compatible_revive_left {α : Type} {q : RawPtr α M} {value : α} {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hFreed : IsFreed h₁ q.loc) :
    PartialCommMonoid.Compatible (h₁.revive q value hFreed) h₂ :=
  compatible_insert_left hCompatible (Finmap.mem_of_lookup_eq_some hFreed)

theorem revive_freedSlot {α : Type} (q : RawPtr α M) (value : α)
    (hFreed : IsFreed (freedSlot q.loc) q.loc) :
    (freedSlot q.loc).revive q value hFreed = singleton q value := by
  apply Heap.ext_impl
  simp [Heap.revive, singleton, freedSlot, Heap.insert]

end Heap

end Aeneas.Std