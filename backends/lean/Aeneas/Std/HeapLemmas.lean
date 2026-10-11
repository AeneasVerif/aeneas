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

@[simp] theorem loc_shiftCells (q : RawPtr T M) (i : Nat) : (q.shiftCells i).loc = q.loc.shift i := by
  simp [RawPtr.shiftCells]

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

theorem mem_cell {α : Type} {q : RawPtr α M} {value : Option α} {address : Loc} :
    address ∈ cell q value ↔ address = q.loc := by
  show address ∈ (Finmap.singleton q.loc (Slot.live ⟨α, value⟩) : HeapImpl) ↔ _
  exact Finmap.mem_singleton _ _ _

theorem mem_endMarker {l address : Loc} {kind : AllocKind} :
    address ∈ endMarker l kind ↔ address = l := by
  show address ∈ (Finmap.singleton l (Slot.endMarker kind) : HeapImpl) ↔ _
  exact Finmap.mem_singleton _ _ _

private theorem lookup_cell {α : Type} (q : RawPtr α M) (value : Option α) :
    (cell q value).lookup q.loc = some ⟨α, value⟩ := by
  simp [cell, Heap.lookup, Slot.cell?]

/-- The cell does not depend on the pointer's mutability. -/
theorem cell_eq_of_loc {α : Type} {q : RawPtr α M} {r : RawPtr α M'}
    (hAddr : q.loc = r.loc) (value : Option α) : cell q value = cell r value := by
  unfold cell
  rw [hAddr]

@[simp]
theorem not_isValid_empty {α : Type} (q : RawPtr α M) :
    ¬ IsValid (∅ : Heap) q := by
  change ¬ match (Finmap.lookup q.loc (∅ : HeapImpl)).bind Slot.cell? with
    | none => False
    | some ⟨β, _⟩ => β = α
  simp

@[simp] theorem array_nil {α : Type} (l : Loc) :
    array l ([] : List (Option α)) = ∅ := by
  rw [array]
  rfl

@[simp] theorem array_cons {α : Type} (l : Loc) (value : Option α) (rest : List (Option α)) :
    array l (value :: rest) = cell (⟨l⟩ : MutRawPtr α) value ∪ array (l.shift 1) rest := by
  rw [array]

@[simp] theorem array_singleton {α : Type} (l : Loc) (value : Option α) :
    array l [value] = cell (⟨l⟩ : MutRawPtr α) value := by
  rw [array_cons, array_nil, Heap.union_empty]

theorem mem_array {α : Type} {l : Loc} {values : List (Option α)} {address : Loc} :
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
      rw [array_cons, Heap.mem_union, mem_cell, ih]
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

theorem array_append {α : Type} (l : Loc) (xs ys : List (Option α)) :
    array l (xs ++ ys) =
      array l xs ∪ array (l.shift xs.length) ys := by
  induction xs generalizing l with
  | nil => simp
  | cons value rest ih =>
      have hShift : (l.shift 1).shift rest.length = l.shift (rest.length + 1) := by
        rw [Loc.shift_shift, Nat.add_comm]
      rw [List.cons_append, array_cons, array_cons, ih, List.length_cons,
        hShift, Heap.union_assoc']

theorem compatible_array_append {α : Type} (l : Loc) (xs ys : List (Option α)) :
    PartialCommMonoid.Compatible (array l xs)
      (array (l.shift xs.length) ys) := by
  intro address hLeft hRight
  obtain ⟨i, hi, hL⟩ := mem_array.mp hLeft
  obtain ⟨j, -, hR⟩ := mem_array.mp hRight
  rw [Loc.shift_shift] at hR
  have hOffset : l.offset + i = l.offset + (xs.length + j) :=
    (congrArg Loc.offset hL).symm.trans (congrArg Loc.offset hR)
  omega

/-- A fresh allocation is aligned (see `freshAllocId`). -/
theorem dvd_freshAllocId (h : Heap) (align : Nat) : max align 1 ∣ freshAllocId h align :=
  Dvd.intro _ rfl

/-- The null allocation `0` is never allocated. -/
theorem freshAllocId_ne_zero (h : Heap) (align : Nat) : freshAllocId h align ≠ 0 := by
  unfold freshAllocId
  exact Nat.mul_ne_zero (by omega) (by omega)

theorem notMem_freshAllocId {h : Heap} {align : Nat} {address : Loc}
    (hBase : address.allocId = freshAllocId h align) : address ∉ h := by
  intro hMem
  have hMemKeys : address ∈ h.keys := Finmap.mem_keys.mpr hMem
  have hImage : freshAllocId h align ∈ h.keys.image Loc.allocId :=
    Finset.mem_image.mpr ⟨_, hMemKeys, hBase⟩
  have hLe : freshAllocId h align ≤ (h.keys.image Loc.allocId).sup id :=
    Finset.le_sup (f := fun a : AllocId => a) hImage
  have hGe : 2 * ((h.keys.image Loc.allocId).sup id + 1) + 1 ≤ freshAllocId h align :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hContra := Nat.le_trans hGe hLe
  generalize (h.keys.image Loc.allocId).sup id = s at hContra
  omega

@[simp] theorem freshLoc_allocId (h : Heap) (align : Nat) :
    (freshLoc h align).allocId = freshAllocId h align := by
  rw [freshLoc]

@[simp] theorem freshLoc_offset (h : Heap) (align : Nat) : (freshLoc h align).offset = 0 := by
  rw [freshLoc]

/-- A fresh allocation sits next to the heap it was allocated in. -/
theorem alloc_eq {α : Type} (h : Heap) (align : Nat) (values : List (Option α))
    (kind : AllocKind) :
    h.alloc align values kind =
      (⟨freshLoc h align⟩, allocation (freshLoc h align) values kind ∪ h) := by
  rw [alloc]

/-- An allocation is its cells followed by its end marker. -/
theorem allocation_eq {α : Type} (l : Loc) (values : List (Option α)) (kind : AllocKind) :
    allocation l values kind = array l values ∪ endMarker (l.shift values.length) kind := by
  rw [allocation]

theorem compatible_freshLoc {α : Type} (h : Heap) (align : Nat) (values : List (Option α))
    (kind : AllocKind) :
    PartialCommMonoid.Compatible (allocation (freshLoc h align) values kind) h := by
  intro address hFresh hMem
  apply notMem_freshAllocId (h := h) (align := align) _ hMem
  rcases Heap.mem_union.mp hFresh with hRange | hEnd
  · obtain ⟨i, -, rfl⟩ := mem_array.mp hRange
    rfl
  · rw [mem_endMarker.mp hEnd]
    rfl

theorem compatible_array_endMarker {α : Type} (l : Loc) (values : List (Option α)) (kind : AllocKind) :
    PartialCommMonoid.Compatible (array l values) (endMarker (l.shift values.length) kind) := by
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

/-- A cell has a single type. -/
theorem isValid_unique {α β : Type} {h : Heap} {q : RawPtr α M} {r : RawPtr β M'}
    (hq : IsValid h q) (hr : IsValid h r) (hLoc : q.loc = r.loc) : α = β := by
  unfold IsValid at hq hr
  rw [hLoc] at hq
  split at hq <;> simp_all

/-- Validity depends only on the location and the type of the cell. -/
theorem isValid_of_loc {α : Type} {h : Heap} {q : RawPtr α M} {r : RawPtr α M'}
    (hValid : IsValid h q) (hLoc : q.loc = r.loc) : IsValid h r := by
  unfold IsValid at hValid ⊢
  rwa [← hLoc]

theorem isLive_union_left {h₁ h₂ : Heap} {l : Loc}
    (hLive : IsLive h₁ l) : IsLive (h₁ ∪ h₂) l := by
  have hMem : l ∈ h₁ := mem_of_isLive hLive
  unfold IsLive at hLive ⊢
  rw [Heap.lookup_union_left hMem]
  exact hLive

/-- Framing: `read` on a bigger heap reads the same value and leaves the frame alone. -/
theorem read_union_left {α : Type} {h₁ h₂ : Heap} {q : RawPtr α M}
    (hValid : IsValid h₁ q) :
    (h₁ ∪ h₂).read q (isValid_union_left hValid) = Prod.map id (· ∪ h₂) (h₁.read q hValid) := by
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
    (q : RawPtr α M) (value : Option α) (hValid : IsValid h₁ q) :
    (h₁ ∪ h₂).write q value (isValid_union_left hValid) =
      Prod.map id (· ∪ h₂) (h₁.write q value hValid) :=
  congrArg (Prod.mk ()) Heap.insert_union

private theorem compatible_insert_left {l : Loc} {cell : Slot}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hMem : l ∈ h₁) :
    PartialCommMonoid.Compatible (h₁.insert l cell) h₂ := by
  intro address hMem₁ hMem₂
  rcases Heap.mem_insert.mp hMem₁ with rfl | hMem₁
  · exact hCompatible _ hMem hMem₂
  · exact hCompatible address hMem₁ hMem₂

theorem compatible_write_left {α : Type} {q : RawPtr α M} {value : Option α}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hValid : IsValid h₁ q) :
    PartialCommMonoid.Compatible (h₁.write q value hValid).2 h₂ :=
  compatible_insert_left hCompatible (mem_of_isValid hValid)

theorem isEndMarker_union_left {h₁ h₂ : Heap} {l : Loc} {kind : AllocKind}
    (hEnd : IsEndMarker h₁ l kind) : IsEndMarker (h₁ ∪ h₂) l kind := by
  show Finmap.lookup l (h₁.impl ∪ h₂.impl) = _
  rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hEnd)]
  exact hEnd

/-- An end marker holds no value. -/
theorem not_isLive_of_isEndMarker {h : Heap} {l : Loc} {kind : AllocKind}
    (hEnd : IsEndMarker h l kind) : ¬ IsLive h l := by
  unfold IsEndMarker at hEnd
  simp [IsLive, Heap.lookup, hEnd, Slot.cell?]

theorem canDealloc_iff {h : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind} :
    CanDealloc h q n kind ↔
      q.loc.offset = 0 ∧ (∀ i < n, IsLive h (q.loc.shift i)) ∧
        IsEndMarker h (q.loc.shift n) kind := by
  rw [CanDealloc]

theorem canDealloc_union_left {h₁ h₂ : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h₁ q n kind) : CanDealloc (h₁ ∪ h₂) q n kind :=
  ⟨hDealloc.1, fun i hi => isLive_union_left (hDealloc.2.1 i hi),
    isEndMarker_union_left hDealloc.2.2⟩

/-- The slots that `dealloc` kills are already in the heap. -/
private theorem mem_of_canDealloc {h : Heap} {q : RawPtr α M} {n i : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h q n kind)
    (hi : i < n + 1) : q.loc.shift i ∈ h := by
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact mem_of_isLive (hDealloc.2.1 i hi)
  · exact Finmap.mem_of_lookup_eq_some hDealloc.2.2

theorem compatible_dealloc_left {h₁ h₂ : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hDealloc : CanDealloc h₁ q n kind) :
    PartialCommMonoid.Compatible (h₁.dealloc q n kind hDealloc).2 h₂ := by
  intro address hMem hMem₂
  change address ∈ freedRange q.loc (n + 1) ∪ h₁ at hMem
  rcases Heap.mem_union.mp hMem with hFreed | hMem₁
  · obtain ⟨i, hi, rfl⟩ := mem_freedRange.mp hFreed
    exact hCompatible _ (mem_of_canDealloc hDealloc hi) hMem₂
  · exact hCompatible _ hMem₁ hMem₂

theorem dealloc_union_left {h₁ h₂ : Heap} {q : RawPtr α M} {n : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h₁ q n kind) :
    (h₁ ∪ h₂).dealloc q n kind (canDealloc_union_left hDealloc) =
      Prod.map id (· ∪ h₂) (h₁.dealloc q n kind hDealloc) :=
  congrArg (Prod.mk ()) (Heap.union_assoc' _ _ _).symm

/-- Deallocated slots stay in the heap, so their allocation id is never handed out again. -/
theorem mem_dealloc {h : Heap} {q : RawPtr α M} {n i : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h q n kind) (hi : i ≤ n) :
    q.loc.shift i ∈ (h.dealloc q n kind hDealloc).2 :=
  Heap.mem_union.mpr (Or.inl (mem_freedRange.mpr ⟨i, by omega, rfl⟩))

private theorem lookup_dealloc {h : Heap} {q : RawPtr α M} {n i : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h q n kind) (hi : i ≤ n) :
    (h.dealloc q n kind hDealloc).2.impl.lookup (q.loc.shift i) = some .freed := by
  show Finmap.lookup (q.loc.shift i) ((freedRange q.loc (n + 1)).impl ∪ h.impl) = _
  rw [Finmap.lookup_union_left (mem_freedRange.mpr ⟨i, by omega, rfl⟩)]
  exact lookup_freedRange (by omega)

/-- A deallocated slot cannot be read or written. -/
theorem not_isLive_dealloc {h : Heap} {q : RawPtr α M} {n i : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h q n kind) (hi : i ≤ n) :
    ¬ IsLive (h.dealloc q n kind hDealloc).2 (q.loc.shift i) := by
  simp [IsLive, Heap.lookup, lookup_dealloc hDealloc hi, Slot.cell?]

/-- After `dealloc`, the allocation end is freed, so the allocation cannot be deallocated again. -/
theorem not_isEndMarker_dealloc {h : Heap} {q : RawPtr α M} {n : Nat} {kind kind' : AllocKind}
    (hDealloc : CanDealloc h q n kind) :
    ¬ IsEndMarker (h.dealloc q n kind hDealloc).2 (q.loc.shift n) kind' := by
  simp [IsEndMarker, lookup_dealloc hDealloc (Nat.le_refl n)]

theorem isFreed_dealloc {h : Heap} {q : RawPtr α M} {n i : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h q n kind) (hi : i ≤ n) :
    IsFreed (h.dealloc q n kind hDealloc).2 (q.loc.shift i) :=
  lookup_dealloc hDealloc hi

/-- A deallocated slot cannot be borrowed back to life. -/
theorem not_isBorrowed_dealloc {h : Heap} {q : RawPtr α M} {n i : Nat} {kind : AllocKind}
    (hDealloc : CanDealloc h q n kind) (hi : i ≤ n) :
    ¬ IsBorrowed (h.dealloc q n kind hDealloc).2 (q.loc.shift i) := by
  simp [IsBorrowed, lookup_dealloc hDealloc hi]

/-- Allocation leaves the slots already in the heap untouched. -/
theorem isLive_alloc_of_mem {β : Type} {h : Heap} {align : Nat} {values : List (Option β)}
    {kind : AllocKind} {l : Loc} (hMem : l ∈ h) :
    IsLive (h.alloc align values kind).2 l ↔ IsLive h l := by
  have hNotMem : l ∉ allocation (freshLoc h align) values kind :=
    fun hFresh => compatible_freshLoc h align values kind l hFresh hMem
  unfold IsLive
  rw [show (h.alloc align values kind).2.lookup l = h.lookup l from
    congrArg (Option.bind · Slot.cell?) (Finmap.lookup_union_right hNotMem)]

/-- The end marker of an allocation is in the heap, so even an empty allocation reserves its id. -/
theorem mem_alloc_end {α : Type} {kind : AllocKind} (h : Heap) (align : Nat)
    (values : List (Option α)) :
    (freshLoc h align).shift values.length ∈ (h.alloc align values kind).2 :=
  Heap.mem_union.mpr (Or.inl (Heap.mem_union.mpr (Or.inr (mem_endMarker.mpr rfl))))

private theorem lookup_alloc_end {α : Type} (h : Heap) (align : Nat) (values : List (Option α))
    (kind : AllocKind) :
    (h.alloc align values kind).2.impl.lookup ((freshLoc h align).shift values.length) =
      some (.endMarker kind) := by
  have hNotRange :
      (freshLoc h align).shift values.length ∉ (array (freshLoc h align) values).impl := by
    intro hRange
    obtain ⟨i, hi, hEq⟩ := mem_array.mp hRange
    have hOffset := congrArg Loc.offset hEq
    simp only [Loc.offset_shift] at hOffset
    omega
  have hEnd : (freshLoc h align).shift values.length ∈
      (endMarker ((freshLoc h align).shift values.length) kind).impl :=
    mem_endMarker.mpr rfl
  show Finmap.lookup _ (((array (freshLoc h align) values).impl ∪
    (endMarker ((freshLoc h align).shift values.length) kind).impl) ∪ h.impl) = _
  rw [Finmap.lookup_union_left (Finmap.mem_union.mpr (Or.inr hEnd)),
    Finmap.lookup_union_right hNotRange]
  simp [endMarker]

/-- The end marker of a fresh allocation holds no value. -/
theorem not_isLive_alloc_end {β : Type} {kind : AllocKind} (h : Heap) (align : Nat)
    (values : List (Option β)) :
    ¬ IsLive (h.alloc align values kind).2 ((freshLoc h align).shift values.length) := by
  simp [IsLive, Heap.lookup, lookup_alloc_end, Slot.cell?]

/-- The end marker of a fresh allocation records the kind of the allocation. -/
theorem isEndMarker_alloc_end_iff {α : Type} (h : Heap) (align : Nat) (values : List (Option α))
    (kind kind' : AllocKind) :
    IsEndMarker (h.alloc align values kind).2 ((freshLoc h align).shift values.length) kind' ↔
      kind = kind' := by
  simp [IsEndMarker, lookup_alloc_end]

theorem compatible_cell {α : Type} {q : RawPtr α M} {r : RawPtr α M'} {value₁ value₂ : Option α}
    (hNe : q.loc ≠ r.loc) :
    PartialCommMonoid.Compatible
      (cell q value₁) (cell r value₂) := by
  intro address hMem₁ hMem₂
  exact hNe ((mem_cell.mp hMem₁).symm.trans (mem_cell.mp hMem₂))

theorem isValid_cell {α : Type} (q : RawPtr α M) (value : Option α) :
    IsValid (cell q value) q := by
  simp [IsValid, cell, Heap.lookup, Slot.cell?]

theorem read_cell {α : Type} (q : RawPtr α M) (value : Option α)
    (hValid : IsValid (cell q value) q) :
    (cell q value).read q hValid = (value, cell q value) := by
  unfold Heap.read
  split
  · rename_i hLookup
    rw [lookup_cell] at hLookup
    contradiction
  · rename_i β stored hLookup
    rw [lookup_cell] at hLookup
    cases hLookup
    rfl

theorem write_cell {α : Type} (q : RawPtr α M)
    (oldValue newValue : Option α)
    (hValid : IsValid (cell q oldValue) q) :
    (cell q oldValue).write q newValue hValid =
      ((), cell q newValue) :=
  congrArg (Prod.mk ()) (Heap.ext_impl (by simp [cell, Heap.insert]))

theorem Subheap.isValid {α : Type} {A h : Heap} {q : RawPtr α M} (hSub : Heap.Subheap A h)
    (hValid : IsValid A q) : IsValid h q := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact isValid_union_left hValid

theorem Subheap.isLive {A h : Heap} {l : Loc} (hSub : Heap.Subheap A h)
    (hLive : IsLive A l) : IsLive h l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact isLive_union_left hLive

theorem Subheap.isEndMarker {l : Loc} {h : Heap} {kind : AllocKind}
    (hSub : Heap.Subheap (endMarker l kind) h) : IsEndMarker h l kind := by
  obtain ⟨rest, -, rfl⟩ := hSub
  have hMem : l ∈ endMarker l kind := mem_endMarker.mpr rfl
  show Finmap.lookup l ((endMarker l kind).impl ∪ rest.impl) = _
  rw [Finmap.lookup_union_left hMem]
  simp [endMarker]

/-- The empty heap has no allocation. -/
@[simp] theorem not_isEndMarker_empty (l : Loc) (kind : AllocKind) :
    ¬ IsEndMarker (∅ : Heap) l kind := by
  change ¬ Finmap.lookup l (∅ : HeapImpl) = some (Slot.endMarker kind)
  simp

theorem isLive_array {α : Type} {l : Loc} {values : List (Option α)} {i : Nat}
    (hIndex : i < values.length) : IsLive (array l values) (l.shift i) := by
  induction values generalizing l i with
  | nil => simp at hIndex
  | cons value rest ih =>
    rw [array_cons]
    cases i with
    | zero => exact isLive_union_left (isLive_of_isValid (isValid_cell _ value))
    | succ j =>
      have hCompatible : PartialCommMonoid.Compatible (cell (⟨l⟩ : MutRawPtr α) value)
          (array (l.shift 1) rest) := by
        have hAppend := compatible_array_append l [value] rest
        rwa [array_singleton] at hAppend
      rw [PartialCommMonoid.union_comm_of_compatible hCompatible,
        show l.shift (j + 1) = (l.shift 1).shift j by rw [Loc.shift_shift, Nat.add_comm]]
      exact isLive_union_left (ih (by simpa using hIndex))

/-- The cells of an array have the type of its values. -/
theorem isValid_array {α : Type} {l : Loc} {values : List (Option α)} {i : Nat}
    (hIndex : i < values.length) : IsValid (array l values) (⟨l.shift i⟩ : MutRawPtr α) := by
  induction values generalizing l i with
  | nil => simp at hIndex
  | cons value rest ih =>
    rw [array_cons]
    cases i with
    | zero => exact isValid_union_left (by simpa using isValid_cell (⟨l⟩ : MutRawPtr α) value)
    | succ j =>
      have hCompatible : PartialCommMonoid.Compatible (cell (⟨l⟩ : MutRawPtr α) value)
          (array (l.shift 1) rest) := by
        have hAppend := compatible_array_append l [value] rest
        rwa [array_singleton] at hAppend
      rw [PartialCommMonoid.union_comm_of_compatible hCompatible,
        show l.shift (j + 1) = (l.shift 1).shift j by rw [Loc.shift_shift, Nat.add_comm]]
      exact isValid_union_left (ih (by simpa using hIndex))

/-- The values of a fresh allocation are live. -/
theorem isLive_alloc {α : Type} {h : Heap} {align : Nat} {values : List (Option α)}
    {kind : AllocKind} {i : Nat} (hIndex : i < values.length) :
    IsLive (h.alloc align values kind).2 ((freshLoc h align).shift i) :=
  Subheap.isLive ((Subheap.union_left (compatible_array_endMarker _ _ _)).trans
    (Subheap.union_left (compatible_freshLoc _ _ _ _))) (isLive_array hIndex)

theorem read_of_subheap {α : Type} {q : RawPtr α M} {value : Option α} {h : Heap}
    (hSub : Heap.Subheap (cell q value) h)
    (hValid : IsValid h q) : (h.read q hValid).1 = value := by
  obtain ⟨rest, hCompatible, rfl⟩ := hSub
  have hValidCell := isValid_cell q value
  rw [show hValid = isValid_union_left hValidCell from
      Subsingleton.elim _ _,
    read_union_left hValidCell, read_cell]
  rfl

/-- `read` leaves the heap alone. -/
theorem read_snd {α : Type} {h : Heap} {q : RawPtr α M} (hValid : IsValid h q) :
    (h.read q hValid).2 = h := by
  unfold Heap.read
  split
  · rename_i hLookup
    simp [IsValid, hLookup] at hValid
  · rfl

/-- `borrow` returns the value that `read` returns. -/
theorem borrow_fst {α : Type} {h : Heap} {q : RawPtr α M} (hValid : IsValid h q) :
    (h.borrow q hValid).1 = (h.read q hValid).1 := by
  unfold Heap.borrow; rfl

theorem isBorrowed_union_left {h₁ h₂ : Heap} {l : Loc} (hBorrowed : IsBorrowed h₁ l) :
    IsBorrowed (h₁ ∪ h₂) l := by
  show Finmap.lookup l (h₁.impl ∪ h₂.impl) = _
  rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hBorrowed)]
  exact hBorrowed

theorem mem_borrowedSlot {l address : Loc} : address ∈ borrowedSlot l ↔ address = l := by
  show address ∈ (Finmap.singleton l Slot.borrowed : HeapImpl) ↔ _
  exact Finmap.mem_singleton _ _ _

theorem isBorrowed_borrowedSlot (l : Loc) : IsBorrowed (borrowedSlot l) l := by
  simp [IsBorrowed, borrowedSlot]

theorem Subheap.isBorrowed {l : Loc} {h : Heap} (hSub : Heap.Subheap (borrowedSlot l) h) :
    IsBorrowed h l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact isBorrowed_union_left (isBorrowed_borrowedSlot l)

/-- A borrowed slot holds no value. -/
theorem not_isLive_of_isBorrowed {h : Heap} {l : Loc} (hBorrowed : IsBorrowed h l) :
    ¬ IsLive h l := by
  unfold IsBorrowed at hBorrowed
  simp [IsLive, Heap.lookup, hBorrowed, Slot.cell?]

theorem borrow_union_left {α : Type} {h₁ h₂ : Heap} (q : RawPtr α M) (hValid : IsValid h₁ q) :
    (h₁ ∪ h₂).borrow q (isValid_union_left hValid) =
      Prod.map id (· ∪ h₂) (h₁.borrow q hValid) :=
  Prod.ext (congrArg Prod.fst (read_union_left (h₂ := h₂) hValid) :) Heap.insert_union

theorem compatible_borrow_left {α : Type} {q : RawPtr α M} {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hValid : IsValid h₁ q) :
    PartialCommMonoid.Compatible (h₁.borrow q hValid).2 h₂ :=
  compatible_insert_left hCompatible (mem_of_isValid hValid)

/-- A borrowed slot holds no value: no access goes through it until `endBorrow`. -/
theorem not_isLive_borrow {α : Type} {h : Heap} {q : RawPtr α M} (hValid : IsValid h q) :
    ¬ IsLive (h.borrow q hValid).2 q.loc := by
  simp [IsLive, Heap.lookup, Heap.borrow, Heap.insert, Slot.cell?]

theorem borrow_cell {α : Type} (q : RawPtr α M) (value : Option α)
    (hValid : IsValid (cell q value) q) :
    (cell q value).borrow q hValid = (value, borrowedSlot q.loc) :=
  Prod.ext (congrArg Prod.fst (read_cell q value hValid) :)
    (Heap.ext_impl (by simp [Heap.borrow, cell, borrowedSlot, Heap.insert]))

theorem endBorrow_union_left {α : Type} {h₁ h₂ : Heap} (q : RawPtr α M) (value : Option α)
    (hBorrowed : IsBorrowed h₁ q.loc) :
    (h₁ ∪ h₂).endBorrow q value (isBorrowed_union_left hBorrowed) =
      Prod.map id (· ∪ h₂) (h₁.endBorrow q value hBorrowed) :=
  congrArg (Prod.mk ()) Heap.insert_union

theorem compatible_endBorrow_left {α : Type} {q : RawPtr α M} {value : Option α} {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂) (hBorrowed : IsBorrowed h₁ q.loc) :
    PartialCommMonoid.Compatible (h₁.endBorrow q value hBorrowed).2 h₂ :=
  compatible_insert_left hCompatible (Finmap.mem_of_lookup_eq_some hBorrowed)

theorem endBorrow_borrowedSlot {α : Type} (q : RawPtr α M) (value : Option α)
    (hBorrowed : IsBorrowed (borrowedSlot q.loc) q.loc) :
    (borrowedSlot q.loc).endBorrow q value hBorrowed = ((), cell q value) :=
  congrArg (Prod.mk ()) (Heap.ext_impl (by simp [cell, borrowedSlot, Heap.insert]))

theorem Subheap.isFreed {l : Loc} {h : Heap} (hSub : Heap.Subheap (freedSlot l) h) :
    IsFreed h l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  show Finmap.lookup l ((Finmap.singleton l Slot.freed : HeapImpl) ∪ rest.impl) = _
  rw [Finmap.lookup_union_left ((Finmap.mem_singleton _ _ _).mpr rfl)]
  simp

/-- A freed slot is owned as a whole: the rest of the heap is everything else. -/
theorem subheap_freedSlot {h : Heap} {l : Loc} (hFreed : IsFreed h l) :
    Heap.Subheap (freedSlot l) h := by
  refine ⟨⟨h.impl.erase l⟩, fun x hx => ?_, Heap.ext_impl (Finmap.ext_lookup fun x => ?_)⟩
  · rw [show x = l from (Finmap.mem_singleton _ _ _).mp hx]
    exact Finmap.notMem_erase_self
  · show _ = Finmap.lookup x ((Finmap.singleton l Slot.freed : HeapImpl) ∪ h.impl.erase l)
    by_cases hx : x = l
    · subst hx
      rw [Finmap.lookup_union_left ((Finmap.mem_singleton _ _ _).mpr rfl), Finmap.lookup_singleton_eq]
      exact hFreed
    · rw [Finmap.lookup_union_right (by simpa [Finmap.mem_singleton] using hx),
        Finmap.lookup_erase_ne hx]

/-- A freed slot holds no value. -/
theorem not_isLive_of_isFreed {h : Heap} {l : Loc} (hFreed : IsFreed h l) : ¬ IsLive h l := by
  unfold IsFreed at hFreed
  simp [IsLive, Heap.lookup, hFreed, Slot.cell?]

/-- A slot is the end marker of one kind of allocation only. -/
theorem isEndMarker_unique {h : Heap} {l : Loc} {kind kind' : AllocKind}
    (hEnd : IsEndMarker h l kind) (hEnd' : IsEndMarker h l kind') : kind = kind' := by
  unfold IsEndMarker at hEnd hEnd'
  rw [hEnd] at hEnd'
  simpa using hEnd'

end Heap

end Aeneas.Std