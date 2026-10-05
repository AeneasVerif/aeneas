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

@[simp] theorem add_fst (l : Loc) (i : Nat) : (l.add i).1 = l.1 := rfl

@[simp] theorem add_snd (l : Loc) (i : Nat) : (l.add i).2 = l.2 + i := rfl

@[simp] theorem add_zero (l : Loc) : l.add 0 = l := rfl

theorem add_add (l : Loc) (i j : Nat) :
    (l.add i).add j = l.add (i + j) := by
  simp [Loc.add, Nat.add_assoc]

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
  Finmap.lookup_union_left hMem

private theorem mem_insert {address insertedAddress : Loc}
    {cell : HeapCell} {h : Heap} :
    address ∈ h.insert insertedAddress cell ↔
      address = insertedAddress ∨ address ∈ h :=
  Finmap.mem_insert

private theorem mem_erase {address erasedAddress : Loc} {h : Heap} :
    address ∈ h.erase erasedAddress ↔
      address ≠ erasedAddress ∧ address ∈ h :=
  Finmap.mem_erase

private theorem insert_union {address : Loc}
    {cell : HeapCell} {h₁ h₂ : Heap} :
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

theorem mem_singleton {α : Type} {l : Loc} {value : α} {address : Loc} :
    address ∈ singleton l value ↔ address = l := by
  show address ∈ (Finmap.singleton l (⟨α, value⟩ : HeapCell) : HeapImpl) ↔ _
  exact Finmap.mem_singleton _ _ _

@[simp]
theorem not_contains_empty {α : Type} (l : Loc) :
    ¬ contains (∅ : Heap) α l := by
  change ¬ match Finmap.lookup l (∅ : HeapImpl) with
    | none => False
    | some ⟨β, _⟩ => β = α
  simp

@[simp] theorem rangeHeap_nil {α : Type} (l : Loc) :
    rangeHeap l ([] : List α) = empty := rfl

@[simp] theorem rangeHeap_cons {α : Type} (l : Loc) (value : α)
    (rest : List α) :
    rangeHeap l (value :: rest) = singleton l value ∪ rangeHeap (l.add 1) rest :=
  rfl

@[simp] theorem rangeHeap_singleton {α : Type} (l : Loc) (value : α) :
    rangeHeap l [value] = singleton l value := by
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
      rw [rangeHeap_cons, Heap.mem_union, mem_singleton, ih]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, by simp, rfl⟩
        · exact ⟨i + 1, by simpa using hi, by rw [hShift]⟩
      · rintro ⟨i, hi, rfl⟩
        cases i with
        | zero => exact Or.inl rfl
        | succ j => exact Or.inr ⟨j, by simpa using hi, by rw [hShift]⟩

theorem rangeHeap_append {α : Type} (l : Loc) (xs ys : List α) :
    rangeHeap l (xs ++ ys) =
      rangeHeap l xs ∪ rangeHeap (l.add xs.length) ys := by
  induction xs generalizing l with
  | nil => simp
  | cons value rest ih =>
      have hShift : (l.add 1).add rest.length = l.add (rest.length + 1) := by
        rw [Loc.add_add, Nat.add_comm]
      rw [List.cons_append, rangeHeap_cons, rangeHeap_cons, ih, List.length_cons,
        hShift, Heap.union_assoc']

theorem compatible_rangeHeap_append {α : Type} (l : Loc) (xs ys : List α) :
    PartialCommMonoid.Compatible (rangeHeap l xs)
      (rangeHeap (l.add xs.length) ys) := by
  intro address hLeft hRight
  obtain ⟨i, hi, hL⟩ := mem_rangeHeap.mp hLeft
  obtain ⟨j, -, hR⟩ := mem_rangeHeap.mp hRight
  rw [Loc.add_add] at hR
  have hOffset : l.2 + i = l.2 + (xs.length + j) :=
    (congrArg Prod.snd hL).symm.trans (congrArg Prod.snd hR)
  omega

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

theorem compatible_freshLoc {α : Type} (h : Heap) (values : List α) :
    PartialCommMonoid.Compatible (rangeHeap (freshLoc h) values) h := by
  intro address hFresh hMem
  obtain ⟨i, -, rfl⟩ := mem_rangeHeap.mp hFresh
  exact not_mem_freshBase (h := h) rfl hMem

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

theorem mem_of_contains {α : Type} {h : Heap} {l : Loc}
    (hContains : contains h α l) : l ∈ h := by
  unfold contains at hContains
  split at hContains
  · contradiction
  · rename_i cell hLookup
    exact Finmap.mem_of_lookup_eq_some hLookup

theorem disjoint_contains_false {α : Type} {h₁ h₂ : Heap} {l : Loc}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains₁ : contains h₁ α l)
    (hContains₂ : contains h₂ α l) : False :=
  hCompatible l (mem_of_contains hContains₁)
    (mem_of_contains hContains₂)

theorem contains_union_left {α : Type} {h₁ h₂ : Heap} {l : Loc}
    (hContains : contains h₁ α l) : contains (h₁ ∪ h₂) α l := by
  have hMem : l ∈ h₁ := mem_of_contains hContains
  unfold contains at hContains ⊢
  rw [Heap.lookup_union_left hMem]
  exact hContains

theorem read_union_left {α : Type} {h₁ h₂ : Heap} {l : Loc}
    (hContains : contains h₁ α l) :
    Heap.read l (h₁ ∪ h₂) (contains_union_left hContains) =
      Heap.read l h₁ hContains := by
  have hMem : l ∈ h₁ := by
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
    (l : Loc) (value : α) (hContains : contains h₁ α l) :
    Heap.update l value (h₁ ∪ h₂) (contains_union_left hContains) =
      Heap.update l value h₁ hContains ∪ h₂ := by
  exact Heap.insert_union

theorem disjoint_update_left {α : Type} {l : Loc} {value : α}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ α l) :
    PartialCommMonoid.Compatible
      (Heap.update l value h₁ hContains) h₂ := by
  have hUnallocated : l ∉ h₂ := by
    intro hMem₂
    unfold contains at hContains
    split at hContains
    · contradiction
    · rename_i cell hLookup
      exact hCompatible l
        (Finmap.mem_of_lookup_eq_some hLookup) hMem₂
  intro address hMem₁ hMem₂
  change address ∈ h₁.insert l ⟨α, value⟩ at hMem₁
  rw [Heap.mem_insert] at hMem₁
  rcases hMem₁ with hEq | hMem₁
  · exact hUnallocated (hEq ▸ hMem₂)
  · exact hCompatible address hMem₁ hMem₂

theorem disjoint_free_left {α : Type} {l : Loc}
    {h₁ h₂ : Heap}
    (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ α l) :
    PartialCommMonoid.Compatible (Heap.free l h₁ hContains) h₂ := by
  intro address hMem₁ hMem₂
  change address ∈ h₁.erase l at hMem₁
  exact hCompatible address (Heap.mem_erase.mp hMem₁).right hMem₂

theorem free_union_left {α : Type} {h₁ h₂ : Heap}
    (l : Loc) (hCompatible : PartialCommMonoid.Compatible h₁ h₂)
    (hContains : contains h₁ α l) :
    Heap.free l (h₁ ∪ h₂) (contains_union_left hContains) =
      Heap.free l h₁ hContains ∪ h₂ := by
  have hMem : l ∈ h₁ := by
    unfold contains at hContains
    split at hContains
    · contradiction
    · rename_i cell hLookup
      exact Finmap.mem_of_lookup_eq_some hLookup
  have hNotMem : l ∉ h₂ :=
    fun hMem₂ => hCompatible l hMem hMem₂
  unfold Heap.free
  apply Heap.ext_impl
  apply Finmap.ext_lookup
  intro address
  change
    Finmap.lookup address (h₁.impl ∪ h₂.impl |>.erase l) =
      Finmap.lookup address (h₁.impl.erase l ∪ h₂.impl)
  by_cases hEq : address = l
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

theorem disjoint_singleton {α : Type} {l l' : Loc} {value₁ value₂ : α}
    (hNe : l ≠ l') :
    PartialCommMonoid.Compatible
      (singleton l value₁) (singleton l' value₂) := by
  intro address hMem₁ hMem₂
  change address ∈
    (Finmap.singleton l ⟨α, value₁⟩ : HeapImpl) at hMem₁
  change address ∈
    (Finmap.singleton l' ⟨α, value₂⟩ : HeapImpl) at hMem₂
  rw [Finmap.mem_singleton] at hMem₁
  rw [Finmap.mem_singleton] at hMem₂
  exact hNe (hMem₁.symm.trans hMem₂)

theorem contains_singleton {α : Type} (l : Loc) (value : α) :
    contains (singleton l value) α l := by
  simp [contains, singleton, Heap.lookup]

theorem read_singleton {α : Type} (l : Loc) (value : α)
    (hContains : contains (singleton l value) α l) :
    Heap.read l (singleton l value) hContains = value := by
  unfold Heap.read
  split
  · rename_i hLookup
    change
      Finmap.lookup l
          (Finmap.singleton l ⟨α, value⟩ : HeapImpl) =
        none at hLookup
    rw [Finmap.lookup_singleton_eq] at hLookup
    contradiction
  · rename_i β stored hLookup
    change
      Finmap.lookup l
          (Finmap.singleton l ⟨α, value⟩ : HeapImpl) =
        some (⟨β, stored⟩ : HeapCell) at hLookup
    rw [Finmap.lookup_singleton_eq] at hLookup
    cases hLookup
    rfl

theorem update_singleton {α : Type} (l : Loc)
    (oldValue newValue : α)
    (hContains : contains (singleton l oldValue) α l) :
    Heap.update l newValue (singleton l oldValue) hContains =
      singleton l newValue := by
  apply Heap.ext_impl
  simp [Heap.update, singleton, Heap.insert]

theorem free_singleton {α : Type} (l : Loc) (value : α)
    (hContains : contains (singleton l value) α l) :
    Heap.free l (singleton l value) hContains = empty := by
  unfold Heap.free
  apply Heap.ext_impl
  apply Finmap.ext_lookup
  intro address
  change
    Finmap.lookup address
        ((Finmap.singleton l ⟨α, value⟩ : HeapImpl).erase
          l) =
      Finmap.lookup address (∅ : HeapImpl)
  by_cases hEq : address = l
  · subst address
    simp
  · rw [Finmap.lookup_erase_ne hEq]
    simp only [Finmap.lookup_empty]
    apply Finmap.lookup_eq_none.mpr
    simpa [singleton, Finmap.mem_singleton] using hEq

theorem contains_of_sub {α : Type} {l : Loc} {value : α} {h : Heap}
    (hSub : Heap.Sub (singleton l value) h) : contains h α l := by
  obtain ⟨rest, -, rfl⟩ := hSub
  exact contains_union_left (contains_singleton l value)

theorem read_of_sub {α : Type} {l : Loc} {value : α} {h : Heap}
    (hSub : Heap.Sub (singleton l value) h)
    (hContains : contains h α l) : Heap.read l h hContains = value := by
  obtain ⟨rest, hCompatible, rfl⟩ := hSub
  have hContainsSingleton := contains_singleton l value
  rw [show hContains = contains_union_left hContainsSingleton from
      Subsingleton.elim _ _,
    read_union_left hContainsSingleton, read_singleton]

end Heap

end Aeneas.Std