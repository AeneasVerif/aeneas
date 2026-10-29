module

public import Aeneas.Std.Heap.Model
public import Aeneas.Tactic.Solver.Grind
import all Aeneas.Std.Heap.Model

/-! Laws of the concrete byte operations and allocation map. No representation
operations or their correctness properties are assumed. -/

@[expose] public section

namespace Aeneas.Std

universe u v

def CellsDisjoint {T : Type u} {U : Type v}
    (reprT : Repr T) (i : Nat) (reprU : Repr U) (j : Nat) : Prop :=
  (i + 1) * reprT.size ≤ j * reprU.size ∨
    (j + 1) * reprU.size ≤ i * reprT.size

namespace Repr

theorem align_pos (repr : Repr ty) : 0 < repr.align.val := by
  obtain ⟨k, hk⟩ := repr.align.property
  rw [hk]
  exact Nat.two_pow_pos k

theorem aligned_stride (repr : Repr ty) (i : Nat) :
    repr.align.val ∣ i * repr.size :=
  dvd_mul_of_dvd_right repr.aligned i

@[simp] theorem select_toList (repr : Repr ty) (bytes : Vector (Cell U8) r)
    (i : Nat) (hi : (i + 1) * repr.size ≤ r) :
    (repr.select bytes i hi).toList = (bytes.toList.drop (i * repr.size)).take repr.size := by
  simp [select, Nat.add_mul]

@[simp] theorem update_toList (repr : Repr ty) (bytes : Vector (Cell U8) r)
    (i : Nat) (hi : (i + 1) * repr.size ≤ r) (data : Vector (Cell U8) repr.size) :
    (repr.update bytes i hi data).toList =
      bytes.toList.take (i * repr.size) ++ data.toList ++
        bytes.toList.drop ((i + 1) * repr.size) := by
  simp [update]

theorem select_update (repr : Repr ty) (bytes : Vector (Cell U8) r)
    (i : Nat) (hi : (i + 1) * repr.size ≤ r) (data : Vector (Cell U8) repr.size) :
    repr.select (repr.update bytes i hi data) i hi = data := by
  apply Vector.toList_inj.mp
  have hs : i * repr.size ≤ r := by grind [Nat.add_mul]
  simp [List.drop_append, List.take_append, Nat.min_eq_left hs]

theorem update_outside (repr : Repr ty) (bytes : Vector (Cell U8) r)
    (i : Nat) (hi : (i + 1) * repr.size ≤ r) (data : Vector (Cell U8) repr.size)
    (j : Nat) (hj : j < i * repr.size ∨ (i + 1) * repr.size ≤ j) :
    (repr.update bytes i hi data).toList[j]? = bytes.toList[j]? := by
  have hs : i * repr.size ≤ r := by grind [Nat.add_mul]
  rw [update_toList]
  rcases hj with hj | hj
  · simp [List.getElem?_append, List.getElem?_take, Nat.min_eq_left hs, hj]
  · simp [List.getElem?_append, List.getElem?_take, Nat.min_eq_left hs,
      show ¬ j < i * repr.size by grind [Nat.add_mul],
      show ¬ j - i * repr.size < repr.size by grind [Nat.add_mul],
      List.getElem?_drop]
    congr 1
    grind [Nat.add_mul]

theorem readBytes_shared (data : Vector U8 n) (depth : Nat) :
    readBytes n (data.map (Cell.shared depth ∘ some)) = some data := by
  simp [readBytes, Vector.mapM_map, Function.comp_def, Cell.read, Vector.mapM_pure]

end Repr

namespace Heap

theorem inv_empty : empty.Inv := fun _ _ => rfl

@[simp] theorem allocations_storeRepr (s : Heap) (base other : BasePtr) (bytes : List (Cell U8)) :
    (s.storeRepr base bytes).allocations other =
      if other = base then (s.allocations base).map (fun b => { b with repr := bytes })
      else s.allocations other := by
  simp [storeRepr, update]

@[simp] theorem allocations_remove (s : Heap) (base other : BasePtr) :
    (s.remove base).allocations other = if other = base then none else s.allocations other := by
  simp [remove, update]

@[simp] theorem cells_storeRepr (s : Heap) (base other : BasePtr) (bytes : List (Cell U8)) :
    (s.storeRepr base bytes).cells other =
      if other = base then (s.cells base).map (fun _ => bytes) else s.cells other := by
  by_cases h : other = base
  · subst other
    simp [storeRepr, cells, update, Option.map_map, Function.comp_def]
  · simp [storeRepr, cells, update, h]

@[simp] theorem cells_remove (s : Heap) (base other : BasePtr) :
    (s.remove base).cells other = if other = base then none else s.cells other := by
  by_cases h : other = base
  · simp [remove, cells, update, h]
  · simp [remove, cells, update, h]

@[simp] theorem allocated_storeRepr (s : Heap) (base other : BasePtr) (bytes : List (Cell U8)) :
    (s.storeRepr base bytes).allocated other = s.allocated other := by
  by_cases h : other = base
  · subst other
    simp [storeRepr, allocated, update, Option.map_map, Function.comp_def]
  · simp [storeRepr, allocated, update, h]

@[simp] theorem alignment_storeRepr (s : Heap) (base other : BasePtr) (bytes : List (Cell U8)) :
    (s.storeRepr base bytes).alignment other = s.alignment other := by
  by_cases h : other = base
  · subst other
    simp [storeRepr, alignment, update, Option.map_map, Function.comp_def]
  · simp [storeRepr, alignment, update, h]

@[simp] theorem allocated_remove (s : Heap) (base other : BasePtr) :
    (s.remove base).allocated other = if other = base then false else s.allocated other := by
  by_cases h : other = base
  · simp [remove, allocated, update, h]
  · simp [remove, allocated, update, h]

@[simp] theorem alignment_remove (s : Heap) (base other : BasePtr) :
    (s.remove base).alignment other =
      if other = base then none else s.alignment other := by
  by_cases h : other = base
  · simp [remove, alignment, update, h]
  · simp [remove, alignment, update, h]

theorem Inv.base_lt {s : Heap} (h : s.Inv) {base : BasePtr} {block : Block}
    (hc : s.allocations base = some block) : base.val < s.next.val := by
  by_contra hn
  have hf := h base (Nat.le_of_not_gt hn)
  simp [hf] at hc

theorem Inv.storeRepr {s : Heap} (h : s.Inv) (base : BasePtr) (bytes : List (Cell U8)) :
    (s.storeRepr base bytes).Inv := by
  intro other ho
  change s.next.val ≤ other.val at ho
  have he := h other ho
  by_cases hb : other = base
  · subst other
    simp [storeRepr, update, he]
  · simpa [storeRepr, update, hb] using he

theorem Inv.remove {s : Heap} (h : s.Inv) (base : BasePtr) :
    (s.remove base).Inv := by
  intro other ho
  change s.next.val ≤ other.val at ho
  by_cases he : other = base
  · simp [remove, update, he]
  · simpa [remove, update, he] using h other ho

/-- Exact lifting rule for a successful, length-preserving byte transformation. -/
theorem modify.spec (repr : Repr ty) (p : RawPtr ty)
    (change : ∀ {r}, Vector (Cell U8) r → Option (Vector (Cell U8) r))
    (s₀ : Heap) (block : Block) (data : Vector (Cell U8) block.repr.length)
    (hl : s₀.allocations p.base = some block)
    (ha : repr.align.val ∣ block.alignment.val) (hc : change block.bytes = some data) :
    modify repr p change s₀ = some (s₀.storeRepr p.base data.toList) := by
  simp [modify, hl, ha, hc]

theorem modify.success {repr : Repr ty} {p : RawPtr ty}
    {change : ∀ {r}, Vector (Cell U8) r → Option (Vector (Cell U8) r)}
    {s₀ s₁ : Heap} (h : modify repr p change s₀ = some s₁) :
    ∃ (block : Block) (data : Vector (Cell U8) block.repr.length),
      s₀.allocations p.base = some block ∧ repr.align.val ∣ block.alignment.val ∧
      change block.bytes = some data ∧ s₁ = s₀.storeRepr p.base data.toList := by
  unfold modify at h
  split at h
  · rename_i block hl
    split at h
    · rename_i ha
      split at h
      · rename_i data hc
        exact ⟨block, data, hl, ha, hc, (Option.some.inj h).symm⟩
      · cases h
    · cases h
  · cases h

theorem modify.inv {repr : Repr ty} {p : RawPtr ty}
    {change : ∀ {r}, Vector (Cell U8) r → Option (Vector (Cell U8) r)}
    {s₀ s₁ : Heap} (hi : s₀.Inv) (h : modify repr p change s₀ = some s₁) : s₁.Inv := by
  obtain ⟨_, data, _, _, _, rfl⟩ := modify.success h
  exact hi.storeRepr p.base data.toList

end Heap
end Aeneas.Std
