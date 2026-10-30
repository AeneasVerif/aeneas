module

public import Aeneas.Std.Heap.Model
public import Aeneas.Tactic.Solver.Grind
import all Aeneas.Std.Heap.Model

/-! Laws of the concrete byte operations and allocation map. No representation
operations or their correctness properties are assumed. -/

@[expose] public section

namespace Aeneas.Std

universe u v

theorem vector_mapM_some {α : Type u} {β : Type v} (xs : Vector α n) (f : α → β) :
    xs.mapM (fun x => some (f x)) = some (xs.map f) := by
  simpa only [Option.pure_def] using Vector.mapM_pure (m := Option) (xs := xs) f

theorem list_mapM_result {α : Type u} {β : Type v} {f : α → Option β} {g : α → β}
    (hg : ∀ a b, f a = some b → b = g a) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys = xs.map g := by
  induction xs generalizing ys
  · simpa using (Option.some.inj h).symm
  · rename_i a xs ih
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tail, ht, h⟩ := Option.bind_eq_some_iff.mp h
    have he := Option.some.inj h
    subst ys
    simp [hg a b hb, ih ht]

theorem vector_mapM_toList {α : Type u} {β : Type v} {f : α → Option β}
    (xs : Vector α n) :
    (xs.mapM f).map Vector.toList = xs.toList.mapM f := by
  have ha := Vector.toArray_mapM (m := Option) (f := f) (xs := xs)
  simp only [Option.map_eq_map] at ha
  calc
    _ = ((xs.mapM f).map Vector.toArray).map Array.toList := by
      simp [Option.map_map, Function.comp_def, Vector.toList_toArray]
    _ = _ := by
      rw [ha, Array.mapM_eq_mapM_toList]
      simp [Option.map_map, Function.comp_def, Vector.toList_toArray]

theorem vector_mapM_result {α : Type u} {β : Type v} {f : α → Option β} {g : α → β}
    (hg : ∀ a b, f a = some b → b = g a) {xs : Vector α n} {ys : Vector β n}
    (h : xs.mapM f = some ys) : ys = xs.map g := by
  have hl := vector_mapM_toList (f := f) xs
  rw [h] at hl
  apply Vector.toList_inj.mp
  simpa [Vector.toList_map] using list_mapM_result hg hl.symm

theorem list_mapM_enabled {α : Type u} {β : Type v} {f : α → Option β}
    {xs : List α} {ys : List β} (h : xs.mapM f = some ys) :
    ∀ a ∈ xs, ∃ b, f a = some b := by
  induction xs generalizing ys
  · simp
  · rename_i a xs ih
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tail, ht, _⟩ := Option.bind_eq_some_iff.mp h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, hb⟩
    · exact ih ht x hx

theorem vector_mapM_enabled {α : Type u} {β : Type v} {f : α → Option β}
    {xs : Vector α n} {ys : Vector β n} (h : xs.mapM f = some ys)
    (i : Nat) (hi : i < n) : ∃ b, f xs[i] = some b := by
  have hl := vector_mapM_toList (f := f) xs
  rw [h] at hl
  have hi' : i < xs.toList.length := by simpa using hi
  obtain ⟨b, hb⟩ := list_mapM_enabled hl.symm xs.toList[i] (List.getElem_mem hi')
  exact ⟨b, (congrArg f (Vector.getElem_toList (xs := xs) hi')).symm.trans hb⟩

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
  Nat.dvd_mul_left_of_dvd repr.aligned i

@[simp] theorem select_toList (repr : Repr ty) (bytes : Vector (Cell U8) r)
    (i : Nat) (hi : (i + 1) * repr.size ≤ r) :
    (repr.select bytes i hi).toList = (bytes.toList.drop (i * repr.size)).take repr.size := by
  simp [select, Vector.toList_cast, Vector.toList_extract, Nat.add_mul]

theorem select_getElem? (repr : Repr ty) (bytes : Vector (Cell U8) r)
    (i : Nat) (hi : (i + 1) * repr.size ≤ r) (j : Nat) (hj : j < repr.size) :
    (repr.select bytes i hi)[j]? = bytes.toList[i * repr.size + j]? := by
  rw [← Vector.getElem?_toList, select_toList, List.getElem?_take_of_lt hj,
    List.getElem?_drop]

@[simp] theorem update_toList (repr : Repr ty) (bytes : Vector (Cell U8) r)
    (i : Nat) (hi : (i + 1) * repr.size ≤ r) (data : Vector (Cell U8) repr.size) :
    (repr.update bytes i hi data).toList =
      bytes.toList.take (i * repr.size) ++ data.toList ++
        bytes.toList.drop ((i + 1) * repr.size) := by
  simp [update, Vector.toList_cast, Vector.toList_extract]
  apply List.take_of_length_le
  simp

theorem select_update (repr : Repr ty) (bytes : Vector (Cell U8) r)
    (i : Nat) (hi : (i + 1) * repr.size ≤ r) (data : Vector (Cell U8) repr.size) :
    repr.select (repr.update bytes i hi data) i hi = data := by
  apply Vector.toList_inj.mp
  have hs : i * repr.size ≤ r := by grind [Nat.add_mul]
  simp [Nat.min_eq_left hs]

theorem update_outside (repr : Repr ty) (bytes : Vector (Cell U8) r)
    (i : Nat) (hi : (i + 1) * repr.size ≤ r) (data : Vector (Cell U8) repr.size)
    (j : Nat) (hj : j < i * repr.size ∨ (i + 1) * repr.size ≤ j) :
    (repr.update bytes i hi data).toList[j]? = bytes.toList[j]? := by
  have hs : i * repr.size ≤ r := by grind [Nat.add_mul]
  rw [update_toList]
  rcases hj with hj | hj
  · simp [List.getElem?_append, Nat.min_eq_left hs, hj]
  · simp [List.getElem?_append, Nat.min_eq_left hs,
      show ¬ j < i * repr.size by grind [Nat.add_mul],
      show ¬ j - i * repr.size < repr.size by grind [Nat.add_mul],
      List.getElem?_drop]
    apply congrArg (bytes[·]?)
    grind [Nat.add_mul]

theorem update_inside (repr : Repr ty) (bytes : Vector (Cell U8) r)
    (i : Nat) (hi : (i + 1) * repr.size ≤ r) (data : Vector (Cell U8) repr.size)
    (j : Nat) (hj : j < repr.size) :
    (repr.update bytes i hi data).toList[i * repr.size + j]? = some data[j] := by
  have hs : i * repr.size ≤ r := by grind [Nat.add_mul]
  rw [update_toList]
  simp [List.getElem?_append, Nat.min_eq_left hs,
    show ¬ i * repr.size + j < i * repr.size by grind, hj]

theorem select_update_disjoint {T : Type u} {U : Type v}
    (reprT : Repr T) (reprU : Repr U) (bytes : Vector (Cell U8) r)
    (i j : Nat) (hi : (i + 1) * reprT.size ≤ r) (hj : (j + 1) * reprU.size ≤ r)
    (data : Vector (Cell U8) reprT.size) (hd : CellsDisjoint reprT i reprU j) :
    reprU.select (reprT.update bytes i hi data) j hj = reprU.select bytes j hj := by
  apply Vector.toList_inj.mp
  apply List.ext_getElem?
  intro k
  simp only [select_toList]
  by_cases hk : k < reprU.size
  · have hout : j * reprU.size + k < i * reprT.size ∨
        (i + 1) * reprT.size ≤ j * reprU.size + k := by
      unfold CellsDisjoint at hd
      grind [Nat.add_mul]
    simpa [hk] using update_outside reprT bytes i hi data (j * reprU.size + k) hout
  · calc
      _ = none := List.getElem?_eq_none (by simp only [List.length_take]; grind)
      _ = _ := (List.getElem?_eq_none (by simp only [List.length_take]; grind)).symm

theorem read_update_disjoint {T : Type u} {U : Type v}
    (reprT : Repr T) (reprU : Repr U) (bytes : Vector (Cell U8) r)
    (i j : Nat) (hi : (i + 1) * reprT.size ≤ r)
    (data : Vector (Cell U8) reprT.size) (hd : CellsDisjoint reprT i reprU j) :
    reprU.read (reprT.update bytes i hi data) j = reprU.read bytes j := by
  by_cases hj : 0 < reprU.size ∧ (j + 1) * reprU.size ≤ r
  · simp [read, hj, select_update_disjoint reprT reprU bytes i j hi hj.2 data hd]
  · simp [read, hj]

theorem readBytes_shared (data : Vector U8 n) (depth : Nat) :
    readBytes n (data.map (Cell.shared depth ∘ some)) = some data := by
  simp only [readBytes, Vector.mapM_map, Function.comp_def, Cell.read]
  exact (Vector.mapM_pure (m := Option) id).trans (by simp)

theorem create_single (repr : Repr ty) (data : Vector U8 repr.size) (depth : Nat) :
    (repr.create #v[Cell.shared depth (some data)]).toList =
      (data.map (Cell.shared depth ∘ some)).toList := by
  simp [create, Vector.toList_map, Vector.toList_toArray]

theorem writeBytes_result {bytes : Vector (Cell U8) n} {data : Vector U8 n}
    {result : Vector (Cell U8) n} (h : writeBytes n bytes data = some result) :
    result = data.map (Cell.shared 0 ∘ some) := by
  have hh : result = (bytes.zip data).map (fun p => Cell.shared 0 (some p.2)) := by
    apply vector_mapM_result (f := fun p : Cell U8 × U8 => Cell.write p.1 p.2)
      (xs := bytes.zip data) ?_ h
    rintro ⟨cell, byte⟩ value hv
    cases cell
    · rename_i depth payload
      cases depth
      · exact (Option.some.inj hv).symm
      · cases hv
    · cases hv
  rw [hh]
  have he := Vector.map_snd_zip (as := bytes) data
  simpa only [Vector.map_map, Function.comp_def] using
    congrArg (Vector.map (Cell.shared 0 ∘ some)) he

theorem writeBytes_shared (old : Vector (Option U8) n) (data : Vector U8 n) :
    writeBytes n (old.map (Cell.shared 0)) data = some (data.map (Cell.shared 0 ∘ some)) := by
  simp only [writeBytes, Vector.zip_map_left, Vector.mapM_map, Function.comp_def,
    Prod.map, Cell.write]
  have hm := Vector.mapM_pure (m := Option) (xs := old.zip data)
    (fun p => Cell.shared 0 (some p.2))
  have he := congrArg (Vector.map (Cell.shared 0 ∘ some))
    (Vector.map_snd_zip (as := old) data)
  simp only [Vector.map_map, Function.comp_def] at he
  simpa only [Vector.map_map, Function.comp_def, id_eq, Option.pure_def] using
    hm.trans (congrArg some he)

theorem write_read {repr : Repr ty} {bytes result : Vector (Cell U8) r} {i : Nat}
    {value : ty} {data : Vector U8 repr.size} {decoded : repr.decode data = some value}
    (h : repr.write bytes i value data decoded = some result) :
    repr.read result i = some value := by
  unfold write at h
  split at h
  · rename_i hi
    split at h
    · rename_i cells hc
      have he := (Option.some.inj h).symm
      subst result
      rw [writeBytes_result hc]
      simp [read, hi, select_update, readBytes_shared, decoded]
    · cases h
  · cases h

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
  by_cases hn : base.val < s.next.val
  · exact hn
  · have hf := h base (Nat.le_of_not_gt hn)
    simp [hf] at hc

theorem Inv.storeRepr {s : Heap} (h : s.Inv) (base : BasePtr) (bytes : List (Cell U8)) :
    (s.storeRepr base bytes).Inv := by
  intro other ho
  change s.next.val ≤ other.val at ho
  have he := h other ho
  by_cases hb : other = base
  · subst other
    simp [he]
  · simpa [storeRepr, update, hb] using he

theorem Inv.remove {s : Heap} (h : s.Inv) (base : BasePtr) :
    (s.remove base).Inv := by
  intro other ho
  change s.next.val ≤ other.val at ho
  by_cases he : other = base
  · simp [he]
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

theorem readRange_single (repr : Repr ty) (p : RawPtr ty) (s : Heap) :
    readRange repr p 1 s = (read repr p s).map (fun value => [value]) := by
  cases hl : s.allocations p.base
  · simp [readRange, read, hl]
  · rename_i blk
    by_cases ha : repr.align.val ∣ blk.alignment.val
    · by_cases hb : 0 < repr.size ∧ (p.index.val + 1) * repr.size ≤ blk.repr.length
      · simp [readRange, read, hl, ha, hb, List.range_succ, Repr.read, Option.bind_assoc]
        apply congrArg (Option.bind _)
        funext data
        dsimp only [Function.comp_def]
        cases repr.decode data
        · rfl
        · rfl
      · simp [readRange, read, hl, ha, hb, Repr.read]
    · simp [readRange, read, hl, ha]

theorem borrowRange_single (repr : Repr ty) (p : RawPtr ty) (s : Heap) :
    borrowRange repr p 1 s = borrow repr p s := by
  cases hl : s.allocations p.base
  · simp [borrowRange, modifyRange, borrow, modify, hl]
  · rename_i blk
    by_cases hb : 0 < repr.size ∧ (p.index.val + 1) * repr.size ≤ blk.repr.length
    · simp [borrowRange, modifyRange, borrow, modify, hl, hb, List.range_succ]
    · simp [borrowRange, modifyRange, borrow, modify, hl, hb, Repr.borrow]

theorem shareRange_single (repr : Repr ty) (p : RawPtr ty) (s : Heap) :
    shareRange repr p 1 s = share repr p s := by
  cases hl : s.allocations p.base
  · simp [shareRange, modifyRange, share, modify, hl]
  · rename_i blk
    by_cases hb : 0 < repr.size ∧ (p.index.val + 1) * repr.size ≤ blk.repr.length
    · simp [shareRange, modifyRange, share, modify, hl, hb, List.range_succ]
    · simp [shareRange, modifyRange, share, modify, hl, hb, Repr.share]

theorem endShareRange_single (repr : Repr ty) (p : RawPtr ty) (s : Heap) :
    endShareRange repr p 1 s = endShare repr p s := by
  cases hl : s.allocations p.base
  · simp [endShareRange, modifyRange, endShare, modify, hl]
  · rename_i blk
    by_cases hb : 0 < repr.size ∧ (p.index.val + 1) * repr.size ≤ blk.repr.length
    · simp [endShareRange, modifyRange, endShare, modify, hl, hb, List.range_succ]
    · simp [endShareRange, modifyRange, endShare, modify, hl, hb, Repr.endShare]

theorem endBorrowRange_single (repr : Repr ty) (p : RawPtr ty)
    (data : Vector U8 repr.size) (value : ty) (decoded : repr.decode data = some value)
    (s : Heap) :
    endBorrowRange repr p [data] s = endBorrow repr p value data decoded s := by
  cases hl : s.allocations p.base
  · simp [endBorrowRange, modifyRange, endBorrow, modify, hl]
  · rename_i blk
    by_cases hb : 0 < repr.size ∧ (p.index.val + 1) * repr.size ≤ blk.repr.length
    · simp [endBorrowRange, modifyRange, endBorrow, modify, hl, hb, List.range_succ,
        Repr.endBorrow]
      generalize repr.decode data = result at decoded ⊢
      cases result
      · cases decoded
      · rfl
    · simp [endBorrowRange, modifyRange, endBorrow, modify, hl, hb, Repr.endBorrow]

end Heap
end Aeneas.Std
