module

public import Aeneas.Std.Heap.Provenance
public import Aeneas.Tactic.Solver.Grind

/-! Selection/update and selected-view layout laws. Arbitrary byte changes no
longer preserve `Inv`: compatibility and symbolic metadata must also be checked. -/

@[expose] public section

namespace Aeneas.Std

universe u v

theorem vector_mapM_some {α : Type u} {β : Type v} (xs : Vector α n) (f : α → β) :
    xs.mapM (fun x => some (f x)) = some (xs.map f) := by
  simpa only [Option.pure_def] using Vector.mapM_pure (m := Option) (xs := xs) f

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

theorem list_mapM_identity {α : Type u} (xs : List α) (f : α → Option α)
    (hf : ∀ x ∈ xs, f x = some x) : xs.mapM f = some xs := by
  induction xs
  · rfl
  · rename_i x xs ih
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp [List.mapM_cons, hx, ht]

theorem list_mapM_enabled {α : Type u} {β : Type v} (xs : List α) {ys : List β}
    {f : α → Option β} (h : xs.mapM f = some ys) :
    ∀ x ∈ xs, ∃ y, f x = some y := by
  induction xs generalizing ys
  · simp
  · rename_i a xs ih
    cases ha : f a
    · simp [List.mapM_cons, ha] at h
    · rename_i b
      cases ht : xs.mapM f
      · simp [List.mapM_cons, ha, ht] at h
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨b, ha⟩
        · exact ih ht x hx

theorem vector_mapM_enabled {α : Type u} {β : Type v} {xs : Vector α n}
    {ys : Vector β n} {f : α → Option β} (h : xs.mapM f = some ys)
    (i : Nat) (hi : i < n) : ∃ y, f xs[i] = some y := by
  have hl := vector_mapM_toList (f := f) xs
  rw [h] at hl
  exact list_mapM_enabled xs.toList hl.symm xs[i] (by simp)

def CellsDisjoint (reprT : Repr T) (i : Nat) (reprU : Repr U) (j : Nat) : Prop :=
  i + reprT.size ≤ j ∨ j + reprU.size ≤ i

namespace Repr

theorem align_pos (repr : Repr ty) : 0 < repr.align.val := by
  obtain ⟨k, hk⟩ := repr.align.property
  rw [hk]
  exact Nat.two_pow_pos k

theorem aligned_stride (repr : Repr ty) (i : Nat) :
    repr.align.val ∣ i * repr.size := Nat.dvd_mul_left_of_dvd repr.aligned i

@[simp] theorem select_toList (repr : Repr ty) (bytes : Vector Cell r)
    (i : Nat) (hi : i + repr.size ≤ r) :
    (repr.select bytes i hi).toList = (bytes.toList.drop i).take repr.size := by
  simp [select, Vector.toList_cast, Vector.toList_extract]

theorem select_getElem? (repr : Repr ty) (bytes : Vector Cell r)
    (i : Nat) (hi : i + repr.size ≤ r) (j : Nat) (hj : j < repr.size) :
    (repr.select bytes i hi)[j]? = bytes.toList[i + j]? := by
  rw [← Vector.getElem?_toList, select_toList, List.getElem?_take_of_lt hj,
    List.getElem?_drop]

@[simp] theorem update_toList (repr : Repr ty) (bytes : Vector Cell r)
    (i : Nat) (hi : i + repr.size ≤ r) (data : Vector Cell repr.size) :
    (repr.update bytes i hi data).toList =
      bytes.toList.take i ++ data.toList ++ bytes.toList.drop (i + repr.size) := by
  simp [update, Vector.toList_cast, Vector.toList_extract]
  apply List.take_of_length_le
  simp

theorem select_update (repr : Repr ty) (bytes : Vector Cell r)
    (i : Nat) (hi : i + repr.size ≤ r) (data : Vector Cell repr.size) :
    repr.select (repr.update bytes i hi data) i hi = data := by
  apply Vector.toList_inj.mp
  have hs : i ≤ r := by grind
  simp [Nat.min_eq_left hs]

theorem update_outside (repr : Repr ty) (bytes : Vector Cell r)
    (i : Nat) (hi : i + repr.size ≤ r) (data : Vector Cell repr.size)
    (j : Nat) (hj : j < i ∨ i + repr.size ≤ j) :
    (repr.update bytes i hi data).toList[j]? = bytes.toList[j]? := by
  have hs : i ≤ r := by grind
  rw [update_toList]
  rcases hj with hj | hj
  · simp [List.getElem?_append, Nat.min_eq_left hs, hj]
  · simp [List.getElem?_append, Nat.min_eq_left hs,
      show ¬ j < i by grind,
      show ¬ j - i < repr.size by grind, List.getElem?_drop]
    apply congrArg (bytes[·]?)
    grind

theorem update_inside (repr : Repr ty) (bytes : Vector Cell r)
    (i : Nat) (hi : i + repr.size ≤ r) (data : Vector Cell repr.size)
    (j : Nat) (hj : j < repr.size) :
    (repr.update bytes i hi data).toList[i + j]? = some data[j] := by
  have hs : i ≤ r := by grind
  rw [update_toList]
  simp [List.getElem?_append, Nat.min_eq_left hs,
    show ¬ i + j < i by grind, hj]

theorem select_update_disjoint (reprT : Repr T) (reprU : Repr U) (bytes : Vector Cell r)
    (i j : Nat) (hi : i + reprT.size ≤ r) (hj : j + reprU.size ≤ r)
    (data : Vector Cell reprT.size) (hd : CellsDisjoint reprT i reprU j) :
    reprU.select (reprT.update bytes i hi data) j hj = reprU.select bytes j hj := by
  apply Vector.toList_inj.mp
  apply List.ext_getElem?
  intro k
  simp only [select_toList]
  by_cases hk : k < reprU.size
  · have hout : j + k < i ∨ i + reprT.size ≤ j + k := by
      unfold CellsDisjoint at hd
      grind
    simpa [hk] using update_outside reprT bytes i hi data (j + k) hout
  · calc
      _ = none := List.getElem?_eq_none (by simp only [List.length_take]; grind)
      _ = _ := (List.getElem?_eq_none (by simp only [List.length_take]; grind)).symm

/-- Uninitialized symbolic bytes are not silently turned into readable values. -/
theorem readBytes_shared (data : Vector Byte n) (depth : Nat)
    (initialized : ∀ i : Fin n, data[i.val] ≠ .uninit) :
    readBytes n (data.map (Cell.shared depth)) = some data := by
  have hm := vector_mapM_toList (f := Cell.read) (data.map (Cell.shared depth))
  simp only [Vector.toList_map, List.mapM_map, Function.comp_def] at hm
  have hl : data.toList.mapM (fun byte => Cell.read (.shared depth byte)) =
      some data.toList := by
    apply list_mapM_identity
    intro byte hb
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hb
    have hn := initialized ⟨i, by simpa using hi⟩
    have hne : byte ≠ Byte.uninit := by simpa [← he] using hn
    cases byte
    · exact (hne rfl).elim
    · rfl
    · rfl
  rw [hl] at hm
  unfold readBytes
  cases h : (data.map (Cell.shared depth)).mapM Cell.read
  · simp [h] at hm
  · rename_i result
    simp only [h, Option.map_some, Option.some.injEq] at hm
    exact congrArg some (Vector.toList_inj.mp hm)

theorem writeBytes_shared (old data : Vector Byte n) :
    writeBytes n (old.map (Cell.shared 0)) data = some (data.map (Cell.shared 0)) := by
  simp only [writeBytes, Vector.zip_map_left, Vector.mapM_map, Function.comp_def,
    Prod.map, Cell.write]
  have hm := Vector.mapM_pure (m := Option) (xs := old.zip data)
    (fun p => Cell.shared 0 p.2)
  have he := congrArg (Vector.map (Cell.shared 0))
    (Vector.map_snd_zip (as := old) data)
  simp only [Vector.map_map, Function.comp_def] at he
  simpa only [Vector.map_map, Function.comp_def, id_eq, Option.pure_def] using
    hm.trans (congrArg some he)

end Repr

namespace Heap

theorem inv_empty : empty.Inv := ⟨fun _ _ => rfl, rfl⟩

@[simp] theorem allocations_storeRepr (s : Heap) (base other : Nat) (bytes : List Cell) :
    (s.storeRepr base bytes).allocations other =
      if other = base then (s.allocations base).map (fun b => { b with repr := bytes })
      else s.allocations other := by
  simp [storeRepr, update]

theorem Inv.base_lt {s : Heap} (h : s.Inv) {base : Nat} {block : Block}
    (hb : s.allocations base = some block) : base < s.next := by
  by_cases hn : base < s.next
  · exact hn
  · have he := h.1 base (Nat.le_of_not_gt hn)
    rw [hb] at he
    contradiction

theorem Inv.compatible {s : Heap} (h : s.Inv) {i j : Nat} {a b : Block}
    (ha : s.allocations i = some a) (hb : s.allocations j = some b)
    (different : i ≠ j) : Heap.compatible a b = true := by
  have hi := h.base_lt ha
  have hj := h.base_lt hb
  have hc := h.2
  unfold Heap.check at hc
  have row := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  simp only [ha, Bool.and_eq_true] at row
  have entry := List.all_eq_true.mp row.2 j (List.mem_range.mpr hj)
  simp only [different, ↓reduceIte, hb, Bool.and_eq_true] at entry
  exact entry.2

/-- Even a fully borrowed active alias blocks root cleanup. Permission
compatibility does not collapse that alias into "no outstanding loan". -/
theorem Inv.noAliases_unique {s : Heap} (hinv : s.Inv) {owner root id : Nat}
    {blk : Block} (noAliases : s.noAliases owner root = true)
    (hl : s.allocations id = some blk) (active : blk.active = true)
    (sameRoot : blk.root = root) : id = owner := by
  by_cases different : id = owner
  · exact different
  · unfold Heap.noAliases at noAliases
    have row := List.all_eq_true.mp noAliases id (List.mem_range.mpr (hinv.base_lt hl))
    simp [different, hl, active, sameRoot] at row

/-- Fixed-length updates preserve root liveness and layout even when updating
the root record itself. Physical alias compatibility is a separate obligation. -/
theorem live_storeRepr (s : Heap) (id : Nat) (bytes : List Cell) (block : Block) :
    (s.storeRepr id bytes).live block = s.live block := by
  simp only [live, allocations_storeRepr]
  split
  · rename_i hroot
    rw [hroot]
    cases s.allocations id
    · rfl
    · rfl
  · rfl

@[simp] theorem live_storeRepr_updated (s : Heap) (id : Nat) (bytes : List Cell)
    (block : Block) (newBytes : List Cell) :
    (s.storeRepr id bytes).live { block with repr := newBytes } = s.live block := by
  change (s.storeRepr id bytes).live block = s.live block
  exact live_storeRepr s id bytes block

theorem modify.spec (repr : Repr ty) (p : RawPtr ty)
    (change : ∀ {r}, Vector Cell r → Option (Vector Cell r))
    (s : Heap) (block : Block) (bytes : Vector Cell block.repr.length)
    (hl : s.allocations p.base = some block) (hlive : s.live block = true)
    (ha : repr.align.val ∣ block.bptr.val + p.byteOffset.val)
    (hc : change block.bytes = some bytes)
    (valid : (s.storeRepr p.base bytes.toList).check = true) :
    Heap.modify repr p change s = some (s.storeRepr p.base bytes.toList) := by
  simp [modify, hl, hlive, ha, hc, commit, valid]

end Heap
end Aeneas.Std
