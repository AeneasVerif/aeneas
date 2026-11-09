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

/-- Permission checking preserves symbolic initialization; the decoder validates
value-bearing bytes and may ignore uninitialized padding. -/
theorem readBytes_shared (data : Vector Byte n) (depth : Nat) :
    readBytes n (data.map (Cell.shared depth)) = some data := by
  simpa [readBytes, Vector.mapM_map, Function.comp_def, Cell.read] using
    vector_mapM_some data id

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

def Cell.PermWeakens (old new : Cell) : Prop :=
  ∀ other, old.compatible other = true → new.compatible other = true

theorem Cell.compatible_symm (a b : Cell) : a.compatible b = b.compatible a := by
  cases a
  · cases b
    · simp [Cell.compatible, Bool.and_comm, eq_comm]
    · rfl
  · cases b <;> rfl

theorem Cell.PermWeakens.refl (c : Cell) : c.PermWeakens c := fun _ h => h

theorem Cell.PermWeakens.writer (old new : Byte) :
    (Cell.shared 0 old).PermWeakens (.shared 0 new) := by
  intro other h
  cases other
  · simp [Cell.compatible] at h
  · rfl

theorem Cell.PermWeakens.borrow (old : Cell) : old.PermWeakens .borrowed :=
  fun _ _ => rfl

theorem Cell.PermWeakens.share (depth : Nat) (byte : Byte) :
    (Cell.shared depth byte).PermWeakens (.shared (depth + 1) byte) := by
  intro other h
  cases other
  · simp only [Cell.compatible, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨by simp, h.1.2⟩, h.2⟩
  · rfl

namespace Heap

theorem readRange_single (repr : Repr ty) (p : RawPtr ty) (s : Heap) :
    readRange repr p 1 s = (read repr p s).map (fun value => [value]) := by
  cases hl : s.allocations p.provenance
  · simp [readRange, read, hl]
  · rename_i blk
    by_cases hv : s.live blk = true ∧ blk.bptr.val ≤ p.address.val ∧
        repr.align.val ∣ p.address.val
    · obtain ⟨hlive, hlo, ha⟩ := hv
      by_cases hs : 0 < repr.size
      · by_cases hb : p.offsetFrom blk.bptr + repr.size ≤ blk.repr.length
        · have habs : p.address.val + repr.size ≤ blk.bptr.val + blk.repr.length := by
            unfold RawPtr.offsetFrom at hb
            agrind
          simp [readRange, read, hl, hlive, hlo, ha, hs, hb, habs,
            List.range_succ, Repr.read, Option.bind_assoc]
          apply congrArg (fun f =>
            (Repr.readBytes repr.size (repr.select blk.bytes (p.offsetFrom blk.bptr) hb)).bind f)
          funext data
          change ((repr.decode data).bind (fun value => some [value])) =
            (repr.decode data).map (fun value => [value])
          cases repr.decode data
          · rfl
          · rfl
        · have habs : ¬ p.address.val + repr.size ≤ blk.bptr.val + blk.repr.length := by
            unfold RawPtr.offsetFrom at hb
            agrind
          simp [readRange, read, hl, hlive, hlo, ha, hs, hb, habs, Repr.read]
      · simp [readRange, read, hl, ha, hs, Repr.read]
    · have hguard : ¬ ((s.live blk = true ∧ blk.bptr.val ≤ p.address.val) ∧
          repr.align.val ∣ p.address.val) :=
        fun h => hv ⟨h.1.1, h.1.2, h.2⟩
      simp [readRange, read, hl, Bool.and_eq_true, hguard]

theorem borrowRange_single (repr : Repr ty) (p : RawPtr ty) (s : Heap) :
    borrowRange repr p 1 s = borrow repr p s := by
  unfold borrowRange modifyRange borrow
  apply congrArg (fun (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r)) =>
    modify repr p change s)
  funext r bytes i
  by_cases hs : 0 < repr.size
  · by_cases hb : i + repr.size ≤ r
    · simp [hs, hb, List.range_succ]
    · simp [hs, hb, Repr.borrow]
  · simp [hs, Repr.borrow]

theorem shareRange_single (repr : Repr ty) (p : RawPtr ty) (s : Heap) :
    shareRange repr p 1 s = share repr p s := by
  unfold shareRange modifyRange share
  apply congrArg (fun (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r)) =>
    modify repr p change s)
  funext r bytes i
  by_cases hs : 0 < repr.size
  · by_cases hb : i + repr.size ≤ r
    · simp [hs, hb, List.range_succ]
    · simp [hs, hb, Repr.share]
  · simp [hs, Repr.share]

theorem endShareRange_single (repr : Repr ty) (p : RawPtr ty) (s : Heap) :
    endShareRange repr p 1 s = endShare repr p s := by
  unfold endShareRange modifyRange endShare
  apply congrArg (fun (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r)) =>
    modify repr p change s)
  funext r bytes i
  by_cases hs : 0 < repr.size
  · by_cases hb : i + repr.size ≤ r
    · simp [hs, hb, List.range_succ]
    · simp [hs, hb, Repr.endShare]
  · simp [hs, Repr.endShare]

theorem endBorrowRange_single (repr : Repr ty) (p : RawPtr ty)
    (data : Vector Byte repr.size) (s : Heap) :
    endBorrowRange repr p [data] s = endBorrow repr p data s := by
  unfold endBorrowRange endBorrow
  apply congrArg (fun (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r)) =>
    modify repr p change s)
  funext r bytes i
  by_cases hs : 0 < repr.size
  · by_cases hb : i + repr.size ≤ r
    · simp [hs, hb]
    · simp [hs, hb, Repr.endBorrow]
  · simp [hs, Repr.endBorrow]

theorem compatible_iff (a b : Block) :
    compatible a b = true ↔
      a.active = false ∨ b.active = false ∨
        ∀ (i : Nat) (hi : i < a.repr.length) (j : Nat) (hj : j < b.repr.length),
          a.bptr.val + i = b.bptr.val + j →
            Cell.compatible a.repr[i] b.repr[j] = true := by
  have all_zip (xs : List Cell) (f : Cell × Nat → Bool) :
      xs.zipIdx.all f = true ↔ ∀ (i : Nat) (hi : i < xs.length), f (xs[i], i) = true := by
    rw [List.all_eq_true]
    constructor
    · intro h i hi
      apply h
      exact List.mem_of_getElem? (i := i)
        (by simp [List.getElem?_zipIdx, List.getElem?_eq_getElem hi])
    · intro h x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      simpa using h i (by simpa using hi)
  simp only [compatible, Bool.or_eq_true, Bool.not_eq_true', all_zip,
    bne_iff_ne]
  simp only [or_assoc]
  grind

theorem compatible_symm (a b : Block) : compatible a b = compatible b a := by
  apply Bool.eq_iff_iff.mpr
  rw [compatible_iff, compatible_iff]
  constructor
  · rintro (ha | hb | hc)
    · exact .inr (.inl ha)
    · exact .inl hb
    · exact .inr (.inr (fun j hj i hi he =>
        Cell.compatible_symm _ _ ▸ hc i hi j hj he.symm))
  · rintro (hb | ha | hc)
    · exact .inr (.inl hb)
    · exact .inl ha
    · exact .inr (.inr (fun i hi j hj he =>
        Cell.compatible_symm _ _ ▸ hc j hj i hi he.symm))

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

theorem Inv.validBlock {s : Heap} (h : s.Inv) {id : Nat} {blk : Block}
    (hl : s.allocations id = some blk) : validBlock s blk = true := by
  have row := List.all_eq_true.mp h.2 id (List.mem_range.mpr (h.base_lt hl))
  simp only [hl, Bool.and_eq_true] at row
  exact row.1

theorem Inv.validCell {s : Heap} (h : s.Inv) {id : Nat} {blk : Block}
    (hl : s.allocations id = some blk) (i : Nat) (hi : i < blk.repr.length) :
    match blk.repr[i] with
    | .borrowed => True
    | .shared _ byte => validByte s byte = true := by
  have hv := h.validBlock hl
  simp only [Heap.validBlock, Bool.and_eq_true] at hv
  have hc := List.all_eq_true.mp hv.2 _ (List.getElem_mem hi)
  cases he : blk.repr[i]
  · simpa only [he] using hc
  · trivial

theorem Inv.validSelected {s : Heap} (h : s.Inv) {id : Nat} {blk : Block}
    {repr : Repr ty} {offset : Nat} {data : Vector Cell repr.size}
    (hl : s.allocations id = some blk) (hb : offset + repr.size ≤ blk.repr.length)
    (selected : repr.select blk.bytes offset hb = data)
    (i : Nat) (hi : i < repr.size) :
    match data[i] with
    | .borrowed => True
    | .shared _ byte => validByte s byte = true := by
  have he := Repr.select_getElem? repr blk.bytes offset hb i hi
  rw [selected, Vector.getElem?_eq_getElem hi] at he
  have hidx : offset + i < blk.repr.length := by grind
  have he' : data[i] = blk.repr[offset + i] := by
    simpa [Block.bytes, List.getElem?_eq_getElem hidx] using he
  rw [he']
  exact h.validCell hl _ hidx

theorem validByte_storeRepr (s : Heap) (id : Nat) (bytes : List Cell) (byte : Byte) :
    validByte (s.storeRepr id bytes) byte = validByte s byte := by
  cases byte
  · rfl
  · rfl
  · rename_i p lane
    by_cases he : p.provenance = id
    · simp only [validByte, allocations_storeRepr, he, ↓reduceIte]
      cases s.allocations id <;> rfl
    · simp [validByte, he]

theorem validBlock_storeRepr (s : Heap) (id : Nat) (bytes : List Cell)
    (blk : Block) (length : ∀ old, s.allocations id = some old → bytes.length = old.repr.length) :
    validBlock (s.storeRepr id bytes) blk = validBlock s blk := by
  by_cases he : blk.root = id
  · simp only [validBlock, allocations_storeRepr, he, ↓reduceIte, validByte_storeRepr]
    cases hl : s.allocations id
    · rfl
    · rename_i old
      simp [length old hl]
  · simp only [validBlock, allocations_storeRepr, he, ↓reduceIte, validByte_storeRepr]

/-- Local replacement law: layout stays fixed, bytes are well formed, and no
new conflicting observer is introduced. This is internal invariant machinery,
not a client precondition. In particular, arbitrary restoration does not qualify. -/
theorem storeRepr_Inv {s : Heap} {id : Nat} {blk : Block} (hinv : s.Inv)
    (hl : s.allocations id = some blk) (bytes : List Cell)
    (length : bytes.length = blk.repr.length)
    (valid : ∀ cell ∈ bytes, match cell with
      | .borrowed => True
      | .shared _ byte => validByte s byte = true)
    (weaker : ∀ (i : Nat) (hi : i < blk.repr.length),
      (blk.repr[i]).PermWeakens (bytes[i]'(by grind))) :
    (s.storeRepr id bytes).Inv := by
  have length' : ∀ old, s.allocations id = some old → bytes.length = old.repr.length := by
    intro old ho
    have he := Option.some.inj (ho.symm.trans hl)
    simpa [he] using length
  have vb : validBlock s { blk with repr := bytes } = true := by
    have original := hinv.validBlock hl
    simp only [validBlock, Bool.and_eq_true] at original ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [bounded, length] using original.1.1
    · simpa [length] using original.1.2
    · apply List.all_eq_true.mpr
      intro cell hc
      cases cell
      · exact valid _ hc
      · rfl
  have compat : ∀ other, compatible blk other = true →
      compatible { blk with repr := bytes } other = true := by
    intro other hc
    rw [compatible_iff] at hc ⊢
    rcases hc with ha | hb | hc
    · exact .inl ha
    · exact .inr (.inl hb)
    · refine .inr (.inr ?_)
      intro i hi j hj he
      have hi' : i < blk.repr.length := by simpa [length] using hi
      exact weaker i hi' other.repr[j] (hc i hi' j hj he)
  refine ⟨storeRepr_support s id bytes hinv (hinv.base_lt hl), ?_⟩
  apply List.all_eq_true.mpr
  intro i hi
  have row := List.all_eq_true.mp hinv.2 i hi
  cases ha : s.allocations i
  · simp [ha] at row
  · rename_i a
    simp only [ha, Bool.and_eq_true] at row
    have vi : validBlock (s.storeRepr id bytes)
        (if i = id then { a with repr := bytes } else a) = true := by
      rw [validBlock_storeRepr _ _ _ _ length']
      split
      · rename_i he
        have he' : a = blk := Option.some.inj ((he ▸ ha).symm.trans hl)
        simpa [he'] using vb
      · exact row.1
    by_cases he : i = id
    ·
      have he' : a = blk := Option.some.inj ((he ▸ ha).symm.trans hl)
      subst i
      subst a
      simp only [allocations_storeRepr, ↓reduceIte, hl, Option.map_some, Bool.and_eq_true]
      refine ⟨by simpa using vi, ?_⟩
      apply List.all_eq_true.mpr
      intro j hj
      by_cases hjid : id = j
      · simp [hjid]
      · have entry := List.all_eq_true.mp row.2 j hj
        cases hb : s.allocations j
        · simp [hjid, hb] at entry
        · rename_i b
          simp only [hjid, ↓reduceIte, hb, Bool.and_eq_true] at entry
          have hji : j ≠ id := Ne.symm hjid
          simpa [hjid, hji, hb, length, overlaps] using
            And.intro entry.1 (compat b entry.2)
    ·
      simp only [allocations_storeRepr, he, ↓reduceIte, ha, Bool.and_eq_true]
      refine ⟨by simpa [he] using vi, ?_⟩
      apply List.all_eq_true.mpr
      intro j hj
      by_cases hij : i = j
      · simp [hij]
      · have entry := List.all_eq_true.mp row.2 j hj
        cases hb : s.allocations j
        · simp [hij, hb] at entry
        · rename_i b
          simp only [hij, ↓reduceIte, hb, Bool.and_eq_true] at entry
          by_cases hjid : j = id
          · have he' : b = blk := Option.some.inj ((hjid ▸ hb).symm.trans hl)
            subst j
            subst b
            have hc := compat a (by rw [compatible_symm]; exact entry.2)
            rw [compatible_symm] at hc
            simpa [hij, hl, length, overlaps] using And.intro entry.1 hc
          · simpa [hij, hjid, hb] using entry

theorem update_Inv {s : Heap} {repr : Repr ty} {p : RawPtr ty} {blk : Block}
    (hinv : s.Inv) (hl : s.allocations p.provenance = some blk)
    (hb : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length)
    (old new : Vector Cell repr.size)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb = old)
    (valid : ∀ (i : Nat) (hi : i < repr.size), match new[i] with
      | .borrowed => True
      | .shared _ byte => validByte s byte = true)
    (weaker : ∀ (i : Nat) (hi : i < repr.size), old[i].PermWeakens new[i]) :
    (s.storeRepr p.provenance (repr.update blk.bytes (p.offsetFrom blk.bptr) hb new).toList).Inv := by
  let bytes := repr.update blk.bytes (p.offsetFrom blk.bptr) hb new
  have at_index (i : Nat) (hi : i < blk.repr.length) :
      (bytes[i] = blk.repr[i] ∧
        (blk.repr[i]).PermWeakens bytes[i]) ∨
      ∃ (j : Nat) (hj : j < repr.size),
        bytes[i] = new[j] ∧
          blk.repr[i] = old[j] := by
    by_cases inside : (p.offsetFrom blk.bptr) ≤ i ∧ i < (p.offsetFrom blk.bptr) + repr.size
    · let j := i - (p.offsetFrom blk.bptr)
      have hj : j < repr.size := by dsimp [j]; grind
      have he : (p.offsetFrom blk.bptr) + j = i := by dsimp [j]; grind
      have hs := Repr.select_getElem? repr blk.bytes (p.offsetFrom blk.bptr) hb j hj
      rw [selected, he, Vector.getElem?_eq_getElem hj] at hs
      have hn := Repr.update_inside repr blk.bytes (p.offsetFrom blk.bptr) hb new j hj
      rw [he, List.getElem?_eq_getElem (by simp only [Vector.length_toList]; exact hi)] at hn
      exact .inr ⟨j, hj, Option.some.inj hn,
        by simpa [Block.bytes, List.getElem?_eq_getElem hi] using hs.symm⟩
    · have he := Repr.update_outside repr blk.bytes (p.offsetFrom blk.bptr) hb new i (by grind)
      have hbc : blk.bytes.toList = blk.repr := by simp [Block.bytes]
      change bytes.toList[i]? = blk.bytes.toList[i]? at he
      rw [hbc, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem (by simpa only [Vector.length_toList] using hi)] at he
      have he' : bytes[i] = blk.repr[i] := by
        simpa only [Vector.getElem_toList] using Option.some.inj he
      exact .inl ⟨he', he' ▸ Cell.PermWeakens.refl _⟩
  apply storeRepr_Inv hinv hl bytes.toList (by simp only [Vector.length_toList])
  · intro cell hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    simp only [Vector.getElem_toList]
    have hi' : i < blk.repr.length := by simpa only [Vector.length_toList] using hi
    rcases at_index i hi' with ⟨he, _⟩ | ⟨j, hj, he, _⟩
    · rw [he]
      have hv := hinv.validBlock hl
      simp only [validBlock, Bool.and_eq_true] at hv
      have hv := List.all_eq_true.mp hv.2 _ (List.getElem_mem hi')
      cases hec : blk.repr[i]
      · simpa only [hec] using hv
      · trivial
    · rw [he]
      exact valid j hj
  · intro i hi
    simp only [Vector.getElem_toList]
    rcases at_index i hi with ⟨_, hw⟩ | ⟨j, hj, he, ho⟩
    · exact hw
    · rw [he, ho]
      exact weaker j hj

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
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (s : Heap) (block : Block) (bytes : Vector Cell block.repr.length)
    (hl : s.allocations p.provenance = some block) (hlive : s.live block = true)
    (hlo : block.bptr.val ≤ p.address.val) (ha : repr.align.val ∣ p.address.val)
    (hc : change block.bytes (p.offsetFrom block.bptr) = some bytes)
    (valid : (s.storeRepr p.provenance bytes.toList).check = true) :
    Heap.modify repr p change s = some (s.storeRepr p.provenance bytes.toList) := by
  simp [modify, hl, hlive, hlo, ha, hc, commit, valid]

end Heap
end Aeneas.Std
