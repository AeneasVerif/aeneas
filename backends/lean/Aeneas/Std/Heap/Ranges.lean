module

public import Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Separation

/-! Contiguous byte footprints and range contracts. The grouping descriptor is
proof infrastructure, not a proposed Rust representation of `Unit`. -/

@[expose] public section

namespace Aeneas.Std

def Repr.region (repr : Repr T) (count : Nat) : Repr Unit where
  size := count * repr.size
  align := repr.align
  decode := fun _ => some ()
  aligned := repr.aligned_stride count
  complete := fun value => by
    cases value
    exact ⟨Vector.replicate _ ⟨0⟩, rfl⟩

theorem range_element_bound {i count start size r : Nat}
    (h : i < count) (hb : start + count * size ≤ r) :
    start + i * size + size ≤ r := by
  have hm := Nat.mul_le_mul_right size (Nat.succ_le_of_lt h)
  simp only [Nat.succ_mul] at hm
  grind

theorem mapM_range'_some {f : Nat → Option T} (values : List T) (start : Nat)
    (h : ∀ i (hi : i < values.length), f (start + i) = some values[i]) :
    (List.range' start values.length).mapM f = some values := by
  induction values generalizing start
  · simp
  · rename_i value values ih
    have hhead : f start = some value := by
      have he := h 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at he
      exact he
    have htail : ∀ i (hi : i < values.length),
        f (start + 1 + i) = some values[i] := by
      intro i hi
      rw [show start + 1 + i = start + (i + 1) by grind]
      have he := h (i + 1) (by simp; grind)
      simp only [List.getElem_cons_succ] at he
      exact he
    simp [List.range'_succ, List.mapM_cons, hhead, ih _ htail]

namespace SepLogic

/-- Splitting and recombining adjacent footprints preserves their exact resources. -/
theorem block_append (repr : Repr T) (p q : RawPtr T) (a b : List (Cell U8))
    (hbase : q.base = p.base) (hoff : q.byteOffset.val = p.byteOffset.val + a.length)
    (hlen : repr.align.val ∣ a.length) (h : Fragment) :
    block repr p (a ++ b) h ↔ sep (block repr p a) (block repr q b) h := by
  constructor
  · rintro ⟨hp, rfl⟩
    refine ⟨cellsHeap repr.align p.base p.byteOffset.val a,
      cellsHeap repr.align q.base q.byteOffset.val b, ?_, ?_, ⟨hp, rfl⟩, ?_⟩
    · simpa [hbase, hoff] using disjoint_cellsHeap_append repr.align p.base p.byteOffset.val a b
    · simpa [hbase, hoff] using cellsHeap_append repr.align p.base p.byteOffset.val a b
    · exact ⟨hoff ▸ Nat.dvd_add hp hlen, rfl⟩
  · rintro ⟨_, _, _, rfl, ⟨hp, rfl⟩, ⟨_, rfl⟩⟩
    exact ⟨hp, by simp only [hbase, hoff, cellsHeap_append]⟩

/-- A range owns one encoding for each exact value and the whole byte footprint. -/
def pointsToRange (repr : Repr T) (p : RawPtr T) (values : Vector T count)
    (depth : Nat := 0) : Assertion :=
  fun h => ∃ data : Vector (Vector U8 repr.size) count,
    (∀ i : Fin count, repr.decode data[i.val] = some values[i.val]) ∧
    block repr p (data.flatMap (fun bytes => bytes.map (Cell.shared depth ∘ some))).toList h

end SepLogic

/-- Recover any element's cells from the selected contiguous region. -/
theorem Repr.select_region (repr : Repr T) (bytes : Vector (Cell U8) r)
    (start count : Nat) (data : Vector (Vector (Cell U8) repr.size) count)
    (hb : start + count * repr.size ≤ r)
    (hs : (repr.region count).select bytes start hb = data.flatMap id)
    (i : Nat) (hi : i < count) :
    repr.select bytes (start + i * repr.size) (range_element_bound hi hb) = data[i] := by
  apply Vector.toList_inj.mp
  apply List.ext_getElem?
  intro j
  by_cases hj : j < repr.size
  · have hend := range_element_bound (start := 0) (size := repr.size)
      (r := count * repr.size) hi (by simp)
    have hij : i * repr.size + j < count * repr.size := by grind
    have he := (repr.region count).select_getElem? bytes start hb (i * repr.size + j) hij
    rw [hs] at he
    change (data.flatMap id)[i * repr.size + j]? =
      bytes.toList[start + (i * repr.size + j)]? at he
    have hdiv : (i * repr.size + j) / repr.size = i := by
      rw [Nat.mul_comm i repr.size, Nat.mul_add_div (show 0 < repr.size by grind),
        Nat.div_eq_of_lt hj, Nat.add_zero]
    have hv : (data.flatMap id)[i * repr.size + j] = data[i][j] := by
      rw [Vector.getElem_flatMap hij]
      simp [hdiv, Nat.add_mod, Nat.mod_eq_of_lt hj]
    rw [Vector.getElem?_eq_getElem hij, hv] at he
    simpa [Repr.select_toList, hj, Nat.add_assoc] using he.symm
  · simp [Repr.select_toList, hj]

theorem Repr.select_region_ext (repr : Repr T) (bytes : Vector (Cell U8) r)
    (start count : Nat) (data : Vector (Vector (Cell U8) repr.size) count)
    (hb : start + count * repr.size ≤ r) (hsize : 0 < repr.size)
    (hs : ∀ i (hi : i < count),
      repr.select bytes (start + i * repr.size) (range_element_bound hi hb) = data[i]) :
    (repr.region count).select bytes start hb = data.flatMap id := by
  apply Vector.toList_inj.mp
  apply List.ext_getElem?
  intro j
  by_cases hj : j < count * repr.size
  · have hi : j / repr.size < count := (Nat.div_lt_iff_lt_mul hsize).mpr hj
    have hk : j % repr.size < repr.size := Nat.mod_lt _ hsize
    have he := repr.select_getElem? bytes (start + j / repr.size * repr.size)
      (range_element_bound hi hb) (j % repr.size) hk
    rw [hs _ hi] at he
    have hindex : start + j / repr.size * repr.size + j % repr.size = start + j := by
      have hd := Nat.mod_add_div j repr.size
      grind
    rw [hindex] at he
    simp only [Vector.getElem?_eq_getElem hk] at he
    have hflat : (data.flatMap id)[j]? = some data[j / repr.size][j % repr.size] := by
      rw [Vector.getElem?_eq_getElem hj, Vector.getElem_flatMap hj]
      rfl
    calc
      _ = ((bytes.toList.drop start).take (count * repr.size))[j]? :=
        congrArg (fun xs : List (Cell U8) => xs[j]?)
          ((repr.region count).select_toList bytes start hb)
      _ = bytes.toList[start + j]? := by
        rw [List.getElem?_take_of_lt hj, List.getElem?_drop]
      _ = some data[j / repr.size][j % repr.size] := he.symm
      _ = _ := hflat.symm.trans (Vector.getElem?_toList (xs := data.flatMap id)).symm
  · simp [Repr.select_toList, Repr.region, hj]

theorem Repr.eq_update_of_select (repr : Repr T) (bytes result : Vector (Cell U8) r)
    (start : Nat) (hb : start + repr.size ≤ r) (data : Vector (Cell U8) repr.size)
    (hs : repr.select result start hb = data)
    (hout : ∀ j, j < start ∨ start + repr.size ≤ j →
      result.toList[j]? = bytes.toList[j]?) :
    result = repr.update bytes start hb data := by
  apply Vector.toList_inj.mp
  apply List.ext_getElem?
  intro j
  by_cases hj : j < start ∨ start + repr.size ≤ j
  · rw [hout j hj, repr.update_outside bytes start hb data j hj]
  · have hk : j - start < repr.size := by grind
    have he := repr.select_getElem? result start hb (j - start) hk
    rw [hs, show start + (j - start) = j by grind] at he
    rw [← he, Vector.getElem?_eq_getElem hk]
    simpa [show start + (j - start) = j by grind] using
      (repr.update_inside bytes start hb data (j - start) hk).symm

theorem range_elements_disjoint (repr : Repr T) (start i j : Nat) (hne : i ≠ j) :
    CellsDisjoint repr (start + i * repr.size) repr (start + j * repr.size) := by
  rcases Nat.lt_or_gt_of_ne hne with hij | hij
  · have hm := Nat.mul_le_mul_right repr.size (Nat.succ_le_of_lt hij)
    simp only [Nat.succ_mul] at hm
    exact Or.inl (by grind)
  · have hm := Nat.mul_le_mul_right repr.size (Nat.succ_le_of_lt hij)
    simp only [Nat.succ_mul] at hm
    exact Or.inr (by grind)

/-- Local element transformations compose into one atomic region update. -/
theorem Repr.fold_region (repr : Repr T) (bytes : Vector (Cell U8) r)
    (start count : Nat) (old new : Vector (Vector (Cell U8) repr.size) count)
    (change : Vector (Cell U8) r → Nat → Option (Vector (Cell U8) r))
    (hb : start + count * repr.size ≤ r)
    (hs : (repr.region count).select bytes start hb = old.flatMap id)
    (hc : ∀ current i (hi : i < count),
      repr.select current (start + i * repr.size) (range_element_bound hi hb) = old[i] →
      change current i = some (repr.update current (start + i * repr.size)
        (range_element_bound hi hb) new[i]))
    (hsize : 0 < repr.size) :
    (List.range count).foldlM change bytes =
      some ((repr.region count).update bytes start hb (new.flatMap id)) := by
  have loop : ∀ k, k ≤ count → ∃ current,
      (List.range k).foldlM change bytes = some current ∧
      (∀ i (hi : i < count),
        repr.select current (start + i * repr.size) (range_element_bound hi hb) =
          if i < k then new[i] else old[i]) ∧
      (∀ j, j < start ∨ start + count * repr.size ≤ j →
        current.toList[j]? = bytes.toList[j]?) := by
    intro k hk
    induction k
    · refine ⟨bytes, rfl, ?_, fun _ _ => rfl⟩
      intro i hi
      simpa using repr.select_region bytes start count old hb hs i hi
    · rename_i k ih
      obtain ⟨current, hrun, hsel, hout⟩ := ih (by grind)
      have hkc : k < count := by grind
      let next := repr.update current (start + k * repr.size)
        (range_element_bound hkc hb) new[k]
      have hstep : change current k = some next := hc current k hkc (by simpa using hsel k hkc)
      refine ⟨next, ?_, ?_, ?_⟩
      · simp [List.range_succ, List.foldlM_append, hrun, hstep]
      · intro i hi
        by_cases he : i = k
        · subst i
          simpa [next] using repr.select_update current (start + k * repr.size)
            (range_element_bound hkc hb) new[k]
        · rw [repr.select_update_disjoint repr current (start + k * repr.size)
            (start + i * repr.size) (range_element_bound hkc hb) (range_element_bound hi hb)
            new[k] (range_elements_disjoint repr start k i (Ne.symm he))]
          rw [hsel i hi]
          simp only [show (i < k + 1) = (i < k) by grind]
      · intro j hj
        have hlocal : j < start + k * repr.size ∨ start + k * repr.size + repr.size ≤ j := by
          have hend := range_element_bound hkc (Nat.le_refl (start + count * repr.size))
          grind
        exact (repr.update_outside current _ _ _ j hlocal).trans (hout j hj)
  obtain ⟨current, hrun, hsel, hout⟩ := loop count (Nat.le_refl _)
  have hnew : (repr.region count).select current start hb = new.flatMap id :=
    repr.select_region_ext current start count new hb hsize (fun i hi => by simpa [hi] using hsel i hi)
  rw [hrun, (repr.region count).eq_update_of_select bytes current start hb _ hnew hout]

namespace SepLogic

theorem modifyRange.spec (repr : Repr T) (p : RawPtr T)
    (old new : Vector (Vector (Cell U8) repr.size) count)
    (change : ∀ {r}, Vector (Cell U8) r → Nat → Option (Vector (Cell U8) r))
    (hcount : 0 < count) (hsize : 0 < repr.size)
    (hc : ∀ {r} (bytes : Vector (Cell U8) r) i (hi : i < count)
      (hb : p.byteOffset.val + count * repr.size ≤ r),
      repr.select bytes (p.byteOffset.val + i * repr.size) (range_element_bound hi hb) = old[i] →
      change bytes i = some (repr.update bytes (p.byteOffset.val + i * repr.size)
        (range_element_bound hi hb) new[i])) :
    Triple (block repr p (old.flatMap id).toList)
      (fun s (_ : Unit) s' => Heap.modifyRange repr p count change s = some s')
      (fun _ => block repr p (new.flatMap id).toList) := by
  have ht := modify.spec (repr.region count) (⟨p.base, p.byteOffset⟩ : RawPtr Unit)
    (old.flatMap id) (new.flatMap id)
    (fun bytes =>
      if (count = 0 ∨ 0 < repr.size) ∧ p.byteOffset.val + count * repr.size ≤ bytes.size then
        (List.range count).foldlM change bytes
      else none)
    (Nat.mul_pos hcount hsize) (by
      intro r bytes hb hs
      change p.byteOffset.val + count * repr.size ≤ r at hb
      simp only [hsize, or_true, true_and, Vector.size, hb, ↓reduceIte]
      exact repr.fold_region bytes p.byteOffset.val count old new change hb hs
        (fun current i hi hs => hc current i hi hb hs) hsize)
  exact ht

theorem borrowRange_cells.spec (repr : Repr T) (p : RawPtr T)
    (data : Vector (Vector U8 repr.size) count) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (block repr p (data.flatMap (fun bytes => bytes.map (Cell.shared 0 ∘ some))).toList)
      (fun s (_ : Unit) s' => Heap.borrowRange repr p count s = some s')
      (fun _ => block repr p (List.replicate (count * repr.size) .borrowed)) := by
  let old := data.map fun bytes => bytes.map (Cell.shared 0 ∘ some)
  let new : Vector (Vector (Cell U8) repr.size) count :=
    Vector.replicate count (Vector.replicate repr.size .borrowed)
  have ht := modifyRange.spec repr p old new
    (fun bytes i => repr.borrow bytes (p.byteOffset.val + i * repr.size)) hcount hsize (by
      intro r bytes i hi hb hs
      simp only [Repr.borrow, hsize, range_element_bound hi hb, and_self, ↓reduceDIte, hs]
      simp [old, new, Function.comp_def, Cell.borrow, vector_mapM_some]
      apply congrArg (repr.update bytes _ _)
      apply Vector.ext
      intro j hj
      simp)
  simpa [old, new, Vector.flatMap_map, Vector.flatMap_replicate, Heap.borrowRange] using ht

theorem shareRange_cells.spec (repr : Repr T) (p : RawPtr T)
    (data : Vector (Vector U8 repr.size) count) (depth : Nat)
    (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (block repr p (data.flatMap (fun bytes => bytes.map (Cell.shared depth ∘ some))).toList)
      (fun s (_ : Unit) s' => Heap.shareRange repr p count s = some s')
      (fun _ => block repr p
        (data.flatMap (fun bytes => bytes.map (Cell.shared (depth + 1) ∘ some))).toList) := by
  have ht := modifyRange.spec repr p
    (data.map fun bytes => bytes.map (Cell.shared depth ∘ some))
    (data.map fun bytes => bytes.map (Cell.shared (depth + 1) ∘ some))
    (fun bytes i => repr.share bytes (p.byteOffset.val + i * repr.size)) hcount hsize (by
      intro r bytes i hi hb hs
      simp [Repr.share, hsize, range_element_bound hi hb, hs, Function.comp_def,
        Cell.share, vector_mapM_some])
  simpa [Vector.flatMap_map, Heap.shareRange] using ht

theorem endShareRange_cells.spec (repr : Repr T) (p : RawPtr T)
    (data : Vector (Vector U8 repr.size) count) (depth : Nat)
    (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (block repr p
      (data.flatMap (fun bytes => bytes.map (Cell.shared (depth + 1) ∘ some))).toList)
      (fun s (_ : Unit) s' => Heap.endShareRange repr p count s = some s')
      (fun _ => block repr p
        (data.flatMap (fun bytes => bytes.map (Cell.shared depth ∘ some))).toList) := by
  have ht := modifyRange.spec repr p
    (data.map fun bytes => bytes.map (Cell.shared (depth + 1) ∘ some))
    (data.map fun bytes => bytes.map (Cell.shared depth ∘ some))
    (fun bytes i => repr.endShare bytes (p.byteOffset.val + i * repr.size)) hcount hsize (by
      intro r bytes i hi hb hs
      simp [Repr.endShare, hsize, range_element_bound hi hb, hs, Function.comp_def,
        Cell.endShare, vector_mapM_some])
  simpa [Vector.flatMap_map, Heap.endShareRange] using ht

theorem read_of_pointsToRange {s : Heap} {repr : Repr T} {p : RawPtr T}
    {values : Vector T count} {depth : Nat} {h : Fragment}
    (hcount : 0 < count) (hsize : 0 < repr.size)
    (hp : pointsToRange repr p values depth h) (hm : Fragment.Matches s h) :
    Heap.readRange repr p count s = some values.toList := by
  obtain ⟨data, decoded, hpa, rfl⟩ := hp
  let grouped := repr.region count
  let q : RawPtr Unit := ⟨p.base, p.byteOffset⟩
  have hpositive : 0 < grouped.size := Nat.mul_pos hcount hsize
  obtain ⟨blk, hb, hl, ha, hs⟩ := bytes_of_matches (repr := grouped) (p := q)
    (data := data.flatMap (fun bytes => bytes.map (Cell.shared depth ∘ some))) hpositive hm
  change p.byteOffset.val + count * repr.size ≤ blk.repr.length at hb
  change s.allocations p.base = some blk at hl
  change repr.align.val ∣ blk.alignment.val at ha
  have hr (i : Nat) (hi : i < count) :
      repr.read blk.bytes (p.byteOffset.val + i * repr.size) = some values[i] := by
    have hsel := repr.select_region blk.bytes p.byteOffset.val count
      (data.map fun bytes => bytes.map (Cell.shared depth ∘ some)) hb
      (by simpa [Vector.flatMap_map] using hs) i hi
    simp only [Vector.getElem_map] at hsel
    simp [Repr.read, hsize, range_element_bound hi hb, hsel,
      Repr.readBytes_shared, decoded ⟨i, hi⟩]
  have hmap : (List.range count).mapM
      (fun i => repr.read blk.bytes (p.byteOffset.val + i * repr.size)) =
        some values.toList := by
    simpa [List.range_eq_range'] using mapM_range'_some values.toList 0
      (fun i hi => by simpa using hr i (by simpa using hi))
  simpa [Heap.readRange, hl, hpa, hsize, hb, ha, grouped, q, Repr.region] using hmap

theorem readRange_transfer.spec (repr : Repr T) (p : RawPtr T)
    (values : Vector T count) (depth : Nat) (change : Heap → Option Heap) (Q : Assertion)
    (hcount : 0 < count) (hsize : 0 < repr.size)
    (ht : Triple (pointsToRange repr p values depth)
      (fun s (_ : Unit) s' => change s = some s') (fun _ => Q)) :
    Triple (pointsToRange repr p values depth)
      (fun s result s' => Heap.readRange repr p count s = some result ∧ change s = some s')
      (fun result h => result = values.toList ∧ Q h) := by
  intro h F s hp hd hm hi
  have hr := read_of_pointsToRange hcount hsize hp ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨⟨_, s₁, hc⟩, hpost⟩ := ht h F s hp hd hm hi
  refine ⟨⟨values.toList, s₁, hr, hc⟩, ?_⟩
  rintro result s₁ ⟨hv, hc⟩
  obtain ⟨h₁, hd₁, hm₁, hi₁, hq⟩ := hpost () s₁ hc
  exact ⟨h₁, hd₁, hm₁, hi₁, Option.some.inj (hv.symm.trans hr), hq⟩

end SepLogic

namespace HeapWP

open SepLogic

theorem readRange.spec (repr : Repr T) (p : RawPtr T) (values : Vector T count)
    (depth : Nat) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (SepLogic.pointsToRange repr p values depth) (RawPtr.readRange repr p count)
      (fun result h => result = values.toList ∧ SepLogic.pointsToRange repr p values depth h) := by
  apply Triple.checkedModify
  intro h F s hp hd hm hi
  have hr := SepLogic.read_of_pointsToRange hcount hsize hp
    ((Fragment.matches_union _ _ _).mp hm).1
  refine ⟨⟨values.toList, s, hr, rfl⟩, ?_⟩
  rintro result s' ⟨hv, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hv.symm.trans hr), hp⟩

theorem borrowRange.spec (repr : Repr T) (p : RawPtr T) (values : Vector T count)
    (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (pointsToRange repr p values) (RawPtr.borrowRange repr p count)
      (fun result h => result = values.toList ∧
        block repr p (List.replicate (count * repr.size) .borrowed) h) := by
  apply Triple.checkedModify
  apply SepLogic.readRange_transfer.spec repr p values 0 _ _ hcount hsize
  rintro h F s ⟨data, _, hp⟩ hd hm hi
  exact SepLogic.borrowRange_cells.spec repr p data hcount hsize h F s hp hd hm hi

theorem shareRange.spec (repr : Repr T) (p : RawPtr T) (values : Vector T count)
    (depth : Nat) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (pointsToRange repr p values depth) (RawPtr.shareRange repr p count)
      (fun result h => result = values.toList ∧ pointsToRange repr p values (depth + 1) h) := by
  apply Triple.checkedModify
  apply SepLogic.readRange_transfer.spec repr p values depth _ _ hcount hsize
  rintro h F s ⟨data, decoded, hp⟩ hd hm hi
  exact SepLogic.Triple.conseq (fun _ h => h) (fun _ _ h => ⟨data, decoded, h⟩)
    (SepLogic.shareRange_cells.spec repr p data depth hcount hsize) h F s hp hd hm hi

theorem endShareRange.spec (repr : Repr T) (p : RawPtr T) (values : Vector T count)
    (depth : Nat) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (pointsToRange repr p values (depth + 1)) (RawPtr.endShareRange repr p values.toList)
      (fun _ => pointsToRange repr p values depth) := by
  apply Triple.checkedModify
  intro h F s hp hd hm hi
  have hr := SepLogic.read_of_pointsToRange hcount hsize hp
    ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨data, decoded, hp⟩ := hp
  obtain ⟨⟨_, s₁, hc⟩, hpost⟩ := SepLogic.endShareRange_cells.spec repr p data depth hcount hsize
    h F s hp hd hm hi
  refine ⟨⟨(), s₁, ?_, ?_⟩, ?_⟩
  · simpa using hr
  · simpa using hc
  · rintro _ s' ⟨_, he⟩
    obtain ⟨h', hd', hm', hi', hq⟩ := hpost () s' (by simpa using he)
    exact ⟨h', hd', hm', hi', data, decoded, hq⟩

/-- An empty range cannot prove liveness from its empty byte footprint. -/
theorem readRange_empty.spec (repr : Repr T) (p : RawPtr T) (s : Heap) (blk : Block)
    (hl : s.allocations p.base = some blk)
    (ha : repr.align.val ∣ blk.alignment.val) (hp : repr.align.val ∣ p.byteOffset.val)
    (hb : p.byteOffset.val ≤ blk.repr.length) :
    Spec (RawPtr.readRange repr p 0) (fun result s' => result = [] ∧ s' = s) s := by
  apply Spec.checkedModify.mpr
  have hr : Heap.readRange repr p 0 s = some [] := by
    simp [Heap.readRange, hl, ha, hp, hb]
  refine ⟨⟨[], s, hr, rfl⟩, ?_⟩
  rintro result s' ⟨hv, rfl⟩
  exact ⟨Option.some.inj (hv.symm.trans hr), rfl⟩

end HeapWP
end Aeneas.Std
