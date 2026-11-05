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
  encode := fun _ bytes => ∀ i : Fin (count * repr.size),
    match bytes[i.val] with
    | .pointer _ lane => lane < pointerWidth
    | _ => True
  aligned := repr.aligned_stride count
  encode_complete := fun _ => ⟨Vector.replicate _ .uninit, by simp⟩
  encode_decode := fun _ _ _ => rfl
  decode_mono := fun _ _ _ decoded _ => decoded
  encode_valid := fun _ _ i encoded => encoded i

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
theorem block_append (repr : Repr T) (p q : RawPtr T) (bptr : BasePtr) (a b : List Cell)
    (hbase : q.provenance = p.provenance) (hoff : q.address.val = p.address.val + a.length)
    (hlen : repr.align.val ∣ a.length) (h : Fragment) :
    block repr p bptr (a ++ b) h ↔ sep (block repr p bptr a) (block repr q bptr b) h := by
  have offset (hlo : bptr.val ≤ p.address.val) :
      q.offsetFrom bptr = p.offsetFrom bptr + a.length := by
    simp only [RawPtr.offsetFrom]
    grind
  constructor
  · rintro ⟨hlo, hp, rfl⟩
    refine ⟨cellsHeap bptr p.provenance (p.offsetFrom bptr) a,
      cellsHeap bptr q.provenance (q.offsetFrom bptr) b, ?_, ?_, ⟨hlo, hp, rfl⟩, ?_⟩
    · simpa [hbase, offset hlo] using disjoint_cellsHeap_append bptr p.provenance (p.offsetFrom bptr) a b
    · simpa [hbase, offset hlo] using cellsHeap_append bptr p.provenance (p.offsetFrom bptr) a b
    · exact ⟨by grind, hoff ▸ Nat.dvd_add hp hlen, rfl⟩
  · rintro ⟨_, _, _, rfl, ⟨hlo, hp, rfl⟩, ⟨_, _, rfl⟩⟩
    exact ⟨hlo, hp, by simp only [hbase, offset hlo, cellsHeap_append]⟩

/-- A range owns one encoding for each exact value and the whole byte footprint. -/
def pointsToRange (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (values : Vector T count)
    (depth : Nat := 0) : Assertion :=
  fun h => ∃ data : Vector (Vector Byte repr.size) count,
    (∀ i : Fin count, repr.encode values[i.val] data[i.val]) ∧
    block repr p bptr (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList h

end SepLogic

/- Read-only exposure may retain symbolic pointer bytes with the same decoding,
   even when those bytes are not an admissible encoding for a scalar write. -/
def readableRange (repr : Repr T) (p : RawPtr T) (base : BasePtr)
    (values : Vector T count) (depth : Nat) : SepLogic.Assertion :=
  fun h => ∃ data : Vector (Vector Byte repr.size) count,
    (∀ i : Fin count, repr.decode data[i.val] = some values[i.val]) ∧
    SepLogic.block repr p base
      (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList h

theorem pointsToRange_readable {repr : Repr T} {p : RawPtr T}
    {base : BasePtr} {values : Vector T count} {depth : Nat} {h : SepLogic.Fragment}
    (hp : SepLogic.pointsToRange repr p base values depth h) :
    readableRange repr p base values depth h := by
  obtain ⟨data, encoded, rest⟩ := hp
  exact ⟨data, fun i => repr.encode_decode _ _ (encoded i), rest⟩

/-- Recover any element's cells from the selected contiguous region. -/
theorem Repr.select_region (repr : Repr T) (bytes : Vector Cell r)
    (start count : Nat) (data : Vector (Vector Cell repr.size) count)
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

theorem Repr.select_region_ext (repr : Repr T) (bytes : Vector Cell r)
    (start count : Nat) (data : Vector (Vector Cell repr.size) count)
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
        congrArg (fun xs : List Cell => xs[j]?)
          ((repr.region count).select_toList bytes start hb)
      _ = bytes.toList[start + j]? := by
        rw [List.getElem?_take_of_lt hj, List.getElem?_drop]
      _ = some data[j / repr.size][j % repr.size] := he.symm
      _ = _ := hflat.symm.trans (Vector.getElem?_toList (xs := data.flatMap id)).symm
  · simp [Repr.select_toList, Repr.region, hj]

theorem Repr.eq_update_of_select (repr : Repr T) (bytes result : Vector Cell r)
    (start : Nat) (hb : start + repr.size ≤ r) (data : Vector Cell repr.size)
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
theorem Repr.fold_region (repr : Repr T) (bytes : Vector Cell r)
    (start count : Nat) (old new : Vector (Vector Cell repr.size) count)
    (change : Vector Cell r → Nat → Option (Vector Cell r))
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

theorem modifyRange.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (old new : Vector (Vector Cell repr.size) count)
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (hcount : 0 < count) (hsize : 0 < repr.size)
    (hc : ∀ {r} (bytes : Vector Cell r) offset i (hi : i < count)
      (hb : offset + count * repr.size ≤ r),
      repr.select bytes (offset + i * repr.size) (range_element_bound hi hb) = old[i] →
      change bytes (offset + i * repr.size) = some (repr.update bytes (offset + i * repr.size)
        (range_element_bound hi hb) new[i]))
    (valid : ∀ s i (hi : i < count * repr.size),
      (match (old.flatMap id)[i] with
        | .borrowed => True | .shared _ byte => Heap.validByte s byte = true) →
      (match (new.flatMap id)[i] with
        | .borrowed => True | .shared _ byte => Heap.validByte s byte = true))
    (weaker : ∀ i (hi : i < count * repr.size),
      (old.flatMap id)[i].PermWeakens (new.flatMap id)[i]) :
    Triple (block repr p bptr (old.flatMap id).toList)
      (fun s (_ : Unit) s' => Heap.modifyRange repr p count change s = some s')
      (fun _ => block repr p bptr (new.flatMap id).toList) := by
  have ht := modify_weaken.spec (repr.region count) (p.cast Unit) bptr
    (old.flatMap id) (new.flatMap id)
    (fun bytes offset =>
      if (count = 0 ∨ 0 < repr.size) && offset + count * repr.size ≤ bytes.size then
        (List.range count).foldlM (fun current i => change current (offset + i * repr.size)) bytes
      else none)
    (Nat.mul_pos hcount hsize) (by
      intro r bytes offset hb hs
      change offset + count * repr.size ≤ r at hb
      simp only [hsize, or_true, decide_true, Bool.true_and, Vector.size, hb, ↓reduceIte]
      exact repr.fold_region bytes offset count old new
        (fun current i => change current (offset + i * repr.size)) hb hs
        (fun current i hi hs => hc current offset i hi hb hs) hsize) valid weaker
  exact ht

theorem borrowRange_cells.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (data : Vector (Vector Byte repr.size) count) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (block repr p bptr (data.flatMap (fun bytes => bytes.map (Cell.shared 0))).toList)
      (fun s (_ : Unit) s' => Heap.borrowRange repr p count s = some s')
      (fun _ => block repr p bptr (List.replicate (count * repr.size) .borrowed)) := by
  let old := data.map fun bytes => bytes.map (Cell.shared 0)
  let new : Vector (Vector Cell repr.size) count :=
    Vector.replicate count (Vector.replicate repr.size .borrowed)
  have ht := modifyRange.spec repr p bptr old new
    (fun bytes offset => repr.borrow bytes offset) hcount hsize (by
      intro r bytes offset i hi hb hs
      simp only [Repr.borrow, hsize, range_element_bound hi hb, and_self, ↓reduceDIte, hs]
      simp [old, new, Function.comp_def, Cell.borrow, vector_mapM_some]
      apply congrArg (repr.update bytes _ _)
      apply Vector.ext
      intro j hj
      simp)
    (by intro s i hi _; simp [new, Vector.flatMap_replicate])
    (by intro i hi; simpa [new, Vector.flatMap_replicate] using
          Cell.PermWeakens.borrow ((old.flatMap id)[i]))
  simpa [old, new, Vector.flatMap_map, Vector.flatMap_replicate, Heap.borrowRange] using ht

theorem shareRange_cells.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (data : Vector (Vector Byte repr.size) count) (depth : Nat)
    (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (block repr p bptr (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList)
      (fun s (_ : Unit) s' => Heap.shareRange repr p count s = some s')
      (fun _ => block repr p bptr
        (data.flatMap (fun bytes => bytes.map (Cell.shared (depth + 1)))).toList) := by
  have ht := modifyRange.spec repr p bptr
    (data.map fun bytes => bytes.map (Cell.shared depth))
    (data.map fun bytes => bytes.map (Cell.shared (depth + 1)))
    (fun bytes offset => repr.share bytes offset) hcount hsize (by
      intro r bytes offset i hi hb hs
      simp [Repr.share, hsize, range_element_bound hi hb, hs, Function.comp_def,
        Cell.share, vector_mapM_some])
    (by intro s i hi hv; simpa [Vector.getElem_flatMap, Vector.getElem_map] using hv)
    (by intro i hi; simp only [Vector.getElem_flatMap, Vector.getElem_map, id_eq]
        exact Cell.PermWeakens.share _ _)
  simpa [Vector.flatMap_map, Heap.shareRange] using ht

/-- Decrements that retain positive sharing permission cannot introduce a writer.
Returning the last shared permission instead requires continuation authority. -/
theorem endShareRange_cells.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (data : Vector (Vector Byte repr.size) count) (depth : Nat) (positive : 0 < depth)
    (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (block repr p bptr
      (data.flatMap (fun bytes => bytes.map (Cell.shared (depth + 1)))).toList)
      (fun s (_ : Unit) s' => Heap.endShareRange repr p count s = some s')
      (fun _ => block repr p bptr
        (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList) := by
  have ht := modifyRange.spec repr p bptr
    (data.map fun bytes => bytes.map (Cell.shared (depth + 1)))
    (data.map fun bytes => bytes.map (Cell.shared depth))
    (fun bytes offset => repr.endShare bytes offset) hcount hsize (by
      intro r bytes offset i hi hb hs
      simp [Repr.endShare, hsize, range_element_bound hi hb, hs, Function.comp_def,
        Cell.endShare, vector_mapM_some])
    (by intro s i hi hv; simpa [Vector.getElem_flatMap, Vector.getElem_map] using hv)
    (by
      intro i hi
      simp only [Vector.getElem_flatMap, Vector.getElem_map, id_eq]
      intro other compatible
      cases other
      · simpa [Cell.compatible, positive] using compatible
      · rfl)
  simpa [Vector.flatMap_map, Heap.endShareRange] using ht

theorem read_of_readableRange {s : Heap} {repr : Repr T} {p : RawPtr T} {bptr : BasePtr}
    {values : Vector T count} {depth : Nat} {h : Fragment}
    (hcount : 0 < count) (hsize : 0 < repr.size)
    (hp : readableRange repr p bptr values depth h) (hm : Fragment.Matches s h) :
    Heap.readRange repr p count s = some values.toList := by
  obtain ⟨data, encoded, hlo, hpa, rfl⟩ := hp
  let grouped := repr.region count
  let q : RawPtr Unit := p.cast Unit
  have hpositive : 0 < grouped.size := Nat.mul_pos hcount hsize
  obtain ⟨blk, hb, hl, hlive, ha, hs⟩ := bytes_of_matches (repr := grouped) (p := q)
    (data := data.flatMap (fun bytes => bytes.map (Cell.shared depth))) hpositive hm
  change p.offsetFrom bptr + count * repr.size ≤ blk.repr.length at hb
  change s.allocations p.provenance = some blk at hl
  have hr (i : Nat) (hi : i < count) :
      repr.read blk.bytes (p.offsetFrom bptr + i * repr.size) = some values[i] := by
    have hsel := repr.select_region blk.bytes (p.offsetFrom bptr) count
      (data.map fun bytes => bytes.map (Cell.shared depth)) hb
      (by simpa [Vector.flatMap_map, grouped, q, RawPtr.cast, RawPtr.offsetFrom] using hs) i hi
    simp only [Vector.getElem_map] at hsel
    simp [Repr.read, hsize, range_element_bound hi hb, hsel,
      Repr.readBytes_shared, encoded ⟨i, hi⟩]
  have hmap : (List.range count).mapM
      (fun i => repr.read blk.bytes (p.offsetFrom bptr + i * repr.size)) =
        some values.toList := by
    simpa [List.range_eq_range'] using mapM_range'_some values.toList 0
      (fun i hi => by simpa using hr i (by simpa using hi))
  have bound : p.address.val + count * repr.size ≤ bptr.val + blk.repr.length := by
    simp only [RawPtr.offsetFrom] at hb
    grind
  simpa [Heap.readRange, hl, hlive, hpa, hsize, bound, ha, hlo] using hmap

theorem read_of_pointsToRange {s : Heap} {repr : Repr T} {p : RawPtr T} {bptr : BasePtr}
    {values : Vector T count} {depth : Nat} {h : Fragment}
    (hcount : 0 < count) (hsize : 0 < repr.size)
    (hp : pointsToRange repr p bptr values depth h) (hm : Fragment.Matches s h) :
    Heap.readRange repr p count s = some values.toList :=
  read_of_readableRange hcount hsize (pointsToRange_readable hp) hm

theorem readRange_transfer.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (depth : Nat) (change : Heap → Option Heap) (Q : Assertion)
    (hcount : 0 < count) (hsize : 0 < repr.size)
    (ht : Triple (pointsToRange repr p bptr values depth)
      (fun s (_ : Unit) s' => change s = some s') (fun _ => Q)) :
    Triple (pointsToRange repr p bptr values depth)
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

theorem readRange.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (values : Vector T count)
    (depth : Nat) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (SepLogic.pointsToRange repr p bptr values depth) (RawPtr.readRange repr p count)
      (fun result h => result = values.toList ∧ SepLogic.pointsToRange repr p bptr values depth h) := by
  apply Triple.checkedModify
  intro h F s hp hd hm hi
  have hr := SepLogic.read_of_pointsToRange hcount hsize hp
    ((Fragment.matches_union _ _ _).mp hm).1
  refine ⟨⟨values.toList, s, hr, rfl⟩, ?_⟩
  rintro result s' ⟨hv, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hv.symm.trans hr), hp⟩

theorem borrowRange.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (values : Vector T count)
    (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (pointsToRange repr p bptr values) (RawPtr.borrowRange repr p count)
      (fun result h => result = values.toList ∧
        block repr p bptr (List.replicate (count * repr.size) .borrowed) h) := by
  apply Triple.checkedModify
  intro h F s hp hd hm hinv
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  have hr := SepLogic.read_of_pointsToRange hcount hsize hp localMatch
  obtain ⟨data, encoded, hlo, ha, rfl⟩ := hp
  obtain ⟨blk, hb, hl, _, hbase, selected⟩ :=
    bytes_of_matches (repr := repr.region count) (p := p.cast Unit)
      (data := data.flatMap (fun bytes => bytes.map (Cell.shared 0)))
      (Nat.mul_pos hcount hsize) localMatch
  have mutable : State.mutableValues repr p values.toList s := by
    refine ⟨blk, hl, ?_⟩
    intro i hi
    have hic : i < count := by simpa using hi
    have hb' : p.offsetFrom blk.bptr + count * repr.size ≤ blk.repr.length := by
      simpa [hbase, RawPtr.cast, RawPtr.offsetFrom, Repr.region] using hb
    have hs := repr.select_region blk.bytes (p.offsetFrom blk.bptr) count
      (data.map fun bytes => bytes.map (Cell.shared 0)) hb'
      (by simpa [hbase, RawPtr.cast, RawPtr.offsetFrom, Vector.flatMap_map] using selected) i hic
    refine ⟨data[i], range_element_bound hic hb', ?_, ?_⟩
    · simpa only [Vector.getElem_map, hs] using Repr.readBytes_shared data[i] 0
    · simpa using encoded ⟨i, hic⟩
  obtain ⟨⟨_, s', hb'⟩, post⟩ :=
    SepLogic.borrowRange_cells.spec repr p bptr data hcount hsize _ F s ⟨hlo, ha, rfl⟩ hd hm hinv
  refine ⟨⟨values.toList, s', hr, mutable, hb'⟩, ?_⟩
  rintro result s' ⟨hv, _, he⟩
  obtain ⟨h', hd', hm', hi', hq⟩ := post () s' he
  exact ⟨h', hd', hm', hi', Option.some.inj (hv.symm.trans hr), hq⟩

theorem shareRange.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (values : Vector T count)
    (depth : Nat) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (pointsToRange repr p bptr values depth) (RawPtr.shareRange repr p count)
      (fun result h => result = values.toList ∧ pointsToRange repr p bptr values (depth + 1) h) := by
  apply Triple.checkedModify
  apply SepLogic.readRange_transfer.spec repr p bptr values depth _ _ hcount hsize
  rintro h F s ⟨data, decoded, hp⟩ hd hm hi
  exact SepLogic.Triple.conseq (fun _ h => h) (fun _ _ h => ⟨data, decoded, h⟩)
    (SepLogic.shareRange_cells.spec repr p bptr data depth hcount hsize) h F s hp hd hm hi

theorem endShareRange.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr) (values : Vector T count)
    (depth : Nat) (positive : 0 < depth) (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (pointsToRange repr p bptr values (depth + 1)) (RawPtr.endShareRange repr p values.toList)
      (fun _ => pointsToRange repr p bptr values depth) := by
  apply Triple.checkedModify
  intro h F s hp hd hm hi
  have hr := SepLogic.read_of_pointsToRange hcount hsize hp
    ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨data, decoded, hp⟩ := hp
  obtain ⟨⟨_, s₁, hc⟩, hpost⟩ := SepLogic.endShareRange_cells.spec repr p bptr data depth positive hcount hsize
    h F s hp hd hm hi
  refine ⟨⟨(), s₁, ?_, ?_⟩, ?_⟩
  · simpa using hr
  · simpa using hc
  · rintro _ s' ⟨_, he⟩
    obtain ⟨h', hd', hm', hi', hq⟩ := hpost () s' (by simpa using he)
    exact ⟨h', hd', hm', hi', data, decoded, hq⟩

/-- An empty range cannot prove liveness from its empty byte footprint. -/
theorem readRange_empty.spec (repr : Repr T) (p : RawPtr T) (s : Heap) (blk : Block)
    (hl : s.allocations p.provenance = some blk)
    (hlive : s.live blk = true)
    (hlo : blk.bptr.val ≤ p.address.val) (hp : repr.align.val ∣ p.address.val)
    (hb : p.address.val ≤ blk.bptr.val + blk.repr.length) :
    Spec (RawPtr.readRange repr p 0) (fun result s' => result = [] ∧ s' = s) s := by
  apply Spec.checkedModify.mpr
  have hr : Heap.readRange repr p 0 s = some [] := by
    simp [Heap.readRange, hl, hlive, hlo, hp, hb]
  refine ⟨⟨[], s, hr, rfl⟩, ?_⟩
  rintro result s' ⟨hv, rfl⟩
  exact ⟨Option.some.inj (hv.symm.trans hr), rfl⟩

end HeapWP
end Aeneas.Std
