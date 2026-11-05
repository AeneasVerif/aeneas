module

public import Aeneas.Std.Heap.Ranges
public import Aeneas.Std.Heap.EffectSpecs
import all Aeneas.Std.Heap.Ranges
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap.Separation

/-! Range returns require the matching backward continuation's authority.
Borrowed cells alone do not exclude conflicting observers in other views. -/

@[expose] public section

namespace Aeneas.Std.Heap

theorem storeRepr_same (s : Heap) (base : Nat) (blk : Block)
    (hl : s.allocations base = some blk) : s.storeRepr base blk.repr = s := by
  rcases s with ⟨allocations, next⟩
  change allocations base = some blk at hl
  apply congrArg (fun a => Heap.mk a next)
  funext other
  by_cases he : other = base
  · subst other
    simp [update, hl]
  · simp [update, he]

theorem storeRepr_storeRepr (s : Heap) (base : Nat) (old new : List Cell) :
    (s.storeRepr base old).storeRepr base new = s.storeRepr base new := by
  rcases s with ⟨allocations, next⟩
  apply congrArg (fun a => Heap.mk a next)
  funext other
  by_cases he : other = base
  · subst other
    simp [storeRepr, update, Option.map_map, Function.comp_def]
  · simp [storeRepr, update, he]

theorem modifyRange_empty (repr : Repr T) (p : RawPtr T) (s : Heap) (blk : Block)
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (hinv : s.Inv) (hl : s.allocations p.provenance = some blk) (live : s.live blk = true)
    (lower : blk.bptr.val ≤ p.address.val) (aligned : repr.align.val ∣ p.address.val)
    (bound : p.address.val ≤ blk.bptr.val + blk.repr.length) :
    Heap.modifyRange repr p 0 change s = some s := by
  have hb : p.offsetFrom blk.bptr ≤ blk.repr.length := by
    dsimp [RawPtr.offsetFrom]
    grind
  simp [Heap.modifyRange, Heap.modify, hl, live, lower, aligned, hb, Block.bytes,
    storeRepr_same s p.provenance blk hl, Heap.commit, hinv.2]

end Aeneas.Std.Heap

namespace Aeneas.Std

private theorem update_update (repr : Repr T) (bytes : Vector Cell r)
    (offset : Nat) (hb : offset + repr.size ≤ r)
    (old new : Vector Cell repr.size) :
    repr.update (repr.update bytes offset hb old) offset hb new =
      repr.update bytes offset hb new := by
  apply Vector.toList_inj.mp
  apply List.ext_getElem?
  intro i
  by_cases inside : offset ≤ i ∧ i < offset + repr.size
  · obtain ⟨j, hj, rfl⟩ : ∃ j, j < repr.size ∧ i = offset + j :=
      ⟨i - offset, by grind, by grind⟩
    rw [Repr.update_inside _ _ _ _ _ j hj, Repr.update_inside _ _ _ _ _ j hj]
  · have outside : i < offset ∨ offset + repr.size ≤ i := by grind
    rw [Repr.update_outside _ _ _ _ _ i outside,
      Repr.update_outside _ _ _ _ _ i outside,
      Repr.update_outside _ _ _ _ _ i outside]

private theorem update_select (repr : Repr T) (bytes : Vector Cell r)
    (offset : Nat) (hb : offset + repr.size ≤ r) :
    repr.update bytes offset hb (repr.select bytes offset hb) = bytes := by
  apply Vector.toList_inj.mp
  apply List.ext_getElem?
  intro i
  by_cases inside : offset ≤ i ∧ i < offset + repr.size
  · have hj : i - offset < repr.size := by agrind
    have he : i = offset + (i - offset) := by agrind
    rw [he, Repr.update_inside _ _ _ _ _ _ hj]
    simp [Repr.select, show offset + (i - offset) < r by agrind]
  · exact Repr.update_outside repr bytes offset hb _ i (by agrind)

private theorem endShare_after_share (repr : Repr T) (p : RawPtr T)
    (s₀ s₁ : Heap) (blk : Block) (old : Vector Byte repr.size) (depth : Nat)
    (hsize : 0 < repr.size) (hb : p.offsetFrom blk.bptr + repr.size ≤ blk.repr.length)
    (hl : s₀.allocations p.provenance = some blk) (live : s₀.live blk = true)
    (lower : blk.bptr.val ≤ p.address.val) (aligned : repr.align.val ∣ p.address.val)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb = old.map (Cell.shared depth))
    (hinv : s₀.Inv) (shared : Heap.share repr p s₀ = some s₁) :
    Heap.endShare repr p s₁ = some s₀ := by
  let suspended := repr.update blk.bytes (p.offsetFrom blk.bptr) hb
    (old.map (Cell.shared (depth + 1)))
  have change : repr.share blk.bytes (p.offsetFrom blk.bptr) = some suspended := by
    simp [Repr.share, hsize, hb, selected, Vector.mapM_map, Function.comp_def,
      Cell.share, vector_mapM_some, suspended]
  have commit : Heap.commit (s₀.storeRepr p.provenance suspended.toList) = some s₁ := by
    simpa [Heap.share, Heap.modify, hl, live, lower, aligned, change] using shared
  obtain ⟨state, _⟩ := Heap.commit_success _ _ commit
  subst s₁
  have hb₁ : p.offsetFrom blk.bptr + repr.size ≤ suspended.toList.length := by simpa using hb
  have bytes : ({ blk with repr := suspended.toList } : Block).bytes =
      suspended.cast (by simp) := by
    apply Vector.toArray_inj.mp
    simp [Block.bytes, Vector.toList, Array.toArray_toList]
  have selected₁ :
      repr.select ({ blk with repr := suspended.toList } : Block).bytes
        (p.offsetFrom blk.bptr) hb₁ = old.map (Cell.shared (depth + 1)) := by
    apply Vector.toList_inj.mp
    simpa only [Repr.select_toList, bytes, Vector.toList_cast] using
      congrArg Vector.toList (Repr.select_update repr blk.bytes (p.offsetFrom blk.bptr) hb
        (old.map (Cell.shared (depth + 1))))
  have updated :
      (repr.update ({ blk with repr := suspended.toList } : Block).bytes
        (p.offsetFrom blk.bptr) hb₁ (old.map (Cell.shared depth))).toList = blk.repr := by
    have identity : repr.update blk.bytes (p.offsetFrom blk.bptr) hb
        (old.map (Cell.shared depth)) = blk.bytes := by
      rw [← selected, update_select]
    have same := (update_update repr blk.bytes (p.offsetFrom blk.bptr) hb
      (old.map (Cell.shared (depth + 1))) (old.map (Cell.shared depth))).trans identity
    have list : blk.bytes.toList = blk.repr := by simp [Block.bytes]
    simpa only [bytes, Vector.toList_cast, suspended, Repr.update_toList, list] using
      congrArg Vector.toList same
  simp [Heap.endShare, Heap.modify, hl, live, lower, aligned,
    Heap.live_storeRepr_updated, Repr.endShare, hsize, hb, selected₁,
    Vector.mapM_map, Function.comp_def, Cell.endShare, vector_mapM_some, updated,
    Heap.storeRepr_storeRepr, Heap.storeRepr_same s₀ p.provenance blk hl,
    Heap.commit, hinv.2]

private theorem endBorrow_after_borrow (repr : Repr T) (p : RawPtr T)
    (s₀ s₁ : Heap) (blk : Block) (old : Vector Byte repr.size)
    (value : T) (data : Vector Byte repr.size) (encoded : repr.encode value data)
    (hsize : 0 < repr.size) (hb : p.offsetFrom blk.bptr + repr.size ≤ blk.repr.length)
    (hl : s₀.allocations p.provenance = some blk) (live : s₀.live blk = true)
    (lower : blk.bptr.val ≤ p.address.val) (aligned : repr.align.val ∣ p.address.val)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb = old.map (Cell.shared 0))
    (borrowed : Heap.borrow repr p s₀ = some s₁) :
    Heap.endBorrow repr p data s₁ = Heap.write repr p value data encoded s₀ := by
  let suspended := repr.update blk.bytes (p.offsetFrom blk.bptr) hb
    (Vector.replicate repr.size .borrowed)
  have change : repr.borrow blk.bytes (p.offsetFrom blk.bptr) = some suspended := by
    have same : old.map (fun _ => Cell.borrowed) =
        Vector.replicate repr.size Cell.borrowed := by
      apply Vector.ext
      intro i hi
      simp
    simp [Repr.borrow, hsize, hb, selected, Vector.mapM_map, Function.comp_def,
      Cell.borrow, vector_mapM_some, same, suspended]
  have commit : Heap.commit (s₀.storeRepr p.provenance suspended.toList) = some s₁ := by
    simpa [Heap.borrow, Heap.modify, hl, live, lower, aligned, change] using borrowed
  obtain ⟨state, _⟩ := Heap.commit_success _ _ commit
  subst s₁
  have hb₁ : p.offsetFrom blk.bptr + repr.size ≤ suspended.toList.length := by
    simpa using hb
  have bytes : ({ blk with repr := suspended.toList } : Block).bytes =
      suspended.cast (by simp) := by
    apply Vector.toArray_inj.mp
    simp [Block.bytes, Vector.toList, Array.toArray_toList]
  have selected₁ :
      repr.select ({ blk with repr := suspended.toList } : Block).bytes
        (p.offsetFrom blk.bptr) hb₁ = Vector.replicate repr.size .borrowed := by
    apply Vector.toList_inj.mp
    simpa only [Repr.select_toList, bytes, Vector.toList_cast] using
      congrArg Vector.toList (Repr.select_update repr blk.bytes (p.offsetFrom blk.bptr) hb
        (Vector.replicate repr.size .borrowed))
  have zipped : (Vector.replicate repr.size (Cell.borrowed : Cell)).zip data =
      data.map (fun byte => (Cell.borrowed, byte)) := by
    apply Vector.ext
    intro i hi
    simp
  have updated :
      (repr.update ({ blk with repr := suspended.toList } : Block).bytes
        (p.offsetFrom blk.bptr) hb₁ (data.map (Cell.shared 0))).toList =
      (repr.update blk.bytes (p.offsetFrom blk.bptr) hb (data.map (Cell.shared 0))).toList := by
    simpa only [bytes, Vector.toList_cast, suspended, Repr.update_toList] using
      congrArg Vector.toList
      (update_update repr blk.bytes (p.offsetFrom blk.bptr) hb
        (Vector.replicate repr.size .borrowed) (data.map (Cell.shared 0)))
  simp [Heap.endBorrow, Heap.write, Heap.modify, hl, live, lower, aligned,
    Heap.live_storeRepr_updated, Repr.endBorrow, Repr.write, hsize, hb,
    selected, selected₁, zipped, Vector.mapM_map, Function.comp_def, Cell.endBorrow,
    vector_mapM_some, Repr.writeBytes_shared, updated, Heap.storeRepr_storeRepr]

/-- On a uniformly shared range, changing each element's depth is the same
    update as changing the depth of its complete byte region. -/
private theorem sharedRange_change (repr : Repr T)
    (data : Vector (Vector Byte repr.size) count) (bytes : Vector Cell r)
    (offset depth nextDepth : Nat) (hb : offset + count * repr.size ≤ r)
    (selected : (repr.region count).select bytes offset hb =
      data.flatMap (fun encoding => encoding.map (Cell.shared depth)))
    (change : Cell → Option Cell)
    (cellChange : ∀ byte, change (.shared depth byte) = some (.shared nextDepth byte))
    (positive : 0 < repr.size) :
    (List.range count).foldlM (fun current i =>
      let start := offset + i * repr.size
      if h : 0 < repr.size ∧ start + repr.size ≤ r then
        ((repr.select current start h.2).mapM change).map (repr.update current start h.2)
      else none) bytes =
    some ((repr.region count).update bytes offset hb
      (data.flatMap (fun encoding => encoding.map (Cell.shared nextDepth)))) := by
  let old := data.map fun encoding => encoding.map (Cell.shared depth)
  let new := data.map fun encoding => encoding.map (Cell.shared nextDepth)
  have step : ∀ current i (hi : i < count),
      repr.select current (offset + i * repr.size) (range_element_bound hi hb) = old[i] →
      (if h : 0 < repr.size ∧ offset + i * repr.size + repr.size ≤ r then
        ((repr.select current (offset + i * repr.size) h.2).mapM change).map
          (repr.update current (offset + i * repr.size) h.2)
      else none) = some (repr.update current (offset + i * repr.size)
        (range_element_bound hi hb) new[i]) := by
    intro current i hi hs
    simp [positive, range_element_bound hi hb, hs, old, new,
      Vector.mapM_map, Function.comp_def, cellChange, vector_mapM_some]
  simpa only [new, Vector.flatMap_map, Function.comp_def, id_eq] using
    repr.fold_region bytes offset count old new _ hb
      (by simpa only [old, Vector.flatMap_map, Function.comp_def, id_eq] using selected)
      step positive

private theorem sharedRange_as_region (repr : Repr T) (p : RawPtr T)
    (data : Vector (Vector Byte repr.size) count) (depth nextDepth : Nat)
    (s : Heap) (blk : Block) (hc : 0 < count) (positive : 0 < repr.size)
    (hb : p.offsetFrom blk.bptr + count * repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (live : s.live blk = true)
    (lower : blk.bptr.val ≤ p.address.val) (aligned : repr.align.val ∣ p.address.val)
    (selected : (repr.region count).select blk.bytes (p.offsetFrom blk.bptr) hb =
      data.flatMap (fun encoding => encoding.map (Cell.shared depth)))
    (change : Cell → Option Cell)
    (cellChange : ∀ byte, change (.shared depth byte) = some (.shared nextDepth byte)) :
    Heap.modifyRange repr p count (fun bytes start =>
      if h : 0 < repr.size ∧ start + repr.size ≤ bytes.size then
        ((repr.select bytes start h.2).mapM change).map (repr.update bytes start h.2)
      else none) s =
    Heap.modify (repr.region count) (p.cast Unit) (fun bytes start =>
      if h : 0 < (repr.region count).size ∧ start + (repr.region count).size ≤ bytes.size then
        (((repr.region count).select bytes start h.2).mapM change).map
          ((repr.region count).update bytes start h.2)
      else none) s := by
  have folded := sharedRange_change repr data blk.bytes (p.offsetFrom blk.bptr)
    depth nextDepth hb selected change cellChange positive
  have whole : (data.flatMap (fun encoding => encoding.map (Cell.shared depth))).mapM change =
      some (data.flatMap (fun encoding => encoding.map (Cell.shared nextDepth))) := by
    have same (d : Nat) : data.flatMap (fun encoding => encoding.map (Cell.shared d)) =
        (data.flatMap id).map (Cell.shared d) := by
      apply Vector.ext
      intro i hi
      simp [Vector.getElem_flatMap]
    rw [same depth, same nextDepth, Vector.mapM_map]
    simp only [Function.comp_def, cellChange]
    rw [vector_mapM_some]
  have whole' : ((repr.region count).select blk.bytes (p.offsetFrom blk.bptr) hb).mapM change =
      some (data.flatMap (fun encoding => encoding.map (Cell.shared nextDepth))) := by
    rw [selected]
    exact whole
  have size : (repr.region count).size = count * repr.size := rfl
  have align : (repr.region count).align = repr.align := rfl
  simp only [Heap.modifyRange, Heap.modify, RawPtr.cast, hl, Bind.bind, Option.bind,
    live, lower, aligned, align, decide_true, Bool.true_and, ↓reduceIte, Vector.size, size]
  simp only [positive, or_true, hb, decide_true, Bool.true_and, ↓reduceIte] at folded ⊢
  simp only [RawPtr.offsetFrom] at hb folded whole' ⊢
  simp only [size, hb, Nat.mul_pos hc positive, and_self, ↓reduceDIte]
  rw [folded]
  rw [whole']
  rfl

private theorem zipIdx_vector [Inhabited α] (data : Vector α count) :
    data.toList.zipIdx = (List.range count).map (fun i => (data[i]!, i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    have bound : i < count := by simpa using hi
    simp [bound]

private theorem endBorrowRange_update (repr : Repr T)
    (data : Vector (Vector Byte repr.size) count) (bytes : Vector Cell r)
    (offset : Nat) (hb : offset + count * repr.size ≤ r)
    (selected : (repr.region count).select bytes offset hb =
      Vector.replicate (count * repr.size) .borrowed)
    (hsize : 0 < repr.size) :
    data.toList.zipIdx.foldlM (fun current (encoding, i) =>
      repr.endBorrow current (offset + i * repr.size) encoding) bytes =
      some ((repr.region count).update bytes offset hb
        (data.flatMap (fun encoding => encoding.map (Cell.shared 0)))) := by
  rw [zipIdx_vector, List.foldlM_map]
  let old : Vector (Vector Cell repr.size) count :=
    Vector.replicate count (Vector.replicate repr.size .borrowed)
  let new := data.map fun encoding => encoding.map (Cell.shared 0)
  have step : ∀ current i (hi : i < count),
      repr.select current (offset + i * repr.size) (range_element_bound hi hb) = old[i] →
      repr.endBorrow current (offset + i * repr.size) data[i]! =
        some (repr.update current (offset + i * repr.size) (range_element_bound hi hb) new[i]) := by
    intro current i hi hs
    have hz : (Vector.replicate repr.size (Cell.borrowed : Cell)).zip data[i] =
        data[i].map (fun byte => (Cell.borrowed, byte)) := by
      apply Vector.ext
      intro j hj
      simp
    simp [Repr.endBorrow, hsize, range_element_bound hi hb, hs, old, hz, new, hi,
      Vector.mapM_map, Function.comp_def, Cell.endBorrow, vector_mapM_some]
  simpa only [new, Vector.flatMap_map, Function.comp_def, id_eq] using
    repr.fold_region bytes offset count old new
      (fun current i => repr.endBorrow current (offset + i * repr.size) data[i]!) hb
      (by simpa [old, Vector.flatMap_replicate] using selected) step hsize

private theorem borrowRange_update (repr : Repr T)
    (data : Vector (Vector Byte repr.size) count) (bytes : Vector Cell r)
    (offset : Nat) (hb : offset + count * repr.size ≤ r)
    (selected : (repr.region count).select bytes offset hb =
      data.flatMap (fun encoding => encoding.map (Cell.shared 0)))
    (hsize : 0 < repr.size) :
    (List.range count).foldlM (fun current i => repr.borrow current (offset + i * repr.size)) bytes =
      some ((repr.region count).update bytes offset hb
        (Vector.replicate (count * repr.size) .borrowed)) := by
  let old := data.map fun encoding => encoding.map (Cell.shared 0)
  let new : Vector (Vector Cell repr.size) count :=
    Vector.replicate count (Vector.replicate repr.size .borrowed)
  have step : ∀ current i (hi : i < count),
      repr.select current (offset + i * repr.size) (range_element_bound hi hb) = old[i] →
      repr.borrow current (offset + i * repr.size) =
        some (repr.update current (offset + i * repr.size) (range_element_bound hi hb) new[i]) := by
    intro current i hi hs
    simp [Repr.borrow, hsize, range_element_bound hi hb, hs, old, new,
      Vector.mapM_map, Function.comp_def, Cell.borrow, vector_mapM_some]
    apply congrArg (repr.update current _ _)
    apply Vector.ext
    intro j hj
    simp
  simpa [new, Vector.flatMap_replicate] using
    repr.fold_region bytes offset count old new
      (fun current i => repr.borrow current (offset + i * repr.size)) hb
      (by simpa only [old, Vector.flatMap_map, Function.comp_def, id_eq] using selected) step hsize

private theorem endBorrowRange_after_borrowRange (repr : Repr T) (p : RawPtr T)
    (s₀ s₁ : Heap) (blk : Block) (old data : Vector (Vector Byte repr.size) count)
    (hsize : 0 < repr.size) (hb : p.offsetFrom blk.bptr + count * repr.size ≤ blk.repr.length)
    (hl : s₀.allocations p.provenance = some blk) (live : s₀.live blk = true)
    (lower : blk.bptr.val ≤ p.address.val) (aligned : repr.align.val ∣ p.address.val)
    (selected : (repr.region count).select blk.bytes (p.offsetFrom blk.bptr) hb =
      old.flatMap (fun encoding => encoding.map (Cell.shared 0)))
    (borrowed : Heap.borrowRange repr p count s₀ = some s₁) :
    Heap.endBorrowRange repr p data.toList s₁ =
      Heap.commit (s₀.storeRepr p.provenance
        ((repr.region count).update blk.bytes (p.offsetFrom blk.bptr) hb
          (data.flatMap (fun encoding => encoding.map (Cell.shared 0)))).toList) := by
  let suspended := (repr.region count).update blk.bytes (p.offsetFrom blk.bptr) hb
    (Vector.replicate (count * repr.size) .borrowed)
  have commit : Heap.commit (s₀.storeRepr p.provenance suspended.toList) = some s₁ := by
    simpa [Heap.borrowRange, Heap.modifyRange, Heap.modify, hl, live, lower, aligned,
      hsize, hb, borrowRange_update repr old blk.bytes _ hb selected hsize, suspended] using borrowed
  obtain ⟨state, _⟩ := Heap.commit_success _ _ commit
  subst s₁
  have hb₁ : p.offsetFrom blk.bptr + count * repr.size ≤ suspended.toList.length := by simpa using hb
  have bytes : ({ blk with repr := suspended.toList } : Block).bytes =
      suspended.cast (by simp) := by
    apply Vector.toArray_inj.mp
    simp [Block.bytes, Vector.toList, Array.toArray_toList]
  have selected₁ :
      (repr.region count).select ({ blk with repr := suspended.toList } : Block).bytes
        (p.offsetFrom blk.bptr) hb₁ = Vector.replicate (count * repr.size) .borrowed := by
    apply Vector.toList_inj.mp
    simpa only [Repr.select, Vector.toList_cast, Vector.toList_extract, bytes, suspended] using
      congrArg Vector.toList (Repr.select_update (repr.region count) blk.bytes
        (p.offsetFrom blk.bptr) hb (Vector.replicate (count * repr.size) .borrowed))
  have updated :
      ((repr.region count).update ({ blk with repr := suspended.toList } : Block).bytes
        (p.offsetFrom blk.bptr) hb₁
        (data.flatMap (fun encoding => encoding.map (Cell.shared 0)))).toList =
      ((repr.region count).update blk.bytes (p.offsetFrom blk.bptr) hb
        (data.flatMap (fun encoding => encoding.map (Cell.shared 0)))).toList := by
    rw [bytes, Repr.update_toList (repr.region count) (suspended.cast (by simp))
      (p.offsetFrom blk.bptr) hb₁ (data.flatMap (fun encoding => encoding.map (Cell.shared 0)))]
    rw [Vector.toList_cast (xs := suspended) (by simp)]
    simpa only [suspended, Repr.region, Repr.update_toList,
      Vector.toList_cast] using
      congrArg Vector.toList
        (update_update (repr.region count) blk.bytes (p.offsetFrom blk.bptr) hb
          (Vector.replicate (count * repr.size) .borrowed)
          (data.flatMap (fun encoding => encoding.map (Cell.shared 0))))
  simp [Heap.endBorrowRange, Heap.modify, hl, live, lower, aligned,
    Heap.live_storeRepr_updated, hsize, hb,
    endBorrowRange_update repr data _ _ hb₁ selected₁ hsize, updated,
    Heap.storeRepr_storeRepr]

private theorem encodeList_length (repr : Repr T) (values : List T)
    (data : List (Vector Byte repr.size)) (encoded : repr.encodeList values data) :
    data.length = values.length := by
  induction values generalizing data
  · cases data
    · rfl
    · contradiction
  · rename_i value values ih
    cases data
    · contradiction
    · rename_i bytes data
      exact congrArg Nat.succ (ih data encoded.2)

private theorem encodeList_get (repr : Repr T) (values : List T)
    (data : List (Vector Byte repr.size)) (encoded : repr.encodeList values data)
    (i : Nat) (hv : i < values.length) (hd : i < data.length) :
    repr.encode values[i] data[i] := by
  induction values generalizing data i
  · simp at hv
  · rename_i value values ih
    cases data
    · contradiction
    · rename_i bytes data
      cases i
      · exact encoded.1
      · rename_i i
        exact ih data encoded.2 i (by simpa using hv) (by simpa using hd)

end Aeneas.Std

namespace Aeneas.Std.SepLogic

/-- Every successful encoding return preserves the frame. This is preservation,
not an enabledness theorem from borrowed cells alone. -/
theorem endBorrowRange_encoding.post (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (data : Vector (Vector Byte repr.size) count)
    (encoded : ∀ i : Fin count, repr.encode values[i.val] data[i.val])
    (hcount : 0 < count) (hsize : 0 < repr.size)
    (h F : Fragment) (s next : Heap)
    (hp : block repr p bptr (List.replicate (count * repr.size) .borrowed) h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s (h ∪ F)) (hinv : s.Inv)
    (run : Heap.endBorrowRange repr p data.toList s = some next) :
    ∃ h', h'.Disjoint F ∧ Fragment.Matches next (h' ∪ F) ∧ next.Inv ∧
      pointsToRange repr p bptr values 0 h' := by
  obtain ⟨lower, aligned, rfl⟩ := hp
  let old := Vector.replicate (count * repr.size) (Cell.borrowed : Cell)
  let new := data.flatMap (fun encoding => encoding.map (Cell.shared 0))
  have matched : Fragment.Matches s
      (cellsHeap bptr p.provenance (p.offsetFrom bptr) old.toList) := by
    simpa [old] using ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨blk, hb, hl, live, hbase, selected⟩ :=
    bytes_of_matches (repr := repr.region count) (p := p.cast Unit) (data := old)
      (Nat.mul_pos hcount hsize) matched
  subst bptr
  change p.offsetFrom blk.bptr + count * repr.size ≤ blk.repr.length at hb
  change s.allocations p.provenance = some blk at hl
  change (repr.region count).select blk.bytes (p.offsetFrom blk.bptr) hb = old at selected
  let change := fun {r} (bytes : Vector Cell r) offset =>
    if (count = 0 ∨ 0 < repr.size) && offset + count * repr.size ≤ bytes.size then
      data.toList.zipIdx.foldlM (fun current (encoding, i) =>
        repr.endBorrow current (offset + i * repr.size) encoding) bytes
    else none
  have hc : change blk.bytes (p.offsetFrom blk.bptr) =
      some ((repr.region count).update blk.bytes (p.offsetFrom blk.bptr) hb new) := by
    simp only [change, hsize, or_true, decide_true, Bool.true_and, Vector.size, hb, ↓reduceIte]
    exact endBorrowRange_update repr data blk.bytes _ hb selected hsize
  have commit : Heap.commit
      (s.storeRepr p.provenance ((repr.region count).update blk.bytes
        (p.offsetFrom blk.bptr) hb new).toList) = some next := by
    simp [Heap.endBorrowRange, Heap.modify, hl, live, lower, aligned, hsize, hb] at run
    rw [endBorrowRange_update repr data blk.bytes _ hb selected hsize] at run
    simpa only [new, bind, Option.bind_some] using run
  obtain ⟨he, valid⟩ := Heap.commit_success _ _ commit
  have valid' : (s.storeRepr p.provenance ((repr.region count).update blk.bytes
      (p.offsetFrom blk.bptr) hb new).toList).check = true := he ▸ valid
  have ht := modify.spec (repr.region count) (p.cast Unit) s blk old new
    change hb hl live aligned hc valid'
  have run' : Heap.modify (repr.region count) (p.cast Unit) change s = some next := by
    change Heap.modify repr p change s = some next
    simpa [Heap.modify, hl, live, lower, aligned, hc] using commit
  obtain ⟨h', hd', hm', hi', hp'⟩ :=
    (ht _ F ⟨lower, aligned, rfl⟩ hd hm hinv).2 () next run'
  exact ⟨h', hd', hm', hi', data, encoded, hp'⟩

end Aeneas.Std.SepLogic

namespace Aeneas.Std.HeapWP

open SepLogic

/-- Whole-scope shared range contract, including return to exclusive depth zero.
    The callback is valid at the exact state produced by sharing. This is not
    an unrestricted rule that recovers exclusivity from shared cells alone. -/
theorem shareRange_return.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (initial : Vector T count) (depth : Nat) (hc : 0 < count) (positive : 0 < repr.size)
    (h F : Fragment) (s₀ : Heap) (hp : pointsToRange repr p bptr initial depth h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s₀ (h ∪ F)) (hinv : s₀.Inv) :
    Spec (RawPtr.shareRange repr p count)
      (fun values s₁ => values = initial.toList ∧
        Spec (RawPtr.endShareRange repr p initial.toList) (fun _ s₂ => s₂ = s₀) s₁) s₀ := by
  have forward := Spec.checkedModify.mp
    (shareRange.spec repr p bptr initial depth hc positive h F s₀ hp hd hm hinv)
  obtain ⟨old, _, lower, aligned, cells⟩ := hp
  have matching := ((Fragment.matches_union _ _ _).mp hm).1
  rw [cells] at matching
  have regionPositive : 0 < (repr.region count).size := Nat.mul_pos hc positive
  obtain ⟨blk, bound, lookup, live, base, selected⟩ :=
    bytes_of_matches (repr := repr.region count) (p := p.cast Unit) regionPositive matching
  subst bptr
  change (repr.region count).select blk.bytes (p.offsetFrom blk.bptr) bound =
    old.flatMap (fun encoding => encoding.map (Cell.shared depth)) at selected
  have wholeSelected :
      (repr.region count).select blk.bytes (p.offsetFrom blk.bptr) bound =
        (old.flatMap id).map (Cell.shared depth) := by
    rw [selected]
    apply Vector.ext
    intro i hi
    simp [Vector.getElem_flatMap]
  have forwardEq : Heap.shareRange repr p count s₀ =
      Heap.share (repr.region count) (p.cast Unit) s₀ :=
    sharedRange_as_region repr p old depth (depth + 1) s₀ blk hc positive bound lookup live
      lower aligned selected Cell.share (fun _ => rfl)
  apply Spec.checkedModify.mpr
  refine ⟨forward.1, ?_⟩
  intro values s₁ run
  obtain ⟨h₁, hd₁, hm₁, hi₁, hv, hp₁⟩ := forward.2 values s₁ run
  have undo := endShare_after_share (repr.region count) (p.cast Unit) s₀ s₁ blk (old.flatMap id)
    depth regionPositive bound lookup live lower aligned wholeSelected hinv
    (forwardEq ▸ run.2)
  have read := read_of_pointsToRange hc positive hp₁ ((Fragment.matches_union _ _ _).mp hm₁).1
  obtain ⟨current, _, lower₁, aligned₁, cells₁⟩ := hp₁
  have matching₁ := ((Fragment.matches_union _ _ _).mp hm₁).1
  rw [cells₁] at matching₁
  obtain ⟨blk₁, bound₁, lookup₁, live₁, base₁, selected₁⟩ :=
    bytes_of_matches (repr := repr.region count) (p := p.cast Unit) regionPositive matching₁
  have bound₁' : p.offsetFrom blk₁.bptr + count * repr.size ≤ blk₁.repr.length := by
    simpa only [base₁, RawPtr.offsetFrom, RawPtr.cast, Repr.region] using bound₁
  have selected₁' : (repr.region count).select blk₁.bytes (p.offsetFrom blk₁.bptr) bound₁' =
      current.flatMap (fun encoding => encoding.map (Cell.shared (depth + 1))) := by
    simpa only [base₁, RawPtr.offsetFrom, RawPtr.cast] using selected₁
  have backwardEq : Heap.endShareRange repr p count s₁ =
      Heap.endShare (repr.region count) (p.cast Unit) s₁ :=
    sharedRange_as_region repr p current (depth + 1) depth s₁ blk₁ hc positive
      bound₁' lookup₁ live₁ (by simpa [base₁] using lower₁) aligned₁ selected₁'
      Cell.endShare (fun _ => rfl)
  have returned : Heap.endShareRange repr p initial.toList.length s₁ = some s₀ := by
    simpa only [Vector.length_toList, backwardEq] using undo
  refine ⟨hv, Spec.checkedModify.mpr ⟨⟨(), s₀, ?_, returned⟩, ?_⟩⟩
  · simpa only [Vector.length_toList] using read
  · rintro _ s₂ ⟨_, returned₂⟩
    exact Option.some.inj (returned₂.symm.trans returned)

/-- Sharing supplies a matching return at the resulting state. Nested scopes
may use this contract when their own backward calls restore that state. -/
theorem shareRange_single_return.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (initial : T) (depth : Nat) (hsize : 0 < repr.size)
    (h F : Fragment) (s₀ : Heap) (hp : pointsTo repr p bptr initial depth h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s₀ (h ∪ F)) (hinv : s₀.Inv) :
    Spec (RawPtr.shareRange repr p 1)
      (fun values s₁ => values = [initial] ∧
        (∃ h₁, h₁.Disjoint F ∧ Fragment.Matches s₁ (h₁ ∪ F) ∧ s₁.Inv ∧
          pointsTo repr p bptr initial (depth + 1) h₁) ∧
        Spec (RawPtr.endShareRange repr p [initial]) (fun _ s₂ => s₂ = s₀) s₁) s₀ := by
  have forward := Spec.checkedModify.mp
    (shareRange_single.spec repr p bptr initial depth hsize h F s₀ hp hd hm hinv)
  have footprint := hp
  obtain ⟨old, _, lower, aligned, he⟩ := footprint
  have localMatch : Fragment.Matches s₀
      (cellsHeap bptr p.provenance (p.offsetFrom bptr) (old.map (Cell.shared depth)).toList) := by
    rw [he] at hm
    exact ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨blk, hb, hl, live, base, selected⟩ := bytes_of_matches hsize localMatch
  subst bptr
  apply Spec.checkedModify.mpr
  refine ⟨forward.1, ?_⟩
  intro values s₁ run
  obtain ⟨h₁, hd₁, hm₁, hi₁, hv, hp₁⟩ := forward.2 values s₁ run
  have undo := endShare_after_share repr p s₀ s₁ blk old depth hsize hb hl live lower aligned
    selected hinv (by simpa only [Heap.shareRange_single] using run.2)
  refine ⟨hv, ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩, ?_⟩
  have returning := Spec.checkedModify.mp
    (endShareRange_single.spec repr p blk.bptr initial depth s₁ hsize ⟨s₀, undo⟩
      h₁ F hp₁ hd₁ hm₁ hi₁)
  apply Spec.checkedModify.mpr
  refine ⟨returning.1, ?_⟩
  intro _ s₂ returned
  have actual : Heap.endShare repr p s₁ = some s₂ := by
    simpa only [List.length_singleton, Heap.endShareRange_single] using returned.2
  exact Option.some.inj (actual.symm.trans undo)

/-- The forward conversion supplies the matching backward computation, with
return enabledness proved from the original exclusive footprint. The callback
contract applies at the returned state: intervening heap effects require their
own scope-preservation argument, not borrowed-cell ownership alone. -/
theorem borrowWithBack.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (initial : T) (hsize : 0 < repr.size)
    (h F : Fragment) (s₀ : Heap) (hp : pointsTo repr p bptr initial 0 h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s₀ (h ∪ F)) (hinv : s₀.Inv) :
    Spec (RawPtr.borrowWithBack repr p)
      (fun (value, back) s₁ => value = initial ∧
        (∃ h₁, h₁.Disjoint F ∧ Fragment.Matches s₁ (h₁ ∪ F) ∧ s₁.Inv ∧
          block repr p bptr (List.replicate repr.size .borrowed) h₁) ∧
        ∀ updated, (∀ q, ¬ repr.Carries updated q) →
          Spec (back updated)
            (fun _ s₂ => ∃ h₂, h₂.Disjoint F ∧ Fragment.Matches s₂ (h₂ ∪ F) ∧
              s₂.Inv ∧ pointsTo repr p bptr updated 0 h₂) s₁) s₀ := by
  have forward := borrowRange_single.spec repr p bptr initial hsize h F s₀ hp hd hm hinv
  obtain ⟨enabled, post⟩ := Spec.checkedModify.mp forward
  obtain ⟨old, encoded, lower, aligned, he⟩ := hp
  have localMatch : Fragment.Matches s₀
      (cellsHeap bptr p.provenance (p.offsetFrom bptr) (old.map (Cell.shared 0)).toList) := by
    rw [he] at hm
    exact ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨blk, hb, hl, live, base, selected⟩ := bytes_of_matches hsize localMatch
  subst bptr
  have borrowing : Spec (RawPtr.borrow repr p)
      (fun value s₁ => value = initial ∧ Heap.borrow repr p s₀ = some s₁ ∧
        ∃ h₁, h₁.Disjoint F ∧ Fragment.Matches s₁ (h₁ ∪ F) ∧ s₁.Inv ∧
          block repr p blk.bptr (List.replicate repr.size .borrowed) h₁) s₀ := by
    unfold RawPtr.borrow
    have transfer : Spec (RawPtr.borrowRange repr p 1)
        (fun values s₁ => State.borrowRange repr p 1 s₀ values s₁ ∧
          ∃ h₁, h₁.Disjoint F ∧ Fragment.Matches s₁ (h₁ ∪ F) ∧ s₁.Inv ∧
            values = [initial] ∧
              block repr p blk.bptr (Vector.replicate repr.size .borrowed).toList h₁) s₀ :=
      Spec.checkedModify.mpr ⟨enabled, fun values s₁ run => ⟨run, post values s₁ run⟩⟩
    apply Spec.bind transfer
    rintro values s₁ ⟨⟨_, _, borrowed⟩, h₁, hd₁, hm₁, hi₁, rfl, hp₁⟩
    apply Spec.pure _ _ _ |>.mpr
    exact ⟨rfl, by simpa only [Heap.borrowRange_single] using borrowed,
      h₁, hd₁, hm₁, hi₁, hp₁⟩
  unfold RawPtr.borrowWithBack
  apply Spec.bind borrowing
  rintro value s₁ ⟨value_eq, borrowed, h₁, hd₁, hm₁, hi₁, hp₁⟩
  subst value
  apply Spec.pure _ _ _ |>.mpr
  refine ⟨rfl, ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩, ?_⟩
  intro updated noPointers
  have write := SepLogic.write_pointsTo.spec repr p blk.bptr initial updated noPointers hsize
    h F s₀ ⟨old, encoded, lower, aligned, he⟩ hd hm hinv
  have restore : ∀ data (encoded : repr.encode updated data),
      Heap.endBorrow repr p data s₁ = Heap.write repr p updated data encoded s₀ :=
    fun data encoded => endBorrow_after_borrow repr p s₀ s₁ blk old updated data encoded
      hsize hb hl live lower aligned selected borrowed
  apply Spec.checkedModify.mpr
  constructor
  · obtain ⟨_, s₂, data, encoded, run⟩ := write.1
    exact ⟨(), s₂, [data], ⟨encoded, trivial⟩, by
      simpa only [Heap.endBorrowRange_single, restore data encoded] using run⟩
  · rintro _ s₂ ⟨data, encoded, run⟩
    cases data
    · simp [Repr.encodeList] at encoded
    · rename_i bytes tail
      cases tail
      · exact write.2 () s₂ ⟨bytes, encoded.1, by
          simpa only [Heap.endBorrowRange_single, restore bytes encoded.1] using run⟩
      · simp [Repr.encodeList] at encoded

/-- Pure safe code can update a borrowed value and call its backward function
without exposing any global invariant or overlap obligation to the client. -/
theorem withBorrow.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (initial : T) (update : T → T)
    (noPointers : ∀ q, ¬ repr.Carries (update initial) q) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr initial) (RawPtr.withBorrow repr p update)
      (fun value h => value = initial ∧ pointsTo repr p bptr (update initial) 0 h) := by
  intro h F s₀ hp hd hm hinv
  unfold RawPtr.withBorrow
  apply Spec.bind (borrowWithBack.spec repr p bptr initial hsize h F s₀ hp hd hm hinv)
  rintro ⟨value, back⟩ s₁ ⟨value_eq, _, returns⟩
  subst value
  apply Spec.bind (returns (update initial) noPointers)
  rintro _ s₂ ⟨h₂, hd₂, hm₂, hi₂, hp₂⟩
  exact Spec.pure _ _ _ |>.mpr ⟨h₂, hd₂, hm₂, hi₂, rfl, hp₂⟩

/-- The matching range return installs every replacement element. Its authority
is scoped to the forward result, rather than inferred from borrowed cells alone. -/
theorem borrowRange_return.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (initial updated : Vector T count)
    (noPointers : ∀ i : Fin count, ∀ q, ¬ repr.Carries updated[i.val] q)
    (hcount : 0 < count) (hsize : 0 < repr.size)
    (h F : Fragment) (s₀ : Heap) (hp : pointsToRange repr p bptr initial 0 h)
    (hd : h.Disjoint F) (hm : Fragment.Matches s₀ (h ∪ F)) (hinv : s₀.Inv) :
    Spec (RawPtr.borrowRange repr p count)
      (fun values s₁ => values = initial.toList ∧
        Spec (RawPtr.endBorrowRange repr p updated.toList)
          (fun _ s₂ => ∃ h₂, h₂.Disjoint F ∧ Fragment.Matches s₂ (h₂ ∪ F) ∧ s₂.Inv ∧
            pointsToRange repr p bptr updated 0 h₂) s₁) s₀ := by
  have forward := Spec.checkedModify.mp
    (borrowRange.spec repr p bptr initial hcount hsize h F s₀ hp hd hm hinv)
  obtain ⟨old, _, lower, aligned, he⟩ := hp
  have localMatch : Fragment.Matches s₀
      (cellsHeap bptr p.provenance (p.offsetFrom bptr)
        (old.flatMap (fun encoding => encoding.map (Cell.shared 0))).toList) := by
    rw [he] at hm
    exact ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨blk, hb, hl, live, base, selected⟩ :=
    bytes_of_matches (repr := repr.region count) (p := p.cast Unit)
      (Nat.mul_pos hcount hsize) localMatch
  subst bptr
  have updateInv (data : Vector (Vector Byte repr.size) count)
      (encoded : ∀ i : Fin count, repr.encode updated[i.val] data[i.val]) :
      (s₀.storeRepr p.provenance
        ((repr.region count).update blk.bytes (p.offsetFrom blk.bptr) hb
          (data.flatMap (fun encoding => encoding.map (Cell.shared 0)))).toList).Inv := by
    apply Heap.update_Inv hinv hl hb _ _ selected
    · intro i hi
      dsimp only [Repr.region] at hi ⊢
      have outer : i / repr.size < count := by
        exact Nat.div_lt_of_lt_mul (by simpa only [Nat.mul_comm] using hi)
      have inner : i % repr.size < repr.size := Nat.mod_lt _ hsize
      change (match (data.flatMap (fun encoding => encoding.map (Cell.shared 0)))[i]'hi with
        | .borrowed => True
        | .shared _ byte => s₀.validByte byte = true)
      rw [Vector.getElem_flatMap hi, Vector.getElem_map]
      exact valid_encoding (encoded ⟨i / repr.size, outer⟩)
        (fun q carried => (noPointers ⟨i / repr.size, outer⟩ q carried).elim) _ inner
    · intro i hi
      dsimp only [Repr.region] at hi ⊢
      change ((old.flatMap (fun encoding => encoding.map (Cell.shared 0)))[i]'hi).PermWeakens
        ((data.flatMap (fun encoding => encoding.map (Cell.shared 0)))[i]'hi)
      rw [Vector.getElem_flatMap hi, Vector.getElem_map]
      rw [Vector.getElem_flatMap hi, Vector.getElem_map]
      exact Cell.PermWeakens.writer _ _
  apply Spec.checkedModify.mpr
  refine ⟨forward.1, ?_⟩
  intro values s₁ run
  obtain ⟨h₁, hd₁, hm₁, hi₁, hv, hp₁⟩ := forward.2 values s₁ run
  refine ⟨hv, ?_⟩
  have inverse (data : Vector (Vector Byte repr.size) count) :=
    endBorrowRange_after_borrowRange repr p s₀ s₁ blk old data hsize hb hl live lower aligned
      selected run.2.2
  have enabled (data : Vector (Vector Byte repr.size) count)
      (encoded : ∀ i : Fin count, repr.encode updated[i.val] data[i.val]) :
      ∃ s₂, Heap.endBorrowRange repr p data.toList s₁ = some s₂ := by
    rw [inverse data]
    simp only [Heap.commit, (updateInv data encoded).2, ↓reduceIte]
    exact ⟨_, rfl⟩
  apply Spec.checkedModify.mpr
  constructor
  · obtain ⟨data, encoded⟩ := repr.encodeList_complete updated.toList
    have length : data.length = count := by
      simpa using encodeList_length repr updated.toList data encoded
    let vector : Vector (Vector Byte repr.size) count := ⟨data.toArray, by simp [length]⟩
    have enc : ∀ i : Fin count, repr.encode updated[i.val] vector[i.val] := by
      intro i
      simpa [vector] using encodeList_get repr updated.toList data encoded i.val
        (by simp) (by simp [length])
    obtain ⟨s₂, actual⟩ := enabled vector enc
    exact ⟨(), s₂, data, encoded, by simpa [vector] using actual⟩
  · rintro _ s₂ ⟨data, encoded, actual⟩
    have length : data.length = count := by
      simpa using encodeList_length repr updated.toList data encoded
    let vector : Vector (Vector Byte repr.size) count := ⟨data.toArray, by simp [length]⟩
    have enc : ∀ i : Fin count, repr.encode updated[i.val] vector[i.val] := by
      intro i
      simpa [vector] using encodeList_get repr updated.toList data encoded i.val
        (by simp) (by simp [length])
    exact endBorrowRange_encoding.post repr p blk.bptr updated vector enc hcount hsize
      h₁ F s₁ s₂ hp₁ hd₁ hm₁ hi₁ (by simpa [vector] using actual)

/-- Low-level state-specific return rule. One compatible encoding enables the
operation; the postcondition covers all permitted encodings. Scoped clients use
captured-state callback contracts or derive enabledness from RootReturn via
endBorrowRange_exclusive.spec, rather than assuming it from borrowed cells. -/
theorem endBorrowRange.spec (repr : Repr T) (p : RawPtr T) (bptr : BasePtr)
    (values : Vector T count) (s : Heap) (hcount : 0 < count) (hsize : 0 < repr.size)
    (enabled : ∃ next, State.endBorrowRange repr p values.toList s () next) :
    TripleAt (block repr p bptr (List.replicate (count * repr.size) .borrowed))
      (RawPtr.endBorrowRange repr p values.toList)
      (fun _ => pointsToRange repr p bptr values) s := by
  apply TripleAt.checkedModify
  intro h F hp hd hm hinv
  obtain ⟨next, hn⟩ := enabled
  refine ⟨⟨(), next, hn⟩, ?_⟩
  rintro _ next ⟨encodings, encoded, run⟩
  have hlen : encodings.length = count := by
    simpa using encodeList_length repr values.toList encodings encoded
  let data : Vector (Vector Byte repr.size) count := ⟨encodings.toArray, by simp [hlen]⟩
  have hlist : data.toList = encodings := by simp [data]
  have each : ∀ i : Fin count, repr.encode values[i.val] data[i.val] := by
    intro i
    have hi : i.val < encodings.length := by simp [hlen]
    simpa [data] using encodeList_get repr values.toList encodings encoded i.val
      (by simp) hi
  exact SepLogic.endBorrowRange_encoding.post repr p bptr values data each hcount hsize
    h F s next hp hd hm hinv (by simpa only [hlist] using run)

theorem emptyRange_transfer.spec (repr : Repr T) (p : RawPtr T) (s : Heap) (blk : Block)
    (change : ∀ {r}, Vector Cell r → Nat → Option (Vector Cell r))
    (hinv : s.Inv) (hl : s.allocations p.provenance = some blk) (live : s.live blk = true)
    (lower : blk.bptr.val ≤ p.address.val) (aligned : repr.align.val ∣ p.address.val)
    (bound : p.address.val ≤ blk.bptr.val + blk.repr.length) :
    Spec (Result.checkedModify (fun s result s' =>
      Heap.readRange repr p 0 s = some result ∧ Heap.modifyRange repr p 0 change s = some s'))
      (fun result s' => result = [] ∧ s' = s) s := by
  have hr : Heap.readRange repr p 0 s = some [] := by
    simp [Heap.readRange, hl, live, lower, aligned, bound]
  have hc := Heap.modifyRange_empty repr p s blk change hinv hl live lower aligned bound
  apply Spec.checkedModify.mpr
  refine ⟨⟨[], s, hr, hc⟩, ?_⟩
  rintro result s' ⟨he, he'⟩
  exact ⟨Option.some.inj (he.symm.trans hr), Option.some.inj (he'.symm.trans hc)⟩

/-- Empty transfers require a live aligned view and an in-bounds position.
They neither restore permissions nor change the heap. -/
theorem emptyRanges.spec (repr : Repr T) (p : RawPtr T) (s : Heap) (blk : Block)
    (hinv : s.Inv) (hl : s.allocations p.provenance = some blk) (live : s.live blk = true)
    (lower : blk.bptr.val ≤ p.address.val) (aligned : repr.align.val ∣ p.address.val)
    (bound : p.address.val ≤ blk.bptr.val + blk.repr.length) :
    Spec (RawPtr.borrowRange repr p 0) (fun result s' => result = [] ∧ s' = s) s ∧
    Spec (RawPtr.shareRange repr p 0) (fun result s' => result = [] ∧ s' = s) s ∧
    Spec (RawPtr.endShareRange repr p []) (fun _ s' => s' = s) s ∧
    Spec (RawPtr.endBorrowRange repr p []) (fun _ s' => s' = s) s := by
  have hr : Heap.readRange repr p 0 s = some [] := by
    simp [Heap.readRange, hl, live, lower, aligned, bound]
  have hc : ∀ change, Heap.modifyRange repr p 0 change s = some s :=
    fun change => Heap.modifyRange_empty repr p s blk change hinv hl live lower aligned bound
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Spec.checkedModify.mpr
    have mutable : State.mutableValues repr p [] s := ⟨blk, hl, by simp⟩
    refine ⟨⟨[], s, hr, mutable, hc _⟩, ?_⟩
    rintro result next ⟨read, _, run⟩
    exact ⟨Option.some.inj (read.symm.trans hr), Option.some.inj (run.symm.trans (hc _))⟩
  · exact emptyRange_transfer.spec repr p s blk _ hinv hl live lower aligned bound
  · apply Spec.checkedModify.mpr
    refine ⟨⟨(), s, hr, hc _⟩, ?_⟩
    rintro _ next ⟨_, run⟩
    exact Option.some.inj (run.symm.trans (hc _))
  · apply Spec.checkedModify.mpr
    have run : Heap.endBorrowRange repr p [] s = some s := by
      simpa [Heap.endBorrowRange, Heap.modifyRange] using hc (fun bytes _ => some bytes)
    refine ⟨⟨(), s, [], trivial, run⟩, ?_⟩
    rintro _ next ⟨data, encoded, run'⟩
    have empty : data = [] := by
      cases data
      · rfl
      · simp [Repr.encodeList] at encoded
    subst data
    exact Option.some.inj (run'.symm.trans run)

end Aeneas.Std.HeapWP
