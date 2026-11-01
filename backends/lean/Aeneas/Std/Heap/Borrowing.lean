module

public import Aeneas.Std.Heap.Allocation

/-! Selected-view transfers preserve symbolic bytes. Restoration/decrements are
state-specific: linear indexed ownership alone does not rule out physical aliases.
Matching safe backward-continuation authority is a separate boundary assumption. -/

@[expose] public section

namespace Aeneas.Std.SepLogic

theorem borrow.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (values : Vector Byte repr.size) (hsize : 0 < repr.size)
    (hb : p.byteOffset.val + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.base = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ blk.bptr.val + p.byteOffset.val)
    (selected : repr.select blk.bytes p.byteOffset.val hb = values.map (Cell.shared 0))
    (valid : (s.storeRepr p.base (repr.update blk.bytes p.byteOffset.val hb
      (Vector.replicate repr.size .borrowed)).toList).check = true) :
    TripleAt (block repr p blk.bptr (values.map (Cell.shared 0)).toList)
      (fun s (_ : Unit) s' => Heap.borrow repr p s = some s')
      (fun _ => block repr p blk.bptr (Vector.replicate repr.size .borrowed).toList) s := by
  have hz : values.map (fun _ => Cell.borrowed) =
      Vector.replicate repr.size Cell.borrowed := by
    apply Vector.ext
    intro i hi
    simp
  apply modify.spec repr p s blk _ _ (fun bytes => repr.borrow bytes p.byteOffset.val)
    hb hl hlive ha _ valid
  simp [Repr.borrow, hsize, hb, selected, Vector.mapM_map, Function.comp_def,
    Cell.borrow, vector_mapM_some, hz]

theorem share.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (values : Vector Byte repr.size) (depth : Nat) (hsize : 0 < repr.size)
    (hb : p.byteOffset.val + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.base = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ blk.bptr.val + p.byteOffset.val)
    (selected : repr.select blk.bytes p.byteOffset.val hb = values.map (Cell.shared depth))
    (valid : (s.storeRepr p.base (repr.update blk.bytes p.byteOffset.val hb
      (values.map (Cell.shared (depth + 1)))).toList).check = true) :
    TripleAt (block repr p blk.bptr (values.map (Cell.shared depth)).toList)
      (fun s (_ : Unit) s' => Heap.share repr p s = some s')
      (fun _ => block repr p blk.bptr (values.map (Cell.shared (depth + 1))).toList) s := by
  apply modify.spec repr p s blk _ _ (fun bytes => repr.share bytes p.byteOffset.val)
    hb hl hlive ha _ valid
  simp [Repr.share, hsize, hb, selected, Vector.mapM_map, Function.comp_def,
    Cell.share, vector_mapM_some]

/-- Restoring depth zero is enabled only when physically conflicting observers
have returned. A different view's positive shared contribution blocks this step. -/
theorem endShare.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (values : Vector Byte repr.size) (depth : Nat) (hsize : 0 < repr.size)
    (hb : p.byteOffset.val + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.base = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ blk.bptr.val + p.byteOffset.val)
    (selected : repr.select blk.bytes p.byteOffset.val hb =
      values.map (Cell.shared (depth + 1)))
    (valid : (s.storeRepr p.base (repr.update blk.bytes p.byteOffset.val hb
      (values.map (Cell.shared depth))).toList).check = true) :
    TripleAt (block repr p blk.bptr (values.map (Cell.shared (depth + 1))).toList)
      (fun s (_ : Unit) s' => Heap.endShare repr p s = some s')
      (fun _ => block repr p blk.bptr (values.map (Cell.shared depth)).toList) s := by
  apply modify.spec repr p s blk _ _ (fun bytes => repr.endShare bytes p.byteOffset.val)
    hb hl hlive ha _ valid
  simp [Repr.endShare, hsize, hb, selected, Vector.mapM_map, Function.comp_def,
    Cell.endShare, vector_mapM_some]

/-- Matching continuation authority is not supplied by this raw contract.
The restored admissible encoding and all aliased frames are pinned exactly. -/
theorem endBorrow.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (data : Vector Byte repr.size) (value : ty) (encoded : repr.encodes value data)
    (initialized : ∀ i : Fin repr.size, data[i.val] ≠ .uninit)
    (hsize : 0 < repr.size) (hb : p.byteOffset.val + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.base = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ blk.bptr.val + p.byteOffset.val)
    (selected : repr.select blk.bytes p.byteOffset.val hb =
      Vector.replicate repr.size .borrowed)
    (valid : (s.storeRepr p.base (repr.update blk.bytes p.byteOffset.val hb
      (data.map (Cell.shared 0))).toList).check = true) :
    TripleAt (block repr p blk.bptr (Vector.replicate repr.size .borrowed).toList)
      (fun s (_ : Unit) s' => Heap.endBorrow repr p data s = some s')
      (fun _ => pointsTo repr p blk.bptr value) s := by
  have hc : Repr.endBorrow repr blk.bytes p.byteOffset.val data =
      some (repr.update blk.bytes p.byteOffset.val hb (data.map (Cell.shared 0))) := by
    have hz : (Vector.replicate repr.size (Cell.borrowed : Cell)).zip data =
        data.map (fun byte => (Cell.borrowed, byte)) := by
      apply Vector.ext
      intro i hi
      simp
    simp [Repr.endBorrow, hsize, hb, selected, hz, Vector.mapM_map, Function.comp_def,
      Cell.endBorrow, vector_mapM_some]
  have ht := modify.spec repr p s blk (Vector.replicate repr.size .borrowed)
    (data.map (Cell.shared 0)) (fun bytes => repr.endBorrow bytes p.byteOffset.val data)
    hb hl hlive ha hc valid
  intro h F hp hd hm hi
  obtain ⟨enabled, post⟩ := ht h F hp hd hm hi
  refine ⟨enabled, fun x s' hrun => ?_⟩
  obtain ⟨h', hd', hm', hi', hp'⟩ := post x s' hrun
  exact ⟨h', hd', hm', hi', data, encoded, initialized, hp'⟩

end Aeneas.Std.SepLogic
