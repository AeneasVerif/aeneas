module

public import Aeneas.Std.Heap.Allocation

/-! Selected-view transfers preserve symbolic bytes. Restoration/decrements are
state-specific: linear indexed ownership alone does not rule out physical aliases.
Scoped callback contracts additionally require current-state return authority;
this low-level interface does not supply that authority. -/

@[expose] public section

namespace Aeneas.Std.SepLogic

theorem borrowAt.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (values : Vector Byte repr.size) (hsize : 0 < repr.size)
    (hb : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ p.address.val)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb = values.map (Cell.shared 0))
    (valid : (s.storeRepr p.provenance (repr.update blk.bytes (p.offsetFrom blk.bptr) hb
      (Vector.replicate repr.size .borrowed)).toList).check = true) :
    TripleAt (block repr p blk.bptr (values.map (Cell.shared 0)).toList)
      (fun s (_ : Unit) s' => Heap.borrow repr p s = some s')
      (fun _ => block repr p blk.bptr (Vector.replicate repr.size .borrowed).toList) s := by
  have hz : values.map (fun _ => Cell.borrowed) =
      Vector.replicate repr.size Cell.borrowed := by
    apply Vector.ext
    intro i hi
    simp
  apply modify.spec repr p s blk _ _ (fun bytes i => repr.borrow bytes i)
    hb hl hlive ha _ valid
  simp [Repr.borrow, hsize, hb, selected, Vector.mapM_map, Function.comp_def,
    Cell.borrow, vector_mapM_some, hz]

theorem shareAt.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (values : Vector Byte repr.size) (depth : Nat) (hsize : 0 < repr.size)
    (hb : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ p.address.val)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb = values.map (Cell.shared depth))
    (valid : (s.storeRepr p.provenance (repr.update blk.bytes (p.offsetFrom blk.bptr) hb
      (values.map (Cell.shared (depth + 1)))).toList).check = true) :
    TripleAt (block repr p blk.bptr (values.map (Cell.shared depth)).toList)
      (fun s (_ : Unit) s' => Heap.share repr p s = some s')
      (fun _ => block repr p blk.bptr (values.map (Cell.shared (depth + 1))).toList) s := by
  apply modify.spec repr p s blk _ _ (fun bytes i => repr.share bytes i)
    hb hl hlive ha _ valid
  simp [Repr.share, hsize, hb, selected, Vector.mapM_map, Function.comp_def,
    Cell.share, vector_mapM_some]

/-- Restoring depth zero is enabled only when physically conflicting observers
have returned. A different view's positive shared contribution blocks this step. -/
theorem endShare.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (values : Vector Byte repr.size) (depth : Nat) (hsize : 0 < repr.size)
    (hb : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ p.address.val)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb =
      values.map (Cell.shared (depth + 1)))
    (valid : (s.storeRepr p.provenance (repr.update blk.bytes (p.offsetFrom blk.bptr) hb
      (values.map (Cell.shared depth))).toList).check = true) :
    TripleAt (block repr p blk.bptr (values.map (Cell.shared (depth + 1))).toList)
      (fun s (_ : Unit) s' => Heap.endShare repr p s = some s')
      (fun _ => block repr p blk.bptr (values.map (Cell.shared depth)).toList) s := by
  apply modify.spec repr p s blk _ _ (fun bytes i => repr.endShare bytes i)
    hb hl hlive ha _ valid
  simp [Repr.endShare, hsize, hb, selected, Vector.mapM_map, Function.comp_def,
    Cell.endShare, vector_mapM_some]

/-- Matching continuation authority is not supplied by this raw contract.
The restored admissible encoding and all aliased frames are pinned exactly. -/
theorem endBorrow.spec (repr : Repr ty) (p : RawPtr ty) (s : Heap) (blk : Block)
    (data : Vector Byte repr.size) (value : ty) (encoded : repr.encode value data)
    (hsize : 0 < repr.size) (hb : (p.offsetFrom blk.bptr) + repr.size ≤ blk.repr.length)
    (hl : s.allocations p.provenance = some blk) (hlive : s.live blk = true)
    (ha : repr.align.val ∣ p.address.val)
    (selected : repr.select blk.bytes (p.offsetFrom blk.bptr) hb =
      Vector.replicate repr.size .borrowed)
    (valid : (s.storeRepr p.provenance (repr.update blk.bytes (p.offsetFrom blk.bptr) hb
      (data.map (Cell.shared 0))).toList).check = true) :
    TripleAt (block repr p blk.bptr (Vector.replicate repr.size .borrowed).toList)
      (fun s (_ : Unit) s' => Heap.endBorrow repr p data s = some s')
      (fun _ => pointsTo repr p blk.bptr value) s := by
  have hc : Repr.endBorrow repr blk.bytes (p.offsetFrom blk.bptr) data =
      some (repr.update blk.bytes (p.offsetFrom blk.bptr) hb (data.map (Cell.shared 0))) := by
    have hz : (Vector.replicate repr.size (Cell.borrowed : Cell)).zip data =
        data.map (fun byte => (Cell.borrowed, byte)) := by
      apply Vector.ext
      intro i hi
      simp
    simp [Repr.endBorrow, hsize, hb, selected, hz, Vector.mapM_map, Function.comp_def,
      Cell.endBorrow, vector_mapM_some]
  have ht := modify.spec repr p s blk (Vector.replicate repr.size .borrowed)
    (data.map (Cell.shared 0)) (fun bytes i => repr.endBorrow bytes i data)
    hb hl hlive ha hc valid
  intro h F hp hd hm hi
  obtain ⟨enabled, post⟩ := ht h F hp hd hm hi
  refine ⟨enabled, fun x s' hrun => ?_⟩
  obtain ⟨h', hd', hm', hi', hp'⟩ := post x s' hrun
  exact ⟨h', hd', hm', hi', data, encoded, hp'⟩

/-- Removing raw access cannot create alias conflicts, even with overlapping
borrowed ancestor views in an arbitrary frame. -/
theorem borrow.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (values : Vector Byte repr.size) (hsize : 0 < repr.size) :
    Triple (block repr p bptr (values.map (Cell.shared 0)).toList)
      (fun s₀ (_ : Unit) s₁ => Heap.borrow repr p s₀ = some s₁)
      (fun _ => block repr p bptr (Vector.replicate repr.size .borrowed).toList) := by
  rintro h F s ⟨hlo, ha, rfl⟩ hd hm hinv
  obtain ⟨blk, hb, hl, hlive, hbase, selected⟩ :=
    bytes_of_matches hsize ((Fragment.matches_union _ _ _).mp hm).1
  subst bptr
  have valid := Heap.update_Inv hinv hl hb _ (Vector.replicate repr.size .borrowed)
    selected (by intro i hi; simp)
    (by intro i hi; simpa using Cell.PermWeakens.borrow (Cell.shared 0 values[i]))
  exact borrowAt.spec repr p s blk values hsize hb hl hlive ha selected valid.2
    _ F ⟨hlo, ha, rfl⟩ hd hm hinv

theorem borrow_pointsTo.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (value : ty) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr value)
      (fun s₀ (_ : Unit) s₁ => Heap.borrow repr p s₀ = some s₁)
      (fun _ => block repr p bptr (Vector.replicate repr.size .borrowed).toList) := by
  rintro h F s ⟨data, _, hp⟩ hd hm hinv
  exact borrow.spec repr p bptr data hsize h F s hp hd hm hinv

/-- Increasing sharing depth retains symbolic bytes and only weakens permission. -/
theorem share.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (values : Vector Byte repr.size) (depth : Nat) (hsize : 0 < repr.size) :
    Triple (block repr p bptr (values.map (Cell.shared depth)).toList)
      (fun s₀ (_ : Unit) s₁ => Heap.share repr p s₀ = some s₁)
      (fun _ => block repr p bptr (values.map (Cell.shared (depth + 1))).toList) := by
  rintro h F s ⟨hlo, ha, rfl⟩ hd hm hinv
  obtain ⟨blk, hb, hl, hlive, hbase, selected⟩ :=
    bytes_of_matches hsize ((Fragment.matches_union _ _ _).mp hm).1
  subst bptr
  have valid := Heap.update_Inv hinv hl hb _ (values.map (Cell.shared (depth + 1))) selected
    (fun i hi => by
      simpa only [Vector.getElem_map] using hinv.validSelected hl hb selected i hi)
    (fun i hi => by
      simp only [Vector.getElem_map]
      exact Cell.PermWeakens.share _ _)
  exact shareAt.spec repr p s blk values depth hsize hb hl hlive ha selected valid.2
    _ F ⟨hlo, ha, rfl⟩ hd hm hinv

theorem share_pointsTo.spec (repr : Repr ty) (p : RawPtr ty) (bptr : BasePtr)
    (value : ty) (depth : Nat) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p bptr value depth)
      (fun s₀ (_ : Unit) s₁ => Heap.share repr p s₀ = some s₁)
      (fun _ => pointsTo repr p bptr value (depth + 1)) := by
  rintro h F s ⟨data, encoded, hp⟩ hd hm hinv
  obtain ⟨enabled, post⟩ := share.spec repr p bptr data depth hsize h F s hp hd hm hinv
  refine ⟨enabled, ?_⟩
  intro x s₁ he
  obtain ⟨h₁, hd₁, hm₁, hi₁, hp₁⟩ := post x s₁ he
  exact ⟨h₁, hd₁, hm₁, hi₁, data, encoded, hp₁⟩

end Aeneas.Std.SepLogic
