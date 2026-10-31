module

public import Aeneas.Std.Heap.Ranges
import all Aeneas.Std.Heap.Ranges
import all Aeneas.Std.Core.Ptr
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap.Separation

/-! Restoration is for the matching translated backward continuation, not a way
for arbitrary raw clients to regain a borrowed footprint. -/

@[expose] public section

namespace Aeneas.Std.Heap

theorem storeRepr_same (s : Heap) (base : BasePtr) (blk : Block)
    (hl : s.allocations base = some blk) : s.storeRepr base blk.repr = s := by
  rcases s with ⟨allocations, next⟩
  change allocations base = some blk at hl
  apply congrArg (fun a => Heap.mk a next)
  funext other
  by_cases he : other = base
  · subst other
    simp [update, hl]
  · simp [update, he]

theorem modifyRange_empty (repr : Repr T) (p : RawPtr T) (s : Heap) (blk : Block)
    (change : ∀ {r}, Vector (Cell U8) r → Nat → Option (Vector (Cell U8) r))
    (hl : s.allocations p.base = some blk)
    (ha : repr.align.val ∣ blk.alignment.val) (hp : repr.align.val ∣ p.byteOffset.val)
    (hb : p.byteOffset.val ≤ blk.repr.length) :
    Heap.modifyRange repr p 0 change s = some s := by
  simp [Heap.modifyRange, Heap.modify, hl, ha, hp, hb, Block.bytes, storeRepr_same s p.base blk hl]

end Aeneas.Std.Heap

namespace Aeneas.Std.SepLogic

theorem endBorrowRange_encoding.spec (repr : Repr T) (p : RawPtr T)
    (values : Vector T count) (data : Vector (Vector U8 repr.size) count)
    (decoded : ∀ i : Fin count, repr.decode data[i.val] = some values[i.val])
    (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (block repr p (List.replicate (count * repr.size) .borrowed))
      (fun s (_ : Unit) s' => Heap.endBorrowRange repr p data.toList s = some s')
      (fun _ => pointsToRange repr p values) := by
  let old : Vector (Vector (Cell U8) repr.size) count :=
    Vector.replicate count (Vector.replicate repr.size .borrowed)
  let new := data.map fun bytes => bytes.map (Cell.shared 0 ∘ some)
  have ht := modifyRange.spec repr p old new
    (fun bytes i =>
      match data.toList[i]? with
      | some encoding =>
        match h : repr.decode encoding with
        | some value => repr.endBorrow bytes (p.byteOffset.val + i * repr.size) value encoding h
        | none => none
      | none => none)
    hcount hsize (by
      intro r bytes i hi hb hs
      rw [Vector.getElem?_toList, Vector.getElem?_eq_getElem hi]
      dsimp only
      simp only [Repr.endBorrow, hsize, range_element_bound hi hb, and_self, ↓reduceDIte, hs]
      have hz : (Vector.replicate repr.size (Cell.borrowed : Cell U8)).zip data[i] =
          data[i].map (fun byte => (Cell.borrowed, byte)) := by
        apply Vector.ext
        intro j hj
        simp
      simp only [old, Vector.getElem_replicate, hz, Vector.mapM_map, Function.comp_def,
        Cell.endBorrow, vector_mapM_some]
      rw [decoded ⟨i, hi⟩]
      simp [new, Function.comp_def])
  simp only [Heap.endBorrowRange, Vector.length_toList]
  exact Triple.conseq (fun _ h => by simpa [old, Vector.flatMap_replicate] using h)
    (fun _ _ h => ⟨data, decoded, by simpa [new, Vector.flatMap_map] using h⟩) ht

end Aeneas.Std.SepLogic

namespace Aeneas.Std.HeapWP

open SepLogic

/-- Every list encoding that decodes to the replacement values restores the range. -/
theorem endBorrowRange.spec (repr : Repr T) (p : RawPtr T) (values : Vector T count)
    (hcount : 0 < count) (hsize : 0 < repr.size) :
    Triple (block repr p (List.replicate (count * repr.size) .borrowed))
      (RawPtr.endBorrowRange repr p values.toList) (fun _ => pointsToRange repr p values) := by
  unfold RawPtr.endBorrowRange
  apply Triple.bind (Triple.chooseList _ repr values.toList)
  rintro ⟨encodings, hd⟩
  have hlen : encodings.length = count := by
    have he := congrArg List.length hd
    simpa using he
  let data : Vector (Vector U8 repr.size) count := ⟨encodings.toArray, by simpa using hlen⟩
  have hlist : data.toList = encodings := by simp [data]
  have decoded : ∀ i : Fin count, repr.decode data[i.val] = some values[i.val] := by
    intro i
    have he := congrArg (fun xs => xs[i.val]?) hd
    have hi : i.val < encodings.length := by simp [hlen]
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
      Vector.getElem?_toList, Vector.getElem?_eq_getElem i.isLt, Option.map_some] at he
    have hget : encodings[i.val] = data[i.val] := by simp [data]
    exact Option.some.inj (hget ▸ he)
  apply Triple.checkedModify
  simpa only [hlist] using
    SepLogic.endBorrowRange_encoding.spec repr p values data decoded hcount hsize

theorem emptyRange_transfer.spec (repr : Repr T) (p : RawPtr T) (s : Heap) (blk : Block)
    (change : ∀ {r}, Vector (Cell U8) r → Nat → Option (Vector (Cell U8) r))
    (hl : s.allocations p.base = some blk)
    (ha : repr.align.val ∣ blk.alignment.val) (hp : repr.align.val ∣ p.byteOffset.val)
    (hb : p.byteOffset.val ≤ blk.repr.length) :
    Spec (Result.checkedModify (fun s result s' =>
      Heap.readRange repr p 0 s = some result ∧ Heap.modifyRange repr p 0 change s = some s'))
      (fun result s' => result = [] ∧ s' = s) s := by
  have hr : Heap.readRange repr p 0 s = some [] := by simp [Heap.readRange, hl, ha, hp, hb]
  have hc := Heap.modifyRange_empty repr p s blk change hl ha hp hb
  apply Spec.checkedModify.mpr
  refine ⟨⟨[], s, hr, hc⟩, ?_⟩
  rintro result s' ⟨he, he'⟩
  exact ⟨Option.some.inj (he.symm.trans hr), Option.some.inj (he'.symm.trans hc)⟩

/-- Empty transfers still require a live aligned allocation and an in-bounds position. -/
theorem emptyRanges.spec (repr : Repr T) (p : RawPtr T) (s : Heap) (blk : Block)
    (hl : s.allocations p.base = some blk)
    (ha : repr.align.val ∣ blk.alignment.val) (hp : repr.align.val ∣ p.byteOffset.val)
    (hb : p.byteOffset.val ≤ blk.repr.length) :
    Spec (RawPtr.borrowRange repr p 0) (fun result s' => result = [] ∧ s' = s) s ∧
    Spec (RawPtr.shareRange repr p 0) (fun result s' => result = [] ∧ s' = s) s ∧
    Spec (RawPtr.endShareRange repr p []) (fun _ s' => s' = s) s ∧
    Spec (RawPtr.endBorrowRange repr p []) (fun _ s' => s' = s) s := by
  have hr : Heap.readRange repr p 0 s = some [] := by simp [Heap.readRange, hl, ha, hp, hb]
  have borrow := emptyRange_transfer.spec repr p s blk
    (fun bytes i => repr.borrow bytes (p.byteOffset.val + i * repr.size)) hl ha hp hb
  have share := emptyRange_transfer.spec repr p s blk
    (fun bytes i => repr.share bytes (p.byteOffset.val + i * repr.size)) hl ha hp hb
  refine ⟨borrow, share, ?_, ?_⟩
  · apply Spec.checkedModify.mpr
    have hc : Heap.endShareRange repr p 0 s = some s :=
      Heap.modifyRange_empty repr p s blk _ hl ha hp hb
    refine ⟨⟨(), s, hr, hc⟩, ?_⟩
    rintro _ s' ⟨_, he⟩
    exact Option.some.inj (he.symm.trans hc)
  · unfold RawPtr.endBorrowRange
    have hchoose : Spec (repr.chooseList []) (fun _ s' => s' = s) s :=
      (Spec.chooseList repr [] _ s).mpr (fun _ _ => rfl)
    apply Spec.bind hchoose
    rintro ⟨data, decoded⟩ current he
    subst current
    have he : data = [] := by
      have hh := congrArg List.length decoded
      simpa using hh
    subst data
    apply Spec.checkedModify.mpr
    have hc : Heap.endBorrowRange repr p [] s = some s :=
      Heap.modifyRange_empty repr p s blk _ hl ha hp hb
    refine ⟨⟨(), s, hc⟩, ?_⟩
    rintro _ s' he
    exact Option.some.inj (he.symm.trans hc)

end Aeneas.Std.HeapWP
