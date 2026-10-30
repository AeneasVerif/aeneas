module

public import Aeneas.Std.Heap.Allocation
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources

/-! Permission transfer changes bytes, not typed values. Restoration is reserved
for the matching translated backward computation; these contracts do not confer
that authority on arbitrary Lean callers. -/

@[expose] public section

namespace Aeneas.Std.SepLogic

theorem borrow.spec (repr : Repr ty) (p : RawPtr ty) (values : Vector (Option U8) repr.size)
    (hsize : 0 < repr.size) :
    Triple (block repr p (values.map (Cell.shared 0)).toList)
      (fun s (_ : Unit) s' => Heap.borrow repr p s = some s')
      (fun _ => block repr p (values.map (fun _ => .borrowed)).toList) := by
  apply modify.spec repr p _ _ _ hsize
  intro r bytes hb he
  simp only [Repr.borrow, hsize, hb, and_self, dite_true, he, Vector.mapM_map,
    Function.comp_def, Cell.borrow]
  rw [vector_mapM_some]

theorem share.spec (repr : Repr ty) (p : RawPtr ty) (values : Vector (Option U8) repr.size)
    (depth : Nat) (hsize : 0 < repr.size) :
    Triple (block repr p (values.map (Cell.shared depth)).toList)
      (fun s (_ : Unit) s' => Heap.share repr p s = some s')
      (fun _ => block repr p (values.map (Cell.shared (depth + 1))).toList) := by
  apply modify.spec repr p _ _ _ hsize
  intro r bytes hb he
  simp only [Repr.share, hsize, hb, and_self, dite_true, he, Vector.mapM_map,
    Function.comp_def, Cell.share]
  rw [vector_mapM_some]

theorem endShare.spec (repr : Repr ty) (p : RawPtr ty) (values : Vector (Option U8) repr.size)
    (depth : Nat) (hsize : 0 < repr.size) :
    Triple (block repr p (values.map (Cell.shared (depth + 1))).toList)
      (fun s (_ : Unit) s' => Heap.endShare repr p s = some s')
      (fun _ => block repr p (values.map (Cell.shared depth)).toList) := by
  apply modify.spec repr p _ _ _ hsize
  intro r bytes hb he
  simp only [Repr.endShare, hsize, hb, and_self, dite_true, he, Vector.mapM_map,
    Function.comp_def, Cell.endShare]
  rw [vector_mapM_some]

theorem endBorrow.spec (repr : Repr ty) (p : RawPtr ty)
    (data : Vector U8 repr.size) (value : ty) (decoded : repr.decode data = some value)
    (hsize : 0 < repr.size) :
    Triple (block repr p (Vector.replicate repr.size .borrowed).toList)
      (fun s (_ : Unit) s' => Heap.endBorrow repr p value data decoded s = some s')
      (fun _ => pointsTo repr p value) := by
  apply Triple.conseq (fun _ h => h) (fun _ _ h => ⟨data, decoded, h⟩)
  apply modify.spec repr p _ (data.map (Cell.shared 0 ∘ some)) _ hsize
  intro r bytes hb he
  simp only [Repr.endBorrow, hsize, hb, and_self, dite_true, he]
  have hz : (Vector.replicate repr.size (Cell.borrowed : Cell U8)).zip data =
      data.map (fun byte => (Cell.borrowed, byte)) := by
    apply Vector.ext
    intro i hi
    simp
  rw [hz, Vector.mapM_map]
  simp only [Function.comp_def, Cell.endBorrow]
  rw [vector_mapM_some]

theorem borrow_pointsTo.spec (repr : Repr ty) (p : RawPtr ty) (value : ty)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p value)
      (fun s (_ : Unit) s' => Heap.borrow repr p s = some s')
      (fun _ => block repr p (Vector.replicate repr.size .borrowed).toList) := by
  intro h F s ⟨data, _, hp⟩ hd hm hi
  have he : (data.map some).map (fun _ => (Cell.borrowed : Cell U8)) =
      Vector.replicate repr.size .borrowed := by
    apply Vector.ext
    intro i hi
    simp
  have ht := borrow.spec repr p (data.map some) hsize
  apply (Triple.conseq (fun _ hp => hp) (fun _ _ hp => ?_) ht) h F s ?_ hd hm hi
  · simpa [Vector.map_map, Function.comp_def] using hp
  · simpa only [he] using hp

theorem share_pointsTo.spec (repr : Repr ty) (p : RawPtr ty) (value : ty)
    (depth : Nat) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p value depth)
      (fun s (_ : Unit) s' => Heap.share repr p s = some s')
      (fun _ => pointsTo repr p value (depth + 1)) := by
  intro h F s ⟨data, decoded, hp⟩ hd hm hi
  have ht := share.spec repr p (data.map some) depth hsize
  apply (Triple.conseq (fun _ hp => hp)
    (fun _ _ hp => ⟨data, decoded, by simpa [Vector.map_map, Function.comp_def] using hp⟩)
    ht) h F s ?_ hd hm hi
  simpa [Vector.map_map, Function.comp_def] using hp

theorem endShare_pointsTo.spec (repr : Repr ty) (p : RawPtr ty) (value : ty)
    (depth : Nat) (hsize : 0 < repr.size) :
    Triple (pointsTo repr p value (depth + 1))
      (fun s (_ : Unit) s' => Heap.endShare repr p s = some s')
      (fun _ => pointsTo repr p value depth) := by
  intro h F s ⟨data, decoded, hp⟩ hd hm hi
  have ht := endShare.spec repr p (data.map some) depth hsize
  apply (Triple.conseq (fun _ hp => hp)
    (fun _ _ hp => ⟨data, decoded, by simpa [Vector.map_map, Function.comp_def] using hp⟩)
    ht) h F s ?_ hd hm hi
  simpa [Vector.map_map, Function.comp_def] using hp

/-- Cleanup authority supplies the extent even when no byte cells are owned. -/
theorem offset.spec (repr : Repr ty) (p : RawPtr ty) (count : Int) (length : Nat)
    (own : Bool) (_hsize : 0 < repr.size) (hstart : p.byteOffset.val ≤ length * repr.size)
    (hlo : 0 ≤ (p.byteOffset.val : Int) + count * repr.size)
    (hhi : (p.byteOffset.val : Int) + count * repr.size ≤ length * repr.size)
    (hfit : (p.byteOffset.val : Int) + count * repr.size < (2 ^ UScalarTy.numBits .Usize : Nat)) :
    Triple (alloc repr ⟨p.base, ⟨0⟩⟩ length own) (State.offset repr p count)
      (fun q h => q.base = p.base ∧ (q.byteOffset.val : Int) = (p.byteOffset.val : Int) + count * repr.size ∧
        alloc repr ⟨p.base, ⟨0⟩⟩ length own h) := by
  rintro h F s ⟨_, rfl⟩ hd hm hi
  obtain ⟨blk, hl, hn, _, _⟩ :=
    ((Fragment.matches_union _ _ _).mp hm).1 _ rfl
  let q : RawPtr ty := ⟨p.base, ⟨BitVec.ofNat _ ((p.byteOffset.val : Int) + count * repr.size).toNat⟩⟩
  have hq : (q.byteOffset.val : Int) = (p.byteOffset.val : Int) + count * repr.size := by
    have ht : ((p.byteOffset.val : Int) + count * repr.size).toNat < 2 ^ UScalarTy.numBits .Usize := by
      grind
    change ((BitVec.ofNat (UScalarTy.numBits .Usize)
      ((p.byteOffset.val : Int) + count * repr.size).toNat).toNat : Int) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht]
    exact Int.toNat_of_nonneg hlo
  have hr : Heap.offset repr p count s = some q := by
    have hf : (p.byteOffset.val : Int) + count * repr.size < (2 : Int) ^ UScalarTy.numBits .Usize := by
      simpa using hfit
    simp [Heap.offset, hl, hn, hstart, hlo, hhi, hf, q]
  refine ⟨⟨q, s, hr, rfl⟩, ?_⟩
  rintro result s' ⟨hs, rfl⟩
  have he := Option.some.inj (hs.symm.trans hr)
  subst result
  exact ⟨_, hd, hm, hi, rfl, hq, rfl, rfl⟩

end Aeneas.Std.SepLogic
