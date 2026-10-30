module

public import Aeneas.Std.Heap.Resources
public import Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Separation
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap

/-! Framed contracts for the executable read/write operations. -/

@[expose] public section

namespace Aeneas.Std.SepLogic

theorem modify.spec (repr : Repr ty) (p : RawPtr ty)
    (old new : Vector (Cell U8) repr.size)
    (change : ∀ {r}, Vector (Cell U8) r → Option (Vector (Cell U8) r))
    (hsize : 0 < repr.size)
    (hc : ∀ {r} (bytes : Vector (Cell U8) r) (hb : (p.byteOffset.val + repr.size) ≤ r),
      repr.select bytes p.byteOffset.val hb = old →
      change bytes = some (repr.update bytes p.byteOffset.val hb new)) :
    Triple (block repr p old.toList)
      (fun s (_ : Unit) s' => Heap.modify repr p change s = some s')
      (fun _ => block repr p new.toList) := by
  rintro h F s ⟨hpa, rfl⟩ hd hm hi
  obtain ⟨blk, hb, hl, ha, hs⟩ :=
    bytes_of_matches hsize ((Fragment.matches_union _ _ _).mp hm).1
  have hrun := Heap.modify.spec repr p change s blk _ hl ha hpa (hc blk.bytes hb hs)
  refine ⟨⟨(), _, hrun⟩, ?_⟩
  rintro _ s' he
  have he := Option.some.inj (hrun.symm.trans he)
  subst s'
  exact ⟨_, disjoint_cellsHeap_congr (by simp) hd,
    (Fragment.matches_union _ _ _).mpr ⟨matches_update hl ha hb _, matches_update_frame hl hb hd
      ((Fragment.matches_union _ _ _).mp hm).2⟩, hi.storeRepr _ _, hpa, rfl⟩

theorem read.spec (repr : Repr ty) (p : RawPtr ty) (value : ty) (depth : Nat)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p value depth) (State.read repr p)
      (fun x h => x = value ∧ pointsTo repr p value depth h) := by
  intro h F s hp hd hm hi
  have hr := read_of_pointsTo hsize hp ((Fragment.matches_union _ _ _).mp hm).1
  refine ⟨⟨value, s, hr, rfl⟩, ?_⟩
  rintro x s' ⟨hx, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hx.symm.trans hr), hp⟩

theorem write.spec (repr : Repr ty) (p : RawPtr ty) (old : Vector (Option U8) repr.size)
    (value : ty) (hsize : 0 < repr.size) :
    Triple (block repr p (old.map (Cell.shared 0)).toList) (State.write repr p value)
      (fun _ => pointsTo repr p value) := by
  rintro h F s ⟨hpa, rfl⟩ hd hm hi
  obtain ⟨block, hb, hl, ha, hs⟩ :=
    bytes_of_matches hsize ((Fragment.matches_union _ _ _).mp hm).1
  obtain ⟨encoding, decoded⟩ := repr.complete value
  have hwrite (data : Vector U8 repr.size) (hdata : repr.decode data = some value) :
      Heap.write repr p value data hdata s =
        some (s.storeRepr p.base
          (repr.update block.bytes p.byteOffset.val hb (data.map (Cell.shared 0 ∘ some))).toList) := by
    apply Heap.modify.spec repr p _ s block _ hl ha hpa
    simp [Repr.write, hsize, hb, hs, Repr.writeBytes_shared]
  refine ⟨⟨(), _, encoding, decoded, hwrite encoding decoded⟩, ?_⟩
  rintro _ s' ⟨data, hdata, hrun⟩
  have he := Option.some.inj ((hwrite data hdata).symm.trans hrun)
  subst s'
  refine ⟨_, disjoint_cellsHeap_congr (by simp) hd,
    (Fragment.matches_union _ _ _).mpr ⟨matches_update hl ha hb _, matches_update_frame hl hb hd
      ((Fragment.matches_union _ _ _).mp hm).2⟩, hi.storeRepr _ _, data, hdata, hpa, rfl⟩

theorem write_pointsTo.spec (repr : Repr ty) (p : RawPtr ty) (old value : ty)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p old) (State.write repr p value)
      (fun _ => pointsTo repr p value) := by
  intro h F s ⟨data, _, hp⟩ hd hm hi
  have hh := write.spec repr p (data.map some) value hsize
  apply hh h F s ?_ hd hm hi
  simpa [Vector.map_map, Function.comp_def] using hp

/-- Any chosen encoding of `value` can be written; enabling does not depend
on which valid encoding was chosen. -/
theorem write_encoding.spec (repr : Repr ty) (p : RawPtr ty) (old value : ty)
    (data : Vector U8 repr.size) (decoded : repr.decode data = some value)
    (hsize : 0 < repr.size) :
    Triple (pointsTo repr p old)
      (fun s (_ : Unit) s' => Heap.write repr p value data decoded s = some s')
      (fun _ => pointsTo repr p value) := by
  intro h F s ⟨bytes, _, hp⟩ hd hm hi
  apply (Triple.conseq (fun _ h => h) (fun _ _ h => ⟨data, decoded, h⟩)
    (modify.spec repr p (bytes.map (Cell.shared 0 ∘ some))
      (data.map (Cell.shared 0 ∘ some))
      (fun bytes => repr.write bytes p.byteOffset.val value data decoded) hsize ?_)) h F s hp hd hm hi
  intro r contents hb he
  have hw : Repr.writeBytes repr.size (bytes.map (Cell.shared 0 ∘ some)) data =
      some (data.map (Cell.shared 0 ∘ some)) := by
    simpa only [Vector.map_map] using Repr.writeBytes_shared (bytes.map some) data
  simp [Repr.write, hsize, hb, he, hw]

end Aeneas.Std.SepLogic
