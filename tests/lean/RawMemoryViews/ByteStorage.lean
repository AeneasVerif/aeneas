module

public import RawMemoryViews.ByteFill
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Model

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic

namespace raw_memory_views

def byteVectorRepr (n : Nat) : Aeneas.Std.Repr (Vector U8 n) where
  size := n
  align := ⟨1, 0, rfl⟩
  aligned := by simp
  decode bytes := bytes.mapM Aeneas.Std.Byte.numeric
  encode values bytes := bytes = values.map Aeneas.Std.Byte.data
  encode_complete _ := ⟨_, rfl⟩
  encode_decode values bytes encoded := by
    subst bytes
    exact raw_box.dataBytes_numeric values
  decode_mono bytes bytes' values decoded agree := by
    have same := raw_box.numericBytes_eq bytes bytes' values decoded agree
    simpa only [same] using decoded
  encode_valid values bytes i encoded := by
    subst bytes
    simp

theorem byteVectorRepr_noPointers (values : Vector U8 n) (p : RawPtr Unit) :
    ¬ (byteVectorRepr n).Carries values p := by
  rintro ⟨bytes, encoded, i, lane, hp⟩
  change bytes = values.map Aeneas.Std.Byte.data at encoded
  subst bytes
  have impossible := (Vector.getElem_map Aeneas.Std.Byte.data (xs := values) i.isLt).symm.trans hp
  cases impossible

theorem byteVectorRepr_calibrated (values : Vector U8 n) (bytes : Vector Aeneas.Std.Byte n)
    (decoded : (byteVectorRepr n).decode bytes = some values)
    (carried : ∀ i : Fin n, ∀ q lane,
      bytes[i.val] = .pointer q lane → (byteVectorRepr n).Carries values q) :
    (byteVectorRepr n).encode values bytes := by
  change bytes.mapM Aeneas.Std.Byte.numeric = some values at decoded
  have data : ∀ i : Fin n, ∃ value, bytes[i.val] = Aeneas.Std.Byte.data value := by
    intro i
    obtain ⟨value, hv⟩ := vector_mapM_enabled decoded i.val i.isLt
    cases hb : bytes[i.val]
    · simp [hb, Aeneas.Std.Byte.numeric] at hv
    · exact ⟨_, rfl⟩
    · rename_i q lane
      exact (byteVectorRepr_noPointers values q (carried i q lane hb)).elim
  classical
  let numeric := Vector.ofFn fun i => (data i).choose
  have same : bytes = numeric.map Aeneas.Std.Byte.data := by
    apply Vector.ext
    intro i hi
    simpa [numeric] using (data ⟨i, hi⟩).choose_spec
  rw [same, raw_box.dataBytes_numeric] at decoded
  exact (Option.some.inj decoded) ▸ same

theorem byteVector_pointsTo (p : RawPtr (Vector U8 n)) (base : BasePtr)
    (values : Vector U8 n) (h : Fragment) :
    pointsTo (byteVectorRepr n) p base values 0 h ↔
      writableBytes (p.cast U8) base (values.map Aeneas.Std.Byte.data) h := by
  constructor
  · rintro ⟨bytes, encoded, lower, aligned, cells⟩
    change bytes = values.map Aeneas.Std.Byte.data at encoded
    subst bytes
    exact ⟨lower, aligned, cells⟩
  · rintro ⟨lower, aligned, cells⟩
    exact ⟨_, rfl, lower, aligned, cells⟩

theorem u8_cells (values : Vector U8 n) (depth : Nat) :
    ((values.map (fun x => #v[Aeneas.Std.Byte.data x])).flatMap
      (fun data => data.map (Cell.shared depth))).toList =
      ((values.map Aeneas.Std.Byte.data).map (Cell.shared depth)).toList := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [Vector.getElem_toList]
    rw [Vector.getElem_flatMap]
    simp

theorem u8_range (p : RawPtr U8) (base : BasePtr) (values : Vector U8 n)
    (depth : Nat) (h : Fragment) :
    pointsToRange Aeneas.Std.Repr.u8 p base values depth h ↔
      block Aeneas.Std.Repr.u8 p base
        ((values.map Aeneas.Std.Byte.data).map (Cell.shared depth)).toList h := by
  constructor
  · rintro ⟨data, encoded, lower, aligned, cells⟩
    have eq : data = values.map (fun x => #v[Aeneas.Std.Byte.data x]) := by
      apply Vector.ext
      intro i hi
      simpa [Aeneas.Std.Repr.u8] using encoded ⟨i, hi⟩
    subst data
    erw [u8_cells] at cells
    exact ⟨lower, aligned, cells⟩
  · intro cells
    refine ⟨values.map (fun x => #v[Aeneas.Std.Byte.data x]), ?_, ?_⟩
    · intro i
      simp [Aeneas.Std.Repr.u8]
    · erw [u8_cells]
      exact cells

/-- Heap validity already bounds every issued byte's numerical address. -/
theorem writableBytes_fits (p : RawPtr U8) (base : BasePtr)
    (bytes : Vector Aeneas.Std.Byte n) (h : Fragment) (s : Heap)
    (hp : writableBytes p base bytes h) (hm : Fragment.Matches s h) (hi : s.Inv)
    (j : Nat) (hj : j < n) :
    p.address.val + j < 2 ^ UScalarTy.numBits .Usize := by
  obtain ⟨lower, _, cells⟩ := hp
  rw [cells] at hm
  obtain ⟨blk, lookup, _, baseEq, byte⟩ := matches_cellsHeap.mp hm j (by simpa using hj)
  have within := List.getElem?_eq_some_iff.mp byte
  have valid := hi.validBlock lookup
  simp only [Heap.validBlock, Bool.and_eq_true] at valid
  have bounded := valid.1.1
  simp only [Heap.bounded, Bool.and_eq_true, decide_eq_true_eq] at bounded
  simp only [RawPtr.offsetFrom] at within
  rw [baseEq] at bounded
  agrind

end raw_memory_views
