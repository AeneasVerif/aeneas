module

public import Aeneas.Std.Heap.Ranges
import all Aeneas.Std.Heap.Resources
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Core.Ptr

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic

namespace raw_scale

set_option maxHeartbeats 1000000

/- Read-only exposure can retain symbolic pointer bytes with the same numeric
   decoding. Such bytes need not be an admissible encoding for a scalar write. -/
def readableRange (repr : Aeneas.Std.Repr T) (p : RawPtr T) (base : BasePtr)
    (values : Vector T count) (depth : Nat) : Assertion :=
  fun h => ∃ data : Vector (Vector Aeneas.Std.Byte repr.size) count,
    (∀ i : Fin count, repr.decode data[i.val] = some values[i.val]) ∧
    block repr p base
      (data.flatMap (fun bytes => bytes.map (Cell.shared depth))).toList h

theorem pointsToRange_readable {repr : Aeneas.Std.Repr T} {p : RawPtr T}
    {base : BasePtr} {values : Vector T count} {depth : Nat} {h : Fragment}
    (hp : pointsToRange repr p base values depth h) :
    readableRange repr p base values depth h := by
  obtain ⟨data, encoded, rest⟩ := hp
  exact ⟨data, fun i => repr.encode_decode _ _ (encoded i), rest⟩

private theorem read_range_element {T : Type} {s : Heap} {repr : Aeneas.Std.Repr T}
    {p q : RawPtr T} {base : BasePtr} {values : Vector T count} {depth : Nat}
    {h : Fragment} (i : Fin count) (hsize : 0 < repr.size)
    (hprov : q.provenance = p.provenance)
    (haddr : q.address.val = p.address.val + i.val * repr.size)
    (hp : readableRange repr p base values depth h) (hm : Fragment.Matches s h) :
    Heap.read repr q s = some values[i.val] := by
  obtain ⟨data, encoded, hlo, aligned, rfl⟩ := hp
  obtain ⟨blk, hb, hl, hlive, hbase, selected⟩ :=
    bytes_of_matches (repr := repr.region count) (p := p.cast Unit)
      (data := data.flatMap (fun bytes => bytes.map (Cell.shared depth)))
      (Nat.mul_pos (by agrind) hsize) hm
  change p.offsetFrom base + count * repr.size ≤ blk.repr.length at hb
  change s.allocations p.provenance = some blk at hl
  have hsel := repr.select_region blk.bytes (p.offsetFrom base) count
    (data.map fun bytes => bytes.map (Cell.shared depth)) hb
    (by simpa [Vector.flatMap_map, Repr.region, RawPtr.cast, RawPtr.offsetFrom] using selected)
    i.val i.isLt
  simp only [Vector.getElem_map] at hsel
  have hoff : q.offsetFrom base = p.offsetFrom base + i.val * repr.size := by
    simp only [RawPtr.offsetFrom]
    agrind
  have halign : repr.align.val ∣ q.address.val := by
    rw [haddr]
    exact Nat.dvd_add aligned (repr.aligned_stride i.val)
  have hlow : base.val ≤ q.address.val := by agrind
  simp [Heap.read, hprov, hl, hlive, hbase, hlow, halign, hoff, Repr.read,
    hsize, range_element_bound i.isLt hb, hsel, Repr.readBytes_shared,
    encoded i]

theorem read_range_with.spec {T : Type} (repr : Aeneas.Std.Repr T)
    (p q : RawPtr T) (base : BasePtr) (values : Vector T count) (depth : Nat)
    (P : Assertion) (view : ∀ h, P h → readableRange repr p base values depth h)
    (i : Fin count) (hsize : 0 < repr.size)
    (hprov : q.provenance = p.provenance)
    (haddr : q.address.val = p.address.val + i.val * repr.size) :
    HeapWP.Triple P (RawPtr.read repr q) (fun result h => result = values[i.val] ∧ P h) := by
  apply HeapWP.Triple.checkedModify
  intro h F s hp hd hm hi
  have hr := read_range_element i hsize hprov haddr (view h hp)
    ((Fragment.matches_union _ _ _).mp hm).1
  refine ⟨⟨values[i.val], s, hr, rfl⟩, ?_⟩
  rintro result s' ⟨hv, rfl⟩
  exact ⟨h, hd, hm, hi, Option.some.inj (hv.symm.trans hr), hp⟩

/-- Reading an interior element preserves the complete range and any frame.
    No allocation-cleanup ownership or distinct-allocation premise is needed. -/
theorem read_range.spec {T : Type} (repr : Aeneas.Std.Repr T)
    (p q : RawPtr T) (base : BasePtr) (values : Vector T count) (depth : Nat)
    (i : Fin count) (hsize : 0 < repr.size)
    (hprov : q.provenance = p.provenance)
    (haddr : q.address.val = p.address.val + i.val * repr.size) :
    HeapWP.Triple (pointsToRange repr p base values depth) (RawPtr.read repr q)
      (fun result h => result = values[i.val] ∧ pointsToRange repr p base values depth h) :=
  read_range_with.spec repr p q base values depth _ (fun _ => pointsToRange_readable)
    i hsize hprov haddr

theorem add_range_with.spec {T : Type} (repr : Aeneas.Std.Repr T)
    (p : RawPtr T) (base : BasePtr) (values : Vector T count) (depth : Nat)
    (P : Assertion) (view : ∀ h, P h → readableRange repr p base values depth h)
    (i : Usize) (hcount : 0 < count) (hsize : 0 < repr.size) (hle : i.val ≤ count)
    (hfit : p.address.val + i.val * repr.size < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Triple P (RawPtr.add repr p i)
      (fun result h => result.provenance = p.provenance ∧
        result.address.val = p.address.val + i.val * repr.size ∧
        P h) := by
  apply HeapWP.Triple.checkedModify
  intro h F s hp hd hm hi
  have keep := hp
  obtain ⟨data, _, hlo, _, cells⟩ := view h hp
  have localMatch := ((Fragment.matches_union _ _ _).mp hm).1
  rw [cells] at localMatch
  obtain ⟨blk, hb, hl, hlive, hbase, _⟩ :=
    bytes_of_matches (repr := repr.region count) (p := p.cast Unit)
      (data := data.flatMap (fun bytes => bytes.map (Cell.shared depth)))
      (Nat.mul_pos hcount hsize) localMatch
  change p.offsetFrom base + count * repr.size ≤ blk.repr.length at hb
  change s.allocations p.provenance = some blk at hl
  have htarget : p.address.val + i.val * repr.size ≤ base.val + blk.repr.length := by
    have hmul := Nat.mul_le_mul_right repr.size hle
    simp only [RawPtr.offsetFrom] at hb
    agrind
  have hstart : p.address.val ≤ base.val + blk.repr.length := by agrind
  have hlo' : (base.val : Int) ≤ (p.address.val : Int) + i.val * repr.size := by agrind
  have hhi' : (p.address.val : Int) + i.val * repr.size ≤ base.val + blk.repr.length := by
    exact_mod_cast htarget
  have hfit' : (p.address.val : Int) + i.val * repr.size <
      (2 ^ UScalarTy.numBits .Usize : Nat) := by exact_mod_cast hfit
  let result : RawPtr T := ⟨p.provenance,
    ⟨BitVec.ofNat _ (p.address.val + i.val * repr.size)⟩⟩
  have hval : result.address.val = p.address.val + i.val * repr.size := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  have hrun : Heap.offset repr p i.val s = some result := by
    have hf : (p.address.val : Int) + i.val * repr.size <
        (2 : Int) ^ System.Platform.numBits := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat, UScalarTy.Usize_numBits_eq] using hfit'
    have target_nat : ((p.address.val : Int) + i.val * repr.size).toNat =
        p.address.val + i.val * repr.size := by
      exact_mod_cast Int.toNat_natCast (p.address.val + i.val * repr.size)
    simp [Heap.offset, hl, hlive, hbase, hlo, hstart, hlo', hhi', hf, target_nat, result]
  refine ⟨⟨result, s, hrun, rfl⟩, ?_⟩
  rintro answer s' ⟨he, rfl⟩
  have he := Option.some.inj (he.symm.trans hrun)
  subst answer
  exact ⟨h, hd, hm, hi, rfl, hval, keep⟩

/-- Range ownership suffices for pointer arithmetic, including one-past pointers.
    In particular, two disjoint ranges may share a single allocation. -/
theorem add_range.spec {T : Type} (repr : Aeneas.Std.Repr T)
    (p : RawPtr T) (base : BasePtr) (values : Vector T count) (depth : Nat)
    (i : Usize) (hcount : 0 < count) (hsize : 0 < repr.size) (hle : i.val ≤ count)
    (hfit : p.address.val + i.val * repr.size < 2 ^ UScalarTy.numBits .Usize) :
    HeapWP.Triple (pointsToRange repr p base values depth) (RawPtr.add repr p i)
      (fun result h => result.provenance = p.provenance ∧
        result.address.val = p.address.val + i.val * repr.size ∧
        pointsToRange repr p base values depth h) :=
  add_range_with.spec repr p base values depth _ (fun _ => pointsToRange_readable)
    i hcount hsize hle hfit

end raw_scale
