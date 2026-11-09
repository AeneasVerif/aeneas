module

public import Aeneas.SepLogic.Ranges
public import Aeneas.SepLogic.Local
import all Aeneas.Std.Heap.Model
import all Aeneas.Std.Heap.Repr
import all Aeneas.Std.Core.Ptr

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.Bytes

namespace Aeneas.Std

open Aeneas.SepLogic

set_option maxHeartbeats 1000000

theorem readableRange_bound (repr : Repr T) (p : RawPtr T) (base : BasePtr)
    (values : Vector T count) (depth : Nat) (hcount : 0 < count) (hsize : 0 < repr.size)
    (h : Fragment) (s : Heap) (hp : readableRange repr p base values depth h)
    (hm : Fragment.Matches s h) (hi : s.Inv) :
    p.address.val + count * repr.size < 2 ^ UScalarTy.numBits .Usize := by
  obtain ⟨data, _, hlo, _, rfl⟩ := hp
  obtain ⟨blk, hb, hl, _, hbase, _⟩ :=
    bytes_of_matches (repr := repr.region count) (p := p.cast Unit)
      (data := data.flatMap (fun b => b.map (Cell.shared depth)))
      (Nat.mul_pos hcount hsize) hm
  have bounded := hi.validBlock hl
  simp only [Heap.validBlock, Bool.and_eq_true] at bounded
  have upper : blk.bptr.val + blk.repr.length < 2 ^ UScalarTy.numBits .Usize := by
    have bounds : 0 < blk.bptr.val ∧
        blk.bptr.val + blk.repr.length < 2 ^ UScalarTy.numBits .Usize := by
      simpa [Heap.bounded] using bounded.1.1
    exact bounds.2
  change p.offsetFrom base + count * repr.size ≤ blk.repr.length at hb
  simp only [RawPtr.offsetFrom] at hb
  agrind

theorem read_range_element {T : Type} {s : Heap} {repr : Aeneas.Std.Repr T}
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
