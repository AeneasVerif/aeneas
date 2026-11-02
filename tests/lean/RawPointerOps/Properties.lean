module

public import RawPointerOps.Funs
public import Aeneas.Std.Heap.PointerOps
public import Aeneas.Std.Heap.PointerMovement
import all RawPointerOps.Funs
import all RawPointerOps.FunsExternal
import all RawBoxProofs
import all RawValueCasts.Repr
import all Aeneas.Std.Heap.Separation

@[expose] public section

open Aeneas.Std Aeneas.Std.SepLogic

namespace raw_pointer_ops

theorem initialize_word.spec (p : MutRawPtr U32) (value : U32)
    (old : Vector (Option U8) 4) :
    HeapWP.Triple (block raw_box.u32Repr p (old.map (Cell.shared 0)).toList)
      (initialize_word p value)
      (fun result h => result = value ∧ pointsTo raw_box.u32Repr p value 0 h) := by
  unfold initialize_word ext.write_word ext.read_word
  apply HeapWP.Triple.bind (HeapWP.write_writable.spec raw_box.u32Repr p old value (by decide))
  intro _
  exact HeapWP.read.spec raw_box.u32Repr p value 0 (by decide)

theorem initialize_flag.spec (p : MutRawPtr Bool) (value : Bool)
    (old : Vector (Option U8) 1) :
    HeapWP.Triple (block raw_value_casts.boolRepr p (old.map (Cell.shared 0)).toList)
      (initialize_flag p value)
      (fun result h => result = value ∧ pointsTo raw_value_casts.boolRepr p value 0 h) := by
  unfold initialize_flag ext.write_flag ext.read_flag
  apply HeapWP.Triple.bind
    (HeapWP.write_writable.spec raw_value_casts.boolRepr p old value (by decide))
  intro _
  exact HeapWP.read.spec raw_value_casts.boolRepr p value 0 (by decide)

/-- No prior Boolean validity is assumed: the old byte is the invalid encoding two. -/
theorem initialize_invalid_flag.spec (p : MutRawPtr Bool) (value : Bool) :
    HeapWP.Triple (block raw_value_casts.boolRepr p [.shared 0 (some 2#u8)])
      (initialize_flag p value)
      (fun result h => result = value ∧ pointsTo raw_value_casts.boolRepr p value 0 h) := by
  simpa using initialize_flag.spec p value #v[some 2#u8]

theorem replace_word.spec (p : MutRawPtr U32) (old value : U32) :
    HeapWP.Triple (pointsTo raw_box.u32Repr p old) (replace_word p value)
      (fun result h => result = old ∧ pointsTo raw_box.u32Repr p value 0 h) :=
  HeapWP.replace.spec raw_box.u32Repr p old value (by decide)

theorem swap_words.spec (p q : MutRawPtr U32) (left right : U32) :
    HeapWP.Triple (sep (pointsTo raw_box.u32Repr p left) (pointsTo raw_box.u32Repr q right))
      (swap_words p q)
      (fun _ => sep (pointsTo raw_box.u32Repr p right) (pointsTo raw_box.u32Repr q left)) :=
  HeapWP.swap.spec raw_box.u32Repr p q left right (by decide)

theorem swap_self.spec (p : MutRawPtr U32) (value : U32) :
    HeapWP.Triple (pointsTo raw_box.u32Repr p value) (swap_self p)
      (fun _ => pointsTo raw_box.u32Repr p value) :=
  HeapWP.swap_same.spec raw_box.u32Repr p value (by decide)

theorem read_unaligned_word.spec (p : MutRawPtr U32) (value : U32) (depth : Nat) :
    HeapWP.Triple (pointsTo raw_box.u32Repr.unaligned p value depth) (read_unaligned_word p)
      (fun result h => result = value ∧ pointsTo raw_box.u32Repr.unaligned p value depth h) :=
  HeapWP.read_unaligned.spec raw_box.u32Repr p value depth (by decide)

theorem write_unaligned_word.spec (p : MutRawPtr U32) (old : Vector (Option U8) 4) (value : U32) :
    HeapWP.Triple (block raw_box.u32Repr.unaligned p (old.map (Cell.shared 0)).toList)
      (write_unaligned_word p value) (fun _ => pointsTo raw_box.u32Repr.unaligned p value) :=
  HeapWP.write_unaligned.spec raw_box.u32Repr p old value (by decide)

theorem byte_advance.spec (p : MutRawPtr U32) (count : Usize) (length : Nat) (own : Bool)
    (hstart : p.byteOffset.val ≤ length * 4) (hhi : p.byteOffset.val + count.val ≤ length * 4)
    (hfit : p.byteOffset.val + count.val < 2 ^ UScalarTy.numBits .Usize)
    (hcount : (count.val : Int) ≤ IScalar.cMax .Isize) :
    HeapWP.Triple (alloc raw_box.u32Repr ⟨p.provenance, ⟨0⟩⟩ length own) (byte_advance p count)
      (fun result h => result.provenance = p.provenance ∧ result.byteOffset.val = p.byteOffset.val + count.val ∧
        alloc raw_box.u32Repr ⟨p.provenance, ⟨0⟩⟩ length own h) :=
  HeapWP.byte_add.spec raw_box.u32Repr p count length own hstart hhi hfit hcount

theorem byte_shift.spec (p : MutRawPtr U32) (count : Isize) (length : Nat) (own : Bool)
    (hstart : p.byteOffset.val ≤ length * 4) (hlo : 0 ≤ (p.byteOffset.val : Int) + count.val)
    (hhi : (p.byteOffset.val : Int) + count.val ≤ length * 4)
    (hfit : (p.byteOffset.val : Int) + count.val < (2 ^ UScalarTy.numBits .Usize : Nat)) :
    HeapWP.Triple (alloc raw_box.u32Repr ⟨p.provenance, ⟨0⟩⟩ length own) (byte_shift p count)
      (fun result h => result.provenance = p.provenance ∧
        (result.byteOffset.val : Int) = (p.byteOffset.val : Int) + count.val ∧
        alloc raw_box.u32Repr ⟨p.provenance, ⟨0⟩⟩ length own h) :=
  HeapWP.byte_offset.spec raw_box.u32Repr p count length own hstart hlo hhi hfit

theorem word_distance.spec (p origin : MutRawPtr U32) (length : Nat) (own : Bool)
    (hbase : p.provenance = origin.provenance) (hp : p.byteOffset.val ≤ length * 4)
    (ho : origin.byteOffset.val ≤ length * 4)
    (hdiv : ((p.byteOffset.val : Int) - origin.byteOffset.val) % 4 = 0)
    (hbytes : IScalar.cMin .Isize ≤ (p.byteOffset.val : Int) - origin.byteOffset.val ∧
      (p.byteOffset.val : Int) - origin.byteOffset.val ≤ IScalar.cMax .Isize)
    (hcount : IScalar.cMin .Isize ≤ ((p.byteOffset.val : Int) - origin.byteOffset.val) / 4 ∧
      ((p.byteOffset.val : Int) - origin.byteOffset.val) / 4 ≤ IScalar.cMax .Isize) :
    HeapWP.Triple (alloc raw_box.u32Repr ⟨p.provenance, ⟨0⟩⟩ length own) (word_distance p origin)
      (fun result h => result.val = ((p.byteOffset.val : Int) - origin.byteOffset.val) / 4 ∧
        result.val * 4 = (p.byteOffset.val : Int) - origin.byteOffset.val ∧
        alloc raw_box.u32Repr ⟨p.provenance, ⟨0⟩⟩ length own h) :=
  HeapWP.offset_from.spec raw_box.u32Repr p origin length own (by decide) hbase hp ho hdiv hbytes hcount

theorem fill_words.spec (p : MutRawPtr U32) (count : Usize) (value : U32)
    (old : Vector U32 count.val) (hcount : 0 < count.val) :
    HeapWP.Triple (pointsToRange raw_box.u32Repr p old) (fill_words p count value)
      (fun _ => pointsToRange raw_box.u32Repr p (Vector.replicate count.val value)) := by
  unfold fill_words ext.fill_words
  apply HeapWP.Triple.bind (HeapWP.borrowRange.spec raw_box.u32Repr p old hcount (by decide))
  intro values
  apply HeapWP.Triple.pure_pre
  intro _
  exact HeapWP.endBorrowRange.spec raw_box.u32Repr p (Vector.replicate count.val value)
    hcount (by decide)

end raw_pointer_ops
