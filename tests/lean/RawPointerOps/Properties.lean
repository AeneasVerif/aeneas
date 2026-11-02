module

public import RawPointerOps.Funs
public import Aeneas.Std.Heap.PointerOps
public import Aeneas.Std.Heap.PointerMovement
public import Aeneas.Std.Heap.RangeRestoration
import all RawPointerOps.Funs
import all RawPointerOps.FunsExternal
import all RawBoxProofs
import all RawValueCasts.Repr
import all Aeneas.Std.Heap.Separation

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.SepLogic

namespace raw_pointer_ops

theorem initialize_word.spec (p : MutRawPtr U32) (bptr : BasePtr) (value : U32)
    (old : Vector Aeneas.Std.Byte 4) :
    HeapWP.Triple (block raw_box.u32Repr p bptr (old.map (Cell.shared 0)).toList)
      (initialize_word p value)
      (fun result h => result = value ∧ pointsTo raw_box.u32Repr p bptr value 0 h) := by
  unfold initialize_word ext.write_word ext.read_word
  apply HeapWP.Triple.bind (HeapWP.write_writable.spec raw_box.u32Repr p bptr old value
    (raw_box.u32Repr_noPointers value) (by decide))
  intro _
  exact HeapWP.read.spec raw_box.u32Repr p bptr value 0 (by decide)

theorem initialize_flag.spec (p : MutRawPtr Bool) (bptr : BasePtr) (value : Bool)
    (old : Vector Aeneas.Std.Byte 1) :
    HeapWP.Triple (block raw_value_casts.boolRepr p bptr (old.map (Cell.shared 0)).toList)
      (initialize_flag p value)
      (fun result h => result = value ∧ pointsTo raw_value_casts.boolRepr p bptr value 0 h) := by
  unfold initialize_flag ext.write_flag ext.read_flag
  apply HeapWP.Triple.bind
    (HeapWP.write_writable.spec raw_value_casts.boolRepr p bptr old value
      (raw_value_casts.boolRepr_noPointers value) (by decide))
  intro _
  exact HeapWP.read.spec raw_value_casts.boolRepr p bptr value 0 (by decide)

/-- No prior Boolean validity is assumed: the old byte is the invalid encoding two. -/
theorem initialize_invalid_flag.spec (p : MutRawPtr Bool) (bptr : BasePtr) (value : Bool) :
    HeapWP.Triple (block raw_value_casts.boolRepr p bptr [.shared 0 (.data 2#u8)])
      (initialize_flag p value)
      (fun result h => result = value ∧ pointsTo raw_value_casts.boolRepr p bptr value 0 h) := by
  simpa using initialize_flag.spec p bptr value #v[.data 2#u8]

theorem replace_word.spec (p : MutRawPtr U32) (bptr : BasePtr) (old value : U32) :
    HeapWP.Triple (pointsTo raw_box.u32Repr p bptr old) (replace_word p value)
      (fun result h => result = old ∧ pointsTo raw_box.u32Repr p bptr value 0 h) :=
  HeapWP.replace.spec raw_box.u32Repr p bptr old value (raw_box.u32Repr_noPointers value) (by decide)

theorem swap_words.spec (p q : MutRawPtr U32) (a b : BasePtr) (left right : U32) :
    HeapWP.Triple (sep (pointsTo raw_box.u32Repr p a left) (pointsTo raw_box.u32Repr q b right))
      (swap_words p q)
      (fun _ => sep (pointsTo raw_box.u32Repr p a right) (pointsTo raw_box.u32Repr q b left)) :=
  HeapWP.swap.spec raw_box.u32Repr p q a b left right (by decide)

theorem swap_self.spec (p : MutRawPtr U32) (bptr : BasePtr) (value : U32) :
    HeapWP.Triple (pointsTo raw_box.u32Repr p bptr value) (swap_self p)
      (fun _ => pointsTo raw_box.u32Repr p bptr value) :=
  HeapWP.swap_same.spec raw_box.u32Repr p bptr value (by decide)

theorem read_unaligned_word.spec (p : MutRawPtr U32) (bptr : BasePtr) (value : U32) (depth : Nat) :
    HeapWP.Triple (pointsTo raw_box.u32Repr.unaligned p bptr value depth) (read_unaligned_word p)
      (fun result h => result = value ∧ pointsTo raw_box.u32Repr.unaligned p bptr value depth h) :=
  HeapWP.read_unaligned.spec raw_box.u32Repr p bptr value depth (by decide)

theorem write_unaligned_word.spec (p : MutRawPtr U32) (bptr : BasePtr)
    (old : Vector Aeneas.Std.Byte 4) (value : U32) :
    HeapWP.Triple (block raw_box.u32Repr.unaligned p bptr (old.map (Cell.shared 0)).toList)
      (write_unaligned_word p value) (fun _ => pointsTo raw_box.u32Repr.unaligned p bptr value) :=
  HeapWP.write_unaligned.spec raw_box.u32Repr p bptr old value
    (raw_box.u32Repr_noPointers value) (by decide)

theorem byte_advance.spec (p : MutRawPtr U32) (bptr : BasePtr) (count : Usize) (length : Nat) (own : Bool)
    (hstart : bptr.val ≤ p.address.val ∧ p.address.val ≤ bptr.val + length * 4)
    (hhi : p.address.val + count.val ≤ bptr.val + length * 4)
    (hfit : p.address.val + count.val < 2 ^ UScalarTy.numBits .Usize)
    (hcount : (count.val : Int) ≤ IScalar.cMax .Isize) :
    HeapWP.Triple (alloc raw_box.u32Repr ⟨p.provenance, bptr⟩ bptr length own) (byte_advance p count)
      (fun result h => result.provenance = p.provenance ∧ result.address.val = p.address.val + count.val ∧
        alloc raw_box.u32Repr ⟨p.provenance, bptr⟩ bptr length own h) :=
  HeapWP.byte_add.spec raw_box.u32Repr p bptr count length own hstart hhi hfit hcount

theorem byte_shift.spec (p : MutRawPtr U32) (bptr : BasePtr) (count : Isize) (length : Nat) (own : Bool)
    (hstart : bptr.val ≤ p.address.val ∧ p.address.val ≤ bptr.val + length * 4)
    (hlo : (bptr.val : Int) ≤ (p.address.val : Int) + count.val)
    (hhi : (p.address.val : Int) + count.val ≤ bptr.val + length * 4)
    (hfit : (p.address.val : Int) + count.val < (2 ^ UScalarTy.numBits .Usize : Nat)) :
    HeapWP.Triple (alloc raw_box.u32Repr ⟨p.provenance, bptr⟩ bptr length own) (byte_shift p count)
      (fun result h => result.provenance = p.provenance ∧
        (result.address.val : Int) = (p.address.val : Int) + count.val ∧
        alloc raw_box.u32Repr ⟨p.provenance, bptr⟩ bptr length own h) :=
  HeapWP.byte_offset.spec raw_box.u32Repr p bptr count length own hstart hlo hhi hfit

theorem word_distance.spec (p origin : MutRawPtr U32) (bptr : BasePtr) (length : Nat) (own : Bool)
    (hbase : p.provenance = origin.provenance)
    (hp : bptr.val ≤ p.address.val ∧ p.address.val ≤ bptr.val + length * 4)
    (ho : bptr.val ≤ origin.address.val ∧ origin.address.val ≤ bptr.val + length * 4)
    (hdiv : ((p.address.val : Int) - origin.address.val) % 4 = 0)
    (hbytes : IScalar.cMin .Isize ≤ (p.address.val : Int) - origin.address.val ∧
      (p.address.val : Int) - origin.address.val ≤ IScalar.cMax .Isize)
    (hcount : IScalar.cMin .Isize ≤ ((p.address.val : Int) - origin.address.val) / 4 ∧
      ((p.address.val : Int) - origin.address.val) / 4 ≤ IScalar.cMax .Isize) :
    HeapWP.Triple (alloc raw_box.u32Repr ⟨p.provenance, bptr⟩ bptr length own) (word_distance p origin)
      (fun result h => result.val = ((p.address.val : Int) - origin.address.val) / 4 ∧
        result.val * 4 = (p.address.val : Int) - origin.address.val ∧
        alloc raw_box.u32Repr ⟨p.provenance, bptr⟩ bptr length own h) :=
  HeapWP.offset_from.spec raw_box.u32Repr p origin bptr length own (by decide) hbase hp ho hdiv hbytes hcount

theorem fill_words.spec (p : MutRawPtr U32) (bptr : BasePtr) (count : Usize) (value : U32)
    (old : Vector U32 count.val) (hcount : 0 < count.val) :
    HeapWP.Triple (pointsToRange raw_box.u32Repr p bptr old) (fill_words p count value)
      (fun _ => pointsToRange raw_box.u32Repr p bptr (Vector.replicate count.val value)) := by
  unfold fill_words ext.fill_words
  intro h F s₀ hp hd hm hinv
  apply HeapWP.Spec.bind (HeapWP.borrowRange_return.spec raw_box.u32Repr p bptr old
    (Vector.replicate count.val value)
    (by intro i q; simp)
    hcount (by decide) h F s₀ hp hd hm hinv)
  rintro values s₁ ⟨_, returns⟩
  simpa using returns

end raw_pointer_ops
