module

public import RawPointerOps.Properties
import all RawPointerOps.FunsExternal
import all RawBoxProofs
import all RawTransmute
import all Aeneas.Std.Core.PtrOps
import all Aeneas.Std.Core.PtrMovement
import all Aeneas.Std.Heap.Ranges
import all Aeneas.Std.Heap
import all Aeneas.Std.Heap.Model

public section

open Aeneas.Std

namespace raw_pointer_ops

def unalignedChecks : Option Bool := do
  let (p, s) ← Heap.newBlock raw_transmute.byteRepr
    [#v[0xaa#u8], #v[0x12#u8], #v[0x34#u8], #v[0x56#u8], #v[0x78#u8], #v[0xbb#u8]] true Heap.empty
  let word : RawPtr U32 := ⟨p.provenance, 1#usize⟩
  let before ← Heap.read raw_box.u32Repr.unaligned word s
  let data := #v[0x21#u8, 0x43#u8, 0x65#u8, 0x87#u8]
  let s' ← Heap.write raw_box.u32Repr.unaligned word 0x87654321#u32 data (by native_decide) s
  let bytes ← Heap.readRange raw_transmute.byteRepr p 6 s'
  pure (before == 0x78563412#u32 && (Heap.read raw_box.u32Repr word s).isNone &&
    bytes == [0xaa#u8, 0x21#u8, 0x43#u8, 0x65#u8, 0x87#u8, 0xbb#u8])

example : unalignedChecks = some true := by native_decide

def rangeCycleChecks : Option Bool := do
  let (p, s) ← Heap.newBlock raw_transmute.byteRepr [#v[1#u8], #v[2#u8], #v[3#u8]] true Heap.empty
  let third : RawPtr U8 := ⟨p.provenance, 2#usize⟩
  let borrowed ← Heap.borrowRange raw_transmute.byteRepr p 2 s
  let frame ← Heap.read raw_transmute.byteRepr third borrowed
  let restored ← Heap.endBorrowRange raw_transmute.byteRepr p [#v[7#u8], #v[8#u8]] borrowed
  let shared ← Heap.shareRange raw_transmute.byteRepr p 2 restored
  let values ← Heap.readRange raw_transmute.byteRepr p 3 shared
  let ended ← Heap.endShareRange raw_transmute.byteRepr p 2 shared
  let final ← Heap.readRange raw_transmute.byteRepr p 3 ended
  pure (frame == 3#u8 && values == [7#u8, 8#u8, 3#u8] && final == values &&
    (Heap.readRange raw_transmute.byteRepr p 2 borrowed).isNone &&
    (Heap.write raw_transmute.byteRepr p 9#u8 #v[9#u8] rfl borrowed).isNone &&
    (Heap.write raw_transmute.byteRepr p 9#u8 #v[9#u8] rfl shared).isNone)

example : rangeCycleChecks = some true := by native_decide

def atomicRangeRejection : Option Bool := do
  let (p, s) ← Heap.newBlock raw_transmute.byteRepr [#v[1#u8], #v[2#u8]] true Heap.empty
  let second : RawPtr U8 := ⟨p.provenance, 1#usize⟩
  let shared ← Heap.share raw_transmute.byteRepr second s
  let values ← Heap.readRange raw_transmute.byteRepr p 2 shared
  pure ((Heap.borrowRange raw_transmute.byteRepr p 2 shared).isNone &&
    (Heap.read raw_transmute.byteRepr p shared == some 1#u8) &&
    values == [1#u8, 2#u8] &&
    (Heap.borrowRange raw_transmute.byteRepr p 3 s).isNone)

example : atomicRangeRejection = some true := by native_decide

def initializationChecks : Option Bool := do
  let (p, s) ← Heap.alloc raw_box.u32Repr 1 Heap.empty
  let data := #v[1#u8, 0#u8, 0#u8, 0#u8]
  let initialized ← Heap.write raw_box.u32Repr p 1#u32 data (by native_decide) s
  pure ((Heap.read raw_box.u32Repr p s).isNone &&
    (Heap.read raw_box.u32Repr p initialized == some 1#u32))

example : initializationChecks = some true := by native_decide

def movementChecks : Option Bool := do
  let (p, s) ← Heap.alloc raw_box.u32Repr 3 Heap.empty
  let (other, s') ← Heap.alloc raw_box.u32Repr 1 s
  let finish ← Heap.byteOffset p 12 s'
  let back ← Heap.byteOffset finish (-12) s'
  let positive ← Heap.offsetFrom raw_box.u32Repr finish p s'
  let negative ← Heap.offsetFrom raw_box.u32Repr p finish s'
  let same ← Heap.offsetFrom raw_box.u32Repr p p s'
  let unaligned ← Heap.byteOffset p 1 s'
  let zst := raw_box.u32Repr.region 0
  pure (positive.val == 3 && negative.val == -3 && same.val == 0 &&
    finish.byteOffset == 12#usize && back.byteOffset == p.byteOffset &&
    unaligned.byteOffset == 1#usize &&
    (Heap.offsetFrom raw_box.u32Repr unaligned p s').isNone &&
    (Heap.offsetFrom raw_box.u32Repr p other s').isNone &&
    (Heap.offsetFrom zst (RawPtr.cast Unit p) (RawPtr.cast Unit p) s').isNone &&
    (Heap.byteOffset p (-1) s').isNone && (Heap.byteOffset finish 1 s').isNone &&
    (Heap.byteOffset p 0 Heap.empty).isNone)

example : movementChecks = some true := by native_decide

example : Heap.readRange raw_box.u32Repr (⟨⟨0⟩, ⟨0⟩⟩ : RawPtr U32) 0 Heap.empty = none := by
  decide

/-- Unsupported partial overlap is explicit failure, not a guessed swap result. -/
example (s : Heap) :
    ¬ HeapWP.Spec (RawPtr.swap raw_box.u32Repr
      (⟨⟨0⟩, 0#usize⟩ : RawPtr U32) ⟨⟨0⟩, 1#usize⟩) (fun _ _ => True) s := by
  simpa [RawPtr.swap, raw_box.u32Repr] using (HeapWP.Spec.fail (α := Unit) (s := s)
    (Q := fun _ _ => True) .undef)

/-- The extracted empty-range caller preserves the entire heap. -/
theorem fill_words_empty.spec (p : MutRawPtr U32) (s : Heap) (blk : Block) (value : U32)
    (hl : s.allocations p.provenance = some blk)
    (ha : raw_box.u32Repr.align.val ∣ blk.alignment.val)
    (hp : raw_box.u32Repr.align.val ∣ p.byteOffset.val)
    (hb : p.byteOffset.val ≤ blk.repr.length) :
    HeapWP.Spec (fill_words p 0#usize value) (fun _ s' => s' = s) s := by
  simp only [fill_words, ext.fill_words]
  have hr := HeapWP.emptyRanges.spec raw_box.u32Repr p s blk hl ha hp hb
  apply HeapWP.Spec.bind hr.1
  rintro values current ⟨_, he⟩
  subst current
  exact hr.2.2.2

/-- info: 'raw_pointer_ops.initialize_word.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initialize_word.spec

/-- info: 'raw_pointer_ops.initialize_invalid_flag.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initialize_invalid_flag.spec

/-- info: 'raw_pointer_ops.replace_word.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms replace_word.spec

/-- info: 'raw_pointer_ops.swap_words.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms swap_words.spec

/-- info: 'raw_pointer_ops.swap_self.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms swap_self.spec

/-- info: 'raw_pointer_ops.read_unaligned_word.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms read_unaligned_word.spec

/-- info: 'raw_pointer_ops.write_unaligned_word.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms write_unaligned_word.spec

/-- info: 'raw_pointer_ops.byte_advance.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms byte_advance.spec

/-- info: 'raw_pointer_ops.byte_shift.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms byte_shift.spec

/-- info: 'raw_pointer_ops.word_distance.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms word_distance.spec

/-- info: 'raw_pointer_ops.fill_words.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fill_words.spec

/-- info: 'Aeneas.Std.HeapWP.shareRange.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HeapWP.shareRange.spec

/-- info: 'Aeneas.Std.HeapWP.endShareRange.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HeapWP.endShareRange.spec

/-- info: 'Aeneas.Std.HeapWP.emptyRanges.spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HeapWP.emptyRanges.spec

end raw_pointer_ops
