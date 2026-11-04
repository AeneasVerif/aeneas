-- Adapted Aeneas emission; see EXTRACTION.md and the adjacent adaptation.patch.
-- [raw_zeroize]: function definitions
module
public import Aeneas
public import RawZeroize.Types
public import RawZeroize.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
namespace raw_zeroize

/-- [raw_zeroize::zeroize]: loop 0:
    Source: 'tests/src/raw_zeroize.rs', lines 23:4-28:5
    Visibility: public -/
@[rust_loop]
def zeroize_loop
  (iter : core.ops.range.Range Std.Usize) (bytes : MutRawPtr Std.U8) :
  Result Unit
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok ()
  | some i =>
    let p ← RawPtr.add Aeneas.Std.Repr.u8 bytes i
    write_volatile p 0#u8
    zeroize_loop iter1 bytes
partial_fixpoint

/-- [raw_zeroize::zeroize]:
    Source: 'tests/src/raw_zeroize.rs', lines 16:0-29:1
    Visibility: public -/
def zeroize
  {T : Type} (elementSize : Std.Usize) (storage : UninitSlice T) :
  Result (UninitSlice T) := do
  let (p, storage1) ← UninitSlice.as_mut_ptr storage
  let bytes ← ptr_cast Std.U8 p
  let i := storage1.len
  let i1 ← size_of T elementSize
  let o ← lift (Usize.checked_mul i i1)
  let size ← core.option.Option.expect o (toStr "overflow")
  let i2 ← lift (IScalar.hcast .Usize core.num.Isize.MAX)
  massert (size <= i2)
  zeroize_loop { start := 0#usize, «end» := size } bytes
  ok storage1

/-- [raw_zeroize::zeroize_word]:
    Source: 'tests/src/raw_zeroize.rs', lines 32:0-38:1
    Visibility: public -/
def zeroize_word (word : Std.U32) : Result Std.U32 := do
  let (p, back) ← core.ptr.from_mut raw_box.u32Repr word
  let ptr ← ptr_cast Std.U32 p
  let (storage, endStorage) ← UninitSlice.from_raw_parts_mut ptr 1#usize
  let storage ← zeroize 4#usize storage
  endStorage storage
  back

end raw_zeroize
