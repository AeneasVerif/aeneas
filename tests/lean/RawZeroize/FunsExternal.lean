module

public import Aeneas
public import RawBoxProofs
public import RawZeroize.Types

@[expose] public section

open Aeneas Aeneas.Std

namespace raw_zeroize

/- Layout is a target-specific input, not a byte-count shortcut: the emitted
   multiplication by the element count remains in zeroize. -/
def size_of (_T : Type) (elementSize : Usize) : Result Usize := .ok elementSize

def ptr_cast {T : Type} (U : Type) (ptr : RawPtr T) : Result (RawPtr U) :=
  .ok (ptr.cast U)

/- Only the heap effect is modeled, not compiler non-elision or event ordering.
   https://doc.rust-lang.org/std/ptr/fn.write_volatile.html -/
def write_volatile (ptr : MutRawPtr U8) (value : U8) : Result Unit :=
  MutRawPtr.write Aeneas.Std.Repr.u8 ptr value

/- These local slice views reuse the caller's exclusive heap region. Neither
   construction nor return decodes, copies, or re-encodes its uninitialized
   bytes. They are not general models of arbitrary Rust reference aliasing. -/
def UninitSlice.as_mut_ptr (storage : UninitSlice T) :
    Result (RawPtr T × UninitSlice T) :=
  .ok (storage.ptr, storage)

def UninitSlice.from_raw_parts_mut (ptr : RawPtr T) (len : Usize) :
    Result (UninitSlice T × (UninitSlice T → Result Unit)) :=
  .ok (⟨ptr, len⟩, fun _ => .ok ())

end raw_zeroize
