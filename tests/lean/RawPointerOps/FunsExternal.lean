module

public import RawPointerOps.Types
public import RawValueCasts.Repr
public import Aeneas.Std.Core.PtrOps
public import Aeneas.Std.Core.PtrMovement
public import Aeneas.Std.Heap.RangeRestoration

/-! Local transparent models for the opaque Rust wrappers. The generated callers
and their signatures are unchanged; Rust-layout refinement remains separate. -/

@[expose] public section

open Aeneas.Std

namespace raw_pointer_ops.ext

def read_word (p : MutRawPtr U32) : Result U32 := p.read raw_box.u32Repr

def write_word (p : MutRawPtr U32) (value : U32) : Result Unit :=
  MutRawPtr.write raw_box.u32Repr p value

def read_flag (p : MutRawPtr Bool) : Result Bool := p.read raw_value_casts.boolRepr

def write_flag (p : MutRawPtr Bool) (value : Bool) : Result Unit :=
  MutRawPtr.write raw_value_casts.boolRepr p value

def replace_word (p : MutRawPtr U32) (value : U32) : Result U32 :=
  p.replace raw_box.u32Repr value

def swap_words (p q : MutRawPtr U32) : Result Unit :=
  p.swap raw_box.u32Repr q

def read_unaligned_word (p : MutRawPtr U32) : Result U32 :=
  p.read_unaligned raw_box.u32Repr

def write_unaligned_word (p : MutRawPtr U32) (value : U32) : Result Unit :=
  p.write_unaligned raw_box.u32Repr value

def byte_advance (p : MutRawPtr U32) (count : Usize) : Result (MutRawPtr U32) :=
  p.byte_add count

def byte_shift (p : MutRawPtr U32) (count : Isize) : Result (MutRawPtr U32) :=
  p.byte_offset count

def word_distance (p origin : MutRawPtr U32) : Result Isize :=
  p.offset_from raw_box.u32Repr origin

def fill_words (p : MutRawPtr U32) (count : Usize) (value : U32) : Result Unit := do
  let _ ← RawPtr.borrowRange raw_box.u32Repr p count.val
  RawPtr.endBorrowRange raw_box.u32Repr p (List.replicate count.val value)

end raw_pointer_ops.ext
