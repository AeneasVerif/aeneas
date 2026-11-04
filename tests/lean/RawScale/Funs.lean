module

public import RawScale.FunsExternal
import all Aeneas.Std.Slice

@[expose] public section

open Aeneas Aeneas.Std Result

namespace raw_scale

/- Marked adaptation of the emitted computational functions from raw_scale.rs.
   Add/read/write use explicit descriptors; casts use ext.cast; exposures retain
   their effectful backward functions. Constructors, prefix accessors, and derived
   traits are outside this module. See EXTRACTION.md for the complete patch ledger. -/

/-- Loop-free scalar kernel: the emitted body with explicit read/write descriptors. -/
def scale_one_raw (k : U32) (src : ConstRawPtr U32) (dst : MutRawPtr U32) :
    Result Unit := do
  let value ← RawPtr.read raw_box.u32Repr src
  let i ← lift (core.num.U32.wrapping_mul k value)
  MutRawPtr.write raw_box.u32Repr dst i

/- Restore the shared cleanup and effectful mutable backward call omitted by
   extraction. The emitted `ok dst1` does not execute the updated model's callback. -/
def scale_one_into (k : U32) (src dst : U32) : Result U32 := do
  let (p, src_back) ← core.ptr.from_ref raw_box.u32Repr src
  let (p1, dst_back) ← core.ptr.from_mut raw_box.u32Repr dst
  scale_one_raw k p p1
  let dst ← dst_back
  src_back
  ok dst

/- The mut-to-const cast preserves provenance and address; return runs the callback. -/
def scale_one_in_place (k : U32) (value : U32) : Result U32 := do
  let (p, back) ← core.ptr.from_mut raw_box.u32Repr value
  let p1 ← ext.cast U32 p
  scale_one_raw k p1 p
  back

@[rust_loop]
def scale_raw_loop
    (iter : core.ops.range.Range Usize) (k : U32)
    (src : ConstRawPtr U32) (dst : MutRawPtr U32) : Result Unit := do
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok ()
  | some i =>
    let p ← RawPtr.add raw_box.u32Repr src i
    let p1 ← RawPtr.add raw_box.u32Repr dst i
    scale_one_raw k p p1
    scale_raw_loop iter1 k src dst
partial_fixpoint

@[reducible]
def scale_raw (N : Usize) (k : U32) (src : ConstRawPtr U32) (dst : MutRawPtr U32) :
    Result Unit := do
  scale_raw_loop { start := 0#usize, «end» := N } k src dst

def scale_into (k : U32) (src : Row13) (dst : Row13) : Result Row13 := do
  let (p, src_back) ← ext.row_as_ptr src
  let (p1, dst_back) ← ext.row_as_mut_ptr dst
  scale_raw 16#usize k p p1
  let dst ← dst_back
  src_back
  ok dst

def scale_in_place (k : U32) (buf : Row13) : Result Row13 := do
  let (p, back) ← ext.row_as_mut_ptr buf
  let p1 ← ext.cast U32 p
  scale_raw 16#usize k p1 p
  back

@[rust_loop]
def scale_rows_raw_loop
    {R : Usize} (iter : core.ops.range.Range Usize)
    (factors : Array U32 R) (src : ConstRawPtr Row13) (dst : MutRawPtr Row13) :
    Result Unit := do
  let (o, iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok ()
  | some r =>
    let i ← Array.index_usize factors r
    let p ← RawPtr.add rowRepr src r
    let p1 ← ext.cast U32 p
    let p2 ← RawPtr.add rowRepr dst r
    let p3 ← ext.cast U32 p2
    scale_raw 16#usize i p1 p3
    scale_rows_raw_loop iter1 factors src dst
partial_fixpoint

@[reducible]
def scale_rows_raw {R : Usize} (factors : Array U32 R)
    (src : ConstRawPtr Row13) (dst : MutRawPtr Row13) : Result Unit := do
  scale_rows_raw_loop { start := 0#usize, «end» := R } factors src dst

def scale_rows_into {R : Usize} (factors : Array U32 R)
    (src : Array Row13 R) (dst : Array Row13 R) : Result (Array Row13 R) := do
  let s ← lift (Array.to_slice src)
  let (p, src_back) ← Slice.as_ptr rowRepr s
  let (s1, to_slice_mut_back) ← lift (Array.to_slice_mut dst)
  let (p1, dst_back) ← Slice.as_mut_ptr rowRepr s1
  scale_rows_raw factors p p1
  let s2 ← dst_back
  src_back
  ok (to_slice_mut_back s2)

/- Extraction replaced this Rust body with an axiom after rejecting its
   mut-to-const aggregate cast. Reconstructed from the three Rust statements,
   using the same array exposure/backward plumbing as scale_rows_into. -/
def scale_rows_in_place {R : Usize} (factors : Array U32 R)
    (rows : Array Row13 R) : Result (Array Row13 R) := do
  let (s, to_slice_mut_back) ← lift (Array.to_slice_mut rows)
  let (p, back) ← Slice.as_mut_ptr rowRepr s
  let p1 ← ext.cast Row13 p
  scale_rows_raw factors p1 p
  let s1 ← back
  ok (to_slice_mut_back s1)

@[rust_loop]
def scale_slice_loop (k : U32) (buf : Slice U32) (i : Usize) : Result (Slice U32) := do
  let i1 := Slice.len buf
  if i < i1 then
    let i2 ← Slice.index_usize buf i
    let i3 ← lift (core.num.U32.wrapping_mul k i2)
    let s ← Slice.update buf i i3
    let i4 ← i + 1#usize
    scale_slice_loop k s i4
  else ok buf
partial_fixpoint

@[reducible]
def scale_slice (k : U32) (buf : Slice U32) : Result (Slice U32) := do
  scale_slice_loop k buf 0#usize

def scale_via_borrow_raw (k : U32) (p : MutRawPtr U32) : Result U32 := do
  let (borrowed, back) ← core.slice.raw.from_raw_parts_mut raw_box.u32Repr p 16#usize
  let borrowed ← scale_slice k borrowed
  back borrowed
  RawPtr.read raw_box.u32Repr p

def scale_via_borrow (k : U32) (buf : Row13) : Result (U32 × Row13) := do
  let (p, back) ← ext.row_as_mut_ptr buf
  let i ← scale_via_borrow_raw k p
  let buf ← back
  ok (i, buf)

end raw_scale
