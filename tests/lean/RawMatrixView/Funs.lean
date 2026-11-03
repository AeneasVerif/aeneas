module

public import RawMatrixView.FunsExternal
public import RawBoxProofs
import all Aeneas.Std.Slice

@[expose] public section

open Aeneas Aeneas.Std Result

namespace raw_matrix_view

/- The two safe functions below are the emitted bodies, unchanged.
   The raw function adds explicit descriptors and the approved backward call.
   Pristine output and the exact extraction command are recorded in EXTRACTION.md. -/
@[rust_loop]
def scale_slice_loop (k : U32) (values : Slice U32) (i : Usize) :
    Result (Slice U32) := do
  let i1 := Slice.len values
  if i < i1 then
    let i2 ← Slice.index_usize values i
    let i3 ← lift (core.num.U32.wrapping_mul k i2)
    let s ← Slice.update values i i3
    let i4 ← i + 1#usize
    scale_slice_loop k s i4
  else ok values
partial_fixpoint

@[reducible]
def scale_slice (k : U32) (values : Slice U32) : Result (Slice U32) := do
  scale_slice_loop k values 0#usize

def scale_raw (matrixRepr : Aeneas.Std.Repr Matrix) (k : U32) (matrix : MutRawPtr Matrix) :
    Result U32 := do
  let p ← core.ptr.mut_ptr.RawPtrMutT.cast U32 matrix
  let (flat, back) ← core.slice.raw.from_raw_parts_mut raw_box.u32Repr p 32#usize
  let flat ← scale_slice k flat
  back flat
  let m ← RawPtr.read matrixRepr matrix
  let a ← Array.index_usize m 1#usize
  Array.index_usize a 12#usize

/- The safe wrapper fails extraction at its implicit mutable-to-raw coercion.
   Reconstruct that boundary with the library exposure and matching backward. -/
def scale (matrixRepr : Aeneas.Std.Repr Matrix) (k : U32) (matrix : Matrix) :
    Result (U32 × Matrix) := do
  let (p, back) ← core.ptr.from_mut matrixRepr matrix
  let result ← scale_raw matrixRepr k p
  let matrix ← back
  ok (result, matrix)

end raw_matrix_view
