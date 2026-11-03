module

public import RawScale.Layout

@[expose] public section

open Aeneas Aeneas.Std

namespace raw_scale.ext

/- These replace emitted opaque casts and the legacy always-failing cast_scalar.
   A cast preserves address and provenance; accesses still check their descriptors. -/
def cast {T : Type} (U : Type) (p : RawPtr T) : Result (RawPtr U) :=
  .ok (p.cast U)

/- Expose the containing row, not a fresh alignment-four u32 slice. This retains
   the source Row13's alignment and all sixteen initialized physical elements. -/
def row_as_ptr (row : Row13) : Result (ConstRawPtr U32 × Result Unit) :=
  Aeneas.Std.bind (RawPtr.allocSharedExposure rowRepr [row]) fun p =>
    .ok (p.cast U32, p.endSharedExposure rowRepr [row])

def row_as_mut_ptr (row : Row13) : Result (MutRawPtr U32 × Result Row13) :=
  Aeneas.Std.bind (core.ptr.from_mut rowRepr row) fun (p, back) =>
    .ok (p.cast U32, back)

end raw_scale.ext
