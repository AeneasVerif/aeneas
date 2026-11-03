module

public import RawMatrixView.Types

@[expose] public section

open Aeneas Aeneas.Std

/- The generated opaque pointer cast is the model's provenance-preserving cast.
   `from_raw_parts_mut` uses the existing effectful library definition directly. -/
def core.ptr.mut_ptr.RawPtrMutT.cast {T : Type} (U : Type)
    (p : MutRawPtr T) : Result (MutRawPtr U) :=
  .ok (p.cast U)
