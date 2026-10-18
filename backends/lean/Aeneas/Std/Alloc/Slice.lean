/- `alloc::slice` -/
module
public import Aeneas.Std.Alloc.Vec

public section

namespace Aeneas.Std

open Result WP

@[expose, rust_fun "alloc::slice::{[@T]}::to_vec"]
def alloc.slice.Slice.to_vec
  {T : Type _} (cloneInst : core.clone.Clone T) (s : Slice T) : Result (alloc.vec.Vec T) := do
  let s ← Slice.clone cloneInst.clone s
  ok {slice := s}

@[step]
theorem alloc.slice.Slice.to_vec_spec {T : Type _} (cloneInst : core.clone.Clone T) (s : Slice T)
  (h : ∀ x ∈ s.val, cloneInst.clone x = ok x) :
  alloc.slice.Slice.to_vec cloneInst s ⦃ s' => s = s'.slice ⦄ := by
  simp only [to_vec]
  apply Std.WP.spec_bind (Slice.clone_spec h)
  intro s' hs
  simpa using hs

@[expose, rust_fun "alloc::slice::{[@T]}::into_vec" -canFail -lift (keepParams := [true, false])]
def alloc.slice.Slice.into_vec
  {T : Type _} (s: Slice T) : (alloc.vec.Vec T) := {slice := s}

end Aeneas.Std
