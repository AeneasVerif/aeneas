/- `alloc::slice` -/
module
public import Aeneas.Std.Alloc.Vec

public section

namespace Aeneas.Std

open Result WP

@[expose, rust_fun "alloc::slice::{[@T]}::to_vec"]
def alloc.slice.Slice.to_vec
  {T : Type _} (cloneInst : core.clone.Clone T) (s : SharedBorrow (Slice T)) :
  Result (alloc.vec.Vec T) := do
  let s ← Slice.clone (fun x => cloneInst.clone (.mk x)) s.val
  ok {slice := s}

@[step]
theorem alloc.slice.Slice.to_vec_spec {T : Type _} (cloneInst : core.clone.Clone T)
  (s : SharedBorrow (Slice T))
  (h : ∀ x ∈ s.val.val, cloneInst.clone (.mk x) = ok x) :
  alloc.slice.Slice.to_vec cloneInst s ⦃ s' => s.val = s'.slice ⦄ := by
  simp only [to_vec]
  apply Std.WP.spec_bind (Slice.clone_spec h)
  intro s' hs
  simpa using hs

@[expose, rust_fun "alloc::slice::{[@T]}::into_vec" -canFail -lift (keepParams := [true, false])]
def alloc.slice.Slice.into_vec
  {T : Type _} (s: Box (Slice T)) : (alloc.vec.Vec T) := {slice := s.val}

end Aeneas.Std
