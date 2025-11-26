import Aeneas.Std.Core.Fmt
import Aeneas.Std.Array.Array
import Aeneas.Std.Slice
import Aeneas.Std.Range
import Aeneas.List.List

/-! Array definitions which mention slices -/

namespace Aeneas.Std

open Result Error core.ops.range

attribute [-simp] List.getElem!_eq_getElem?_getD

/-! Array to slice/subslices -/

@[progress_pure_def]
def Array.to_slice {α : Type u} {n : Usize} (v : Array α n) : Slice α :=
  ⟨ v.val, by scalar_tac ⟩

def Array.from_slice {α : Type u} {n : Usize} (a : Array α n) (s : Slice α) : Array α n :=
  if h: s.val.length = n.val then
    ⟨ s.val, by simp [*] ⟩
  else a -- Unreachable case

@[simp]
theorem Array.from_slice_val {α : Type u} {n : Usize} (a : Array α n) (ns : Slice α) (h : ns.val.length = n.val) :
  (from_slice a ns).val = ns.val
  := by simp [from_slice, *]

@[progress_pure_def]
def Array.to_slice_mut {α : Type u} {n : Usize} (a : Array α n) :
  Slice α × (Slice α → Array α n) :=
  (Array.to_slice a, Array.from_slice a)

def Array.subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end_.val ∧ r.end_.val ≤ a.val.length then
    ok ⟨ a.val.slice r.start.val r.end_.val,
          by
            have := a.val.slice_length_le r.start.val r.end_.val
            scalar_tac ⟩
  else
    fail panic

@[progress]
theorem Array.subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ a.val.length) :
  ∃ s, subslice a r = ok s ∧
  s.val = a.val.slice r.start.val r.end_.val ∧
  (∀ i, i + r.start.val < r.end_.val → s.val[i]! = a.val[r.start.val + i]!)
  := by
  simp only [subslice, true_and, h0, h1, ↓reduceIte, ok.injEq, exists_eq_left', true_and]
  intro i _
  have := List.getElem!_slice r.start.val r.end_.val i a.val (by scalar_tac)
  simp only [this]


def Array.update_subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) (s : Slice α) : Result (Array α n) :=
  -- TODO: not completely sure here
  if h: r.start.val < r.end_.val ∧ r.end_.val ≤ a.length ∧ s.val.length = r.end_.val - r.start.val then
    ok ⟨ a.val.setSlice! r.start s.val, by scalar_tac ⟩
  else
    fail panic

-- TODO: it is annoying to write `.val` everywhere. We could leverage coercions,
-- but: some symbols like `+` are already overloaded to be notations for monadic
-- operations/
-- We should introduce special symbols for the monadic arithmetic operations
-- (the user will never write those symbols directly).
@[progress]
theorem Array.update_subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize) (s : Slice α)
  (_ : r.start.val < r.end_.val) (_ : r.end_.val ≤ a.length) (_ : s.length = r.end_.val - r.start.val) :
  ∃ na, update_subslice a r s = ok na ∧
  (∀ i, i < r.start.val → na[i]! = a[i]!) ∧
  (∀ i, r.start.val ≤ i → i < r.end_.val → na[i]! = s[i - r.start.val]!) ∧
  (∀ i, r.end_.val ≤ i → i < n.val → na[i]! = a[i]!) := by
  simp [update_subslice]
  split <;> simp only [reduceCtorEq, false_and, exists_false, ok.injEq, exists_eq_left']
  . simp_lists
  . scalar_tac

@[rust_fun "core::array::{core::ops::index::Index<[@T; @N], @I, @O>}::index"]
def core.array.Array.index
  {T I Output : Type} {N : Usize} (inst : core.ops.index.Index (Slice T) I Output)
  (a : Array T N) (i : I) : Result Output :=
  inst.index a.to_slice i

@[rust_fun "core::array::{core::ops::index::IndexMut<[@T; @N], @I, @O>}::index_mut"]
def core.array.Array.index_mut
  {T I Output : Type} {N : Usize} (inst : core.ops.index.IndexMut (Slice T) I Output)
  (a : Array T N) (i : I) :
  Result (Output × (Output → Array T N)) := do
  let (s, back) ← inst.index_mut a.to_slice i
  ok (s, fun o => Array.from_slice a (back o))

@[rust_trait_impl "core::ops::index::Index<[@T; @N], @I, @O>"]
def core.ops.index.IndexArray {T I Output : Type} {N : Usize}
  (inst : core.ops.index.Index (Slice T) I Output) :
  core.ops.index.Index (Array T N) I Output := {
  index := core.array.Array.index inst
}

@[rust_trait_impl "core::ops::index::IndexMut<[@T; @N], @I, @O>"]
def core.ops.index.IndexMutArray {T I Output : Type} {N : Usize}
  (inst : core.ops.index.IndexMut (Slice T) I Output) :
  core.ops.index.IndexMut (Array T N) I Output := {
  indexInst := core.ops.index.IndexArray inst.indexInst
  index_mut := core.array.Array.index_mut inst
}

@[reducible, rust_type "core::array::TryFromSliceError"]
def core.array.TryFromSliceError := Unit

@[simp, simp_lists_simps]
theorem Array.val_to_slice {α} {n} (a : Array α n) : a.to_slice.val = a.val := by
  simp only [Array.to_slice]

@[simp, simp_lists_simps, simp_scalar_simps, scalar_tac a.to_slice]
theorem Array.length_to_slice (a : Array α n) :
  a.to_slice.length = n := by
  simp only [Slice.length, Array.to_slice, List.Vector.length_val]

@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::eq"]
def core.array.equality.PartialEqArray.eq
  {T : Type} {U : Type} {N : Usize} (partialEqInst : core.cmp.PartialEq T U)
  (a0 : Array T N) (a1 : Array U N) : Result Bool := do
  if a0.length = a1.length then
    List.allM (fun (x, y) => partialEqInst.eq x y) (List.zip a0.val a1.val)
  else .ok false

@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::ne"]
def core.array.equality.PartialEqArray.ne
  {T : Type} {U : Type} {N : Usize} (partialEqInst : core.cmp.PartialEq T U)
  (a0 : Array T N) (a1 : Array U N) : Result Bool := do
  if a0.length = a1.length then
    List.anyM (fun (x, y) => partialEqInst.ne x y) (List.zip a0.val a1.val)
  else .ok true

@[rust_fun "core::array::{core::fmt::Debug<core::array::TryFromSliceError>}::fmt"]
def core.array.DebugcorearrayTryFromSliceError.fmt
  (_ : core.array.TryFromSliceError) (fmt : core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: this model is simplistic
  .ok (.Ok (), fmt)

@[rust_fun "core::array::{core::convert::TryFrom<[@T; @N], &'0 [@T], core::array::TryFromSliceError>}::try_from"]
def core.array.TryFromArrayCopySlice.try_from
  {T : Type} (N : Usize) (copyInst : core.marker.Copy T) (s : Slice T) :
  Result (core.result.Result (Array T N) core.array.TryFromSliceError) := do
  if h0: s.length = N then
    match h1: List.mapM copyInst.cloneInst.clone s.val with
    | ok s =>
      ok (.Ok ⟨s, by have := List.mapM_Result_length h1; scalar_tac ⟩)
    | fail e => fail e
    | div => div
  else ok (.Err ())

@[rust_fun "core::array::{core::convert::TryFrom<&'a [@T; @N], &'a [@T], core::array::TryFromSliceError>}::try_from"]
def core.array.TryFromSharedArraySlice.try_from
  {T : Type} (N : Usize) (s : Slice T) :
  Result (core.result.Result (Array T N) core.array.TryFromSliceError) := do
  if h: s.len = N then .ok (.Ok ⟨s.val, by scalar_tac⟩)
  else .ok (.Err ())

@[rust_fun "core::array::{core::convert::TryFrom<&'a mut [@T; @N], &'a mut [@T], core::array::TryFromSliceError>}::try_from"]
def core.array.TryFromMutArraySlice.try_from
  {T : Type} (N : Usize) (s : Slice T) :
  Result (
    core.result.Result (Array T N) core.array.TryFromSliceError ×
    (core.result.Result (Array T N) core.array.TryFromSliceError → Slice T)) :=
  if h: s.len = N then
    let back (a : core.result.Result (Array T N) core.array.TryFromSliceError) : Slice T :=
      match a with
      | .Ok a =>
        if a.length = s.length then ⟨ a.val, by scalar_tac ⟩
        else s
      | _ => s
    ok ((.Ok ⟨ s.val, by scalar_tac⟩, back))
  else ok ((.Err (), fun _ => s))

@[simp, rust_fun "core::array::{core::fmt::Debug<[@T; @N]>}::fmt"]
def core.array.DebugArray.fmt
  {T : Type} {N : Usize} (_ : core.fmt.Debug T) (_ : Array T N) (fmt : core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: this model is simplistic
  ok (.Ok (), fmt)

@[rust_fun "core::array::{[@T; @N]}::as_slice"]
def core.array.Array.as_slice {T : Type} {N : Usize} (a : Array T N) : Result (Slice T) :=
  ok (⟨ a.val, by scalar_tac ⟩)

@[rust_fun "core::array::{[@T; @N]}::as_mut_slice"]
def core.array.Array.as_mut_slice
  {T : Type} {N : Usize} (a : Array T N) :
  Result (Slice T × (Slice T → Array T N)) :=
  let back (s : Slice T) : Array T N :=
    if h: s.length = N then ⟨ s.val, by scalar_tac ⟩
    else a
  ok (⟨ a.val, by scalar_tac ⟩, back)

end Aeneas.Std
