import Aeneas.Std.Core.Fmt
import Aeneas.Std.Array.Array
import Aeneas.Std.Slice
import Aeneas.Std.Range
import Aeneas.Data.List.List
import Aeneas.Std.Core.Convert
import Aeneas.Std.Core.Cmp

/-! Array definitions which mention slices -/

namespace Aeneas.Std

open Result Error core.ops.range WP

attribute [-simp] List.getElem!_eq_getElem?_getD

/-! Array to slice/subslices -/

@[step_pure_def]
def Array.to_slice {α : Type u} {n : Usize} (v : Array α n) : Slice α :=
  ⟨ v.val, by scalar_tac ⟩

@[simp, scalar_tac_simps]
theorem Array.to_slice_val {α : Type u} {n : Usize} (v : Array α n) :
    v.to_slice.val = v.val := by rfl

@[simp, scalar_tac_simps]
theorem Array.to_slice_length {α : Type u} {n : Usize} (v : Array α n) :
    v.to_slice.length = n.val := by simp [Slice.length, Array.to_slice]

@[simp, scalar_tac_simps]
theorem Array.to_slice_len {α : Type u} {n : Usize} (v : Array α n) :
    v.to_slice.len = n := by
  unfold Slice.len
  simp [Array.to_slice]
  scalar_tac

def Array.from_slice {α : Type u} {n : Usize} (a : Array α n) (s : Slice α) : Array α n :=
  if h: s.val.length = n.val then
    ⟨ s.val, by simp [*] ⟩
  else a -- Unreachable case

@[simp]
theorem Array.from_slice_val {α : Type u} {n : Usize} (a : Array α n) (ns : Slice α) (h : ns.val.length = n.val) :
  (from_slice a ns).val = ns.val
  := by simp [from_slice, *]

@[step_pure_def]
def Array.to_slice_mut {α : Type u} {n : Usize} (a : Array α n) :
  Slice α × (Slice α → Array α n) :=
  (Array.to_slice a, Array.from_slice a)

def Array.subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end.val ∧ r.end.val ≤ a.val.length then
    ok ⟨ a.val.slice r.start.val r.end.val,
          by
            have := a.val.slice_length_le r.start.val r.end.val
            scalar_tac ⟩
  else
    fail panic

@[step]
theorem Array.subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize)
  (h0 : r.start.val < r.end.val) (h1 : r.end.val ≤ a.val.length) :
  subslice a r ⦃ s =>
  s.val = a.val.slice r.start.val r.end.val ∧
  (∀ i, i + r.start.val < r.end.val → s.val[i]! = a.val[r.start.val + i]!) ⦄
  := by
  simp only [subslice, true_and, h0, h1, ↓reduceIte, spec_ok, true_and]
  intro i _
  have := List.getElem!_slice r.start.val r.end.val i a.val (by scalar_tac)
  simp only [this]


def Array.update_subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) (s : Slice α) : Result (Array α n) :=
  -- TODO: not completely sure here
  if h: r.start.val < r.end.val ∧ r.end.val ≤ a.length ∧ s.val.length = r.end.val - r.start.val then
    ok ⟨ a.val.setSlice! r.start s.val, by scalar_tac ⟩
  else
    fail panic

-- TODO: it is annoying to write `.val` everywhere. We could leverage coercions,
-- but: some symbols like `+` are already overloaded to be notations for monadic
-- operations/
-- We should introduce special symbols for the monadic arithmetic operations
-- (the user will never write those symbols directly).
@[step]
theorem Array.update_subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize) (s : Slice α)
  (_ : r.start.val < r.end.val) (_ : r.end.val ≤ a.length) (_ : s.length = r.end.val - r.start.val) :
  update_subslice a r s ⦃ na =>
  (∀ i, i < r.start.val → na[i]! = a[i]!) ∧
  (∀ i, r.start.val ≤ i → i < r.end.val → na[i]! = s[i - r.start.val]!) ∧
  (∀ i, r.end.val ≤ i → i < n.val → na[i]! = a[i]!) ⦄ := by
  simp [update_subslice]
  split
  . simp [spec_ok]
    simp_lists
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

@[simp, simp_lists_safe, grind =, agrind =]
theorem Array.val_to_slice {α} {n} (a : Array α n) : a.to_slice.val = a.val := by
  simp only [Array.to_slice]

@[simp, simp_lists_safe, simp_scalar_safe, scalar_tac a.to_slice]
theorem Array.length_to_slice (a : Array α n) :
  a.to_slice.length = n := by
  simp only [Slice.length, Array.to_slice, List.Vector.length_val]

grind_pattern Array.length_to_slice => a.to_slice
grind_pattern [agrind] Array.length_to_slice => a.to_slice

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
def core.array.DebugTryFromSliceError.fmt
  (_ : core.array.TryFromSliceError) (fmt : core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: this model is simplistic
  .ok (.Ok (), fmt)

@[reducible, rust_trait_impl
  "core::fmt::Debug<core::array::TryFromSliceError>"]
def core.fmt.DebugTryFromSliceError : core.fmt.Debug
  core.array.TryFromSliceError := {
  fmt := core.array.DebugTryFromSliceError.fmt
}

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

@[reducible, rust_trait_impl
  "core::convert::TryFrom<&'a [@T; @N], &'a [@T], core::array::TryFromSliceError>"]
def core.convert.TryFromSharedArraySliceTryFromSliceError (T : Type) (N : Usize) :
  core.convert.TryFrom (Array T N) (Slice T)
  core.array.TryFromSliceError := {
  try_from := core.array.TryFromSharedArraySlice.try_from N
}

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

@[simp, step_simps]
theorem Array.index_SliceIndexRangeUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.Range Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeUsizeSlice.index r a.to_slice := by rfl

-- Array index/index_mut with RangeTo

@[simp, step_simps]
theorem Array.index_SliceIndexRangeToUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.RangeTo Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeToUsizeSlice.index r a.to_slice := by rfl

@[step]
theorem Array.index_mut_SliceIndexRangeToUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.RangeTo Usize)
    (h : r.end ≤ N) :
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice T)) a r
    ⦃ (s, back) =>
      s.val = a.val.slice 0 r.end ∧
      s.length = r.end.val ∧
      ∀ s', (back s').val = a.val.setSlice! 0 s'.val ⦄ := by
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut]
  have hts : a.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  simp only [core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    show (r.end : Usize) ≤ a.to_slice.length from by scalar_tac]
  refine ⟨?_, ?_, ?_⟩
  · simp [Array.to_slice]
  · simp [Slice.length]; scalar_tac
  · intro s'; simp [Array.from_slice, Array.to_slice]

-- Array index/index_mut with RangeFrom

@[simp, step_simps]
theorem Array.index_SliceIndexRangeFromUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.RangeFrom Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeFromUsizeSlice.index r a.to_slice := by rfl

@[step]
theorem Array.index_mut_SliceIndexRangeFromUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.RangeFrom Usize)
    (h : r.start ≤ N) :
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice T)) a r
    ⦃ (s, back) =>
      s.val = a.val.drop r.start ∧
      s.length = N.val - r.start.val ∧
      ∀ s', (back s').val = a.val.setSlice! r.start.val s'.val ⦄ := by
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut]
  have hts : a.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  simp only [core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    Slice.drop,
    show (r.start : Usize) ≤ a.to_slice.length from by scalar_tac]
  refine ⟨?_, ?_, ?_⟩
  · simp [Array.to_slice]
  · simp [Slice.length, List.length_drop]
  · intro s'; simp [Array.from_slice, Array.to_slice]

/-! ## Cross-type slice/array comparisons

Pinned to Rust `1.85.0` (Charon pin `nightly-2026-02-07`). -/

/-- Helper: elementwise PartialEq over two equal-length lists. -/
def core.array.equality.PartialEqSliceArray.eq_loop {T U : Type}
    (partialEqInst : core.cmp.PartialEq T U)
    (a : List T) (b : List U) : Result Bool :=
  match a, b with
  | [], [] => ok true
  | x :: xs, y :: ys => do
    let r ← partialEqInst.eq x y
    if r then eq_loop partialEqInst xs ys else ok false
  | _, _ => ok false

/-- `PartialEq<[U; N]> for [T]::eq`: slice equals array elementwise.

- Docs: https://doc.rust-lang.org/core/primitive.slice.html#impl-PartialEq-for-%5BT%5D
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/array/equality.rs
-/
@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::eq"]
def core.array.equality.PartialEqSliceArray.eq {T U : Type} {N : Usize}
    (partialEqInst : core.cmp.PartialEq T U)
    (s : Slice T) (a : Array U N) : Result Bool :=
  if s.length = a.length then
    core.array.equality.PartialEqSliceArray.eq_loop partialEqInst s.val a.val
  else ok false

@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T], [@U; @N]>}::ne"]
def core.array.equality.PartialEqSliceArray.ne {T U : Type} {N : Usize}
    (partialEqInst : core.cmp.PartialEq T U)
    (s : Slice T) (a : Array U N) : Result Bool := do
  let r ← core.array.equality.PartialEqSliceArray.eq partialEqInst s a
  ok (¬ r)

@[reducible, rust_trait_impl "core::cmp::PartialEq<[@T], [@U; @N]>"]
def core.array.equality.PartialEqSliceArray {T U : Type} {N : Usize}
    (partialEqInst : core.cmp.PartialEq T U) :
    core.cmp.PartialEq (Slice T) (Array U N) := {
  eq := core.array.equality.PartialEqSliceArray.eq partialEqInst
  ne := core.array.equality.PartialEqSliceArray.ne partialEqInst
}

/-- Helper: lexicographic compare on lists. -/
def core.slice.cmp.OrdSlice.cmp_loop {T : Type}
    (ordInst : core.cmp.Ord T) (a b : List T) : Result Ordering :=
  match a, b with
  | [], [] => ok .eq
  | [], _ :: _ => ok .lt
  | _ :: _, [] => ok .gt
  | x :: xs, y :: ys => do
    let c ← ordInst.cmp x y
    match c with
    | .eq => cmp_loop ordInst xs ys
    | other => ok other

/-- `Ord for [T]::cmp`: lexicographic comparison over slices.

- Docs: https://doc.rust-lang.org/core/primitive.slice.html#impl-Ord-for-%5BT%5D
- Source: https://github.com/rust-lang/rust/blob/1.85.0/library/core/src/slice/cmp.rs
-/
@[rust_fun "core::slice::cmp::{core::cmp::Ord<[@T]>}::cmp"]
def core.slice.cmp.OrdSlice.cmp {T : Type}
    (ordInst : core.cmp.Ord T) (s s' : Slice T) : Result Ordering :=
  core.slice.cmp.OrdSlice.cmp_loop ordInst s.val s'.val

end Aeneas.Std
