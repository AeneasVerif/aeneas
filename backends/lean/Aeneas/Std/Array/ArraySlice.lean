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

def Array.from_slice {α : Type u} {n : Usize} (a : Array α n) (s : Slice α) : Array α n :=
  if h: s.val.length = n.val then
    ⟨ s.val, by simp [*] ⟩
  else a -- Unreachable case

@[simp]
theorem Array.from_slice_val {α : Type u} {n : Usize} (a : Array α n) (ns : Slice α) (h : ns.val.length = n.val) :
  (from_slice a ns).val = ns.val
  := by simp [from_slice, *]

def Array.to_slice_mut {α : Type u} {n : Usize} (a : Array α n) :
  Slice α × (Slice α → Array α n) :=
  (Array.to_slice a, Array.from_slice a)

/-- Step theorem for `lift (Array.to_slice_mut a)` with curried postcondition.
    Handles the new Aeneas translation pattern `let (s, back) ← lift (to_slice_mut a)`. -/
@[step]
theorem Array.to_slice_mut_spec {α : Type u} {n : Usize} (a : Array α n) :
  (lift (Array.to_slice_mut a))
  ⦃ (s : Slice α) (back : Slice α → Array α n) =>
    s.val = a.val ∧ back = Array.from_slice a ⦄ := by
  simp [lift, to_slice_mut, to_slice, WP.spec_ok]

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

@[simp, simp_lists_safe, simp_scalar_safe, scalar_tac a.to_slice, grind =, agrind =]
theorem Array.length_to_slice (a : Array α n) :
  a.to_slice.length = n := by
  simp only [Slice.length, Array.to_slice, List.Vector.length_val]

@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::eq"]
def core.array.equality.PartialEqArray.eq
  {T : Type} {U : Type} {N : Usize} (partialEqInst : core.cmp.PartialEq T U)
  (a0 : Array T N) (a1 : Array U N) : Result Bool := do
  if a0.length = a1.length then
    -- We mimick as much as possible the Rust implementation
    List.allM (fun (x, y) => do let b ← partialEqInst.ne x y; ok (¬ b)) (List.zip a0.val a1.val)
  else .ok false

@[rust_fun "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::ne"]
def core.array.equality.PartialEqArray.ne
  {T : Type} {U : Type} {N : Usize} (partialEqInst : core.cmp.PartialEq T U)
  (a0 : Array T N) (a1 : Array U N) : Result Bool := do
  let b ← core.array.equality.PartialEqArray.eq partialEqInst a0 a1
  ok (¬ b)

/-- `<[T] as PartialEq<[U]>>::eq`: two slices are equal iff they have the same
    length and are elementwise equal (per the element `PartialEq`). -/
@[rust_fun "core::slice::cmp::{core::cmp::PartialEq<[@T], [@U]>}::eq"]
def core.slice.cmp.PartialEqSlice.eq
  {T : Type} {U : Type} (partialEqInst : core.cmp.PartialEq T U)
  (s0 : Slice T) (s1 : Slice U) : Result Bool := do
  if s0.length = s1.length then
    -- We mimick as much as possible the Rust implementation
    List.allM (fun (x, y) => do let b ← partialEqInst.ne x y; ok (¬ b)) (List.zip s0.val s1.val)
  else .ok false

/-- Helper -/
private theorem core.slice.cmp.allM_pairs_eq_spec {α} (p : α → α → Result Bool)
    (hp : ∀ x y, p x y ⦃ b => b ↔ x = y ⦄) :
    ∀ (l1 l2 : List α), l1.length = l2.length →
    WP.spec (List.allM (fun (xy : α × α) => p xy.1 xy.2) (List.zip l1 l2))
      (fun b => b ↔ l1 = l2) := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 hlen
    have : l2 = [] := by cases l2 <;> simp_all
    subst this
    simp only [List.zip_nil_left, List.allM, pure, spec_ok]
  | cons x xs ih =>
    intro l2 hlen
    cases l2 with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zip_cons_cons, List.allM]
      apply spec_bind (hp x y)
      intro r hr
      cases r with
      | true =>
        have hxy : x = y := hr.mp rfl
        subst hxy
        apply spec_mono (ih ys hlen)
        intro b hb
        simp only [List.cons.injEq, true_and] at *
        exact hb
      | false =>
        simp only [pure, spec_ok]
        have hne : x ≠ y := by intro h; have := hr.mpr h; simp at this
        simp [hne]

/-- Spec for homogeneous partial equality -/
theorem core.slice.cmp.PartialEqSlice.eq_homo_spec
  {α} (partialEq : core.cmp.PartialEq α α) (s1 s2 : Slice α)
  (hNe : ∀ x y, partialEq.ne x y ⦃ b => b ↔ ¬ (x = y) ⦄) :
  core.slice.cmp.PartialEqSlice.eq partialEq s1 s2 ⦃ (b : Bool) => b ↔ (s1 = s2) ⦄ := by
  unfold core.slice.cmp.PartialEqSlice.eq
  by_cases hlen : s1.length = s2.length
  · simp only [hlen, ↓reduceIte]
    apply spec_mono (core.slice.cmp.allM_pairs_eq_spec
      (fun x y => do let b ← partialEq.ne x y; ok (¬ b))
      (by
        intro x y
        apply spec_bind (hNe x y)
        intro b hb
        simp only [spec_ok]
        cases b <;> simp_all)
      s1.val s2.val hlen)
    intro b hb
    rw [Slice.eq_iff]; exact hb
  · simp only [hlen, ↓reduceIte, spec_ok]
    have hne : s1 ≠ s2 := fun h => hlen (by rw [h])
    simp [hne]

/-- `<[T] as PartialEq<[U]>>::ne`: negation of slice equality. -/
@[rust_fun "core::slice::cmp::{core::cmp::PartialEq<[@T], [@U]>}::ne"]
def core.slice.cmp.PartialEqSlice.ne
  {T : Type} {U : Type} (partialEqInst : core.cmp.PartialEq T U)
  (s0 : Slice T) (s1 : Slice U) : Result Bool := do
  if s0.length = s1.length then
    List.anyM (fun (x, y) => partialEqInst.ne x y) (List.zip s0.val s1.val)
  else .ok true

/-- Helper -/
private theorem core.slice.cmp.anyM_pairs_ne_spec {α} (p : α → α → Result Bool)
    (hp : ∀ x y, p x y ⦃ b => b ↔ ¬ (x = y) ⦄) :
    ∀ (l1 l2 : List α), l1.length = l2.length →
    WP.spec (List.anyM (fun (xy : α × α) => p xy.1 xy.2) (List.zip l1 l2))
      (fun b => b ↔ ¬ (l1 = l2)) := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 hlen
    have : l2 = [] := by cases l2 <;> simp_all
    subst this
    simp [pure, spec_ok]
  | cons x xs ih =>
    intro l2 hlen
    cases l2 with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [List.zip_cons_cons, List.anyM]
      apply spec_bind (hp x y)
      intro r hr
      cases r with
      | true =>
        simp only [pure, spec_ok]
        have hne : x ≠ y := hr.mp rfl
        simp [hne]
      | false =>
        have hxy : x = y := by by_contra h; have := hr.mpr h; simp at this
        subst hxy
        apply spec_mono (ih ys hlen)
        intro b hb
        simp only [List.cons.injEq, true_and] at *
        exact hb

/-- Spec for homogeneous partial inequality -/
theorem core.slice.cmp.PartialEqSlice.ne_homo_spec
  {α} (partialEq : core.cmp.PartialEq α α) (s1 s2 : Slice α)
  (hNe : ∀ x y, partialEq.ne x y ⦃ b => b ↔ ¬ (x = y) ⦄) :
  core.slice.cmp.PartialEqSlice.ne partialEq s1 s2 ⦃ (b : Bool) => b ↔ ¬ (s1 = s2) ⦄ := by
  unfold core.slice.cmp.PartialEqSlice.ne
  by_cases hlen : s1.length = s2.length
  · simp only [hlen, ↓reduceIte]
    apply spec_mono (core.slice.cmp.anyM_pairs_ne_spec partialEq.ne hNe s1.val s2.val hlen)
    intro b hb
    rw [Slice.eq_iff]; exact hb
  · simp only [hlen, ↓reduceIte, spec_ok]
    have hne : s1 ≠ s2 := fun h => hlen (by rw [h])
    simp [hne]

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
  {T : Type} (N : Usize) (_copyInst : core.marker.Copy T) (s : Slice T) :
  Result (core.result.Result (Array T N) core.array.TryFromSliceError) := do
  if h0: s.length = N then
    .ok (.Ok ⟨s.val, by scalar_tac⟩)
  else .ok (.Err ())

@[step]
theorem core.array.TryFromArrayCopySlice.try_from.step
    {T : Type} (N : Usize) (copyInst : core.marker.Copy T) (s : Slice T) :
    core.array.TryFromArrayCopySlice.try_from N copyInst s
    ⦃ (result : core.result.Result (Array T N) core.array.TryFromSliceError) =>
      match result with
      | .Ok a =>
        a.val = s.val ∧ a.length = N
      | .Err () => s.length ≠ N ⦄ := by
  simp only [core.array.TryFromArrayCopySlice.try_from]
  grind only [usr Usize.cMax_bound, usr Usize.cMax_bound', = spec_ok]

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

@[rust_fun "core::array::{[@T; @N]}::as_slice"]
def core.array.Array.as_slice {T : Type} {N : Usize} (a : Array T N) : Result (Slice T) :=
  ok (⟨ a.val, by scalar_tac ⟩)

/-- Model for `<[T; N] as AsRef<[T]>>::as_ref`: returns the array viewed as a slice. -/
@[rust_fun "core::array::{core::convert::AsRef<[@T; @N], [@T]>}::as_ref"]
def Array.Insts.CoreConvertAsRefSlice.as_ref
    {T : Type} {N : Usize} (a : Array T N) : Result (Slice T) :=
  ok (⟨ a.val, by scalar_tac ⟩)

/-- Model for `<[T; N] as AsMut<[T]>>::as_mut`: returns the array as a mutable slice
    plus a back-conversion that restores it to an array. -/
@[rust_fun "core::array::{core::convert::AsMut<[@T; @N], [@T]>}::as_mut"]
def Array.Insts.CoreConvertAsMutSlice.as_mut
    {T : Type} {N : Usize} (a : Array T N) :
    Result ((Slice T) × (Slice T → Array T N)) :=
  let back (s : Slice T) : Array T N :=
    if h : s.length = N then ⟨ s.val, by scalar_tac ⟩
    else a
  ok (⟨ a.val, by scalar_tac ⟩, back)

@[rust_fun "core::array::{[@T; @N]}::as_mut_slice"]
def core.array.Array.as_mut_slice
  {T : Type} {N : Usize} (a : Array T N) :
  Result (Slice T × (Slice T → Array T N)) :=
  let back (s : Slice T) : Array T N :=
    if h: s.length = N then ⟨ s.val, by scalar_tac ⟩
    else a
  ok (⟨ a.val, by scalar_tac ⟩, back)

@[step]
theorem Array.Insts.CoreConvertAsRefSlice.as_ref.spec
    {T : Type} {N : Usize} (a : Array T N) :
    Array.Insts.CoreConvertAsRefSlice.as_ref a
    ⦃ (s : Slice T) => s.val = a.val ⦄ := by
  simp [Array.Insts.CoreConvertAsRefSlice.as_ref, WP.spec_ok]

@[step]
theorem Array.Insts.CoreConvertAsMutSlice.as_mut.spec
    {T : Type} {N : Usize} (a : Array T N) :
    Array.Insts.CoreConvertAsMutSlice.as_mut a
    ⦃ (s : Slice T) (back : Slice T → Array T N) =>
      s.val = a.val ∧
      s.length = N.val ∧
      ∀ s' : Slice T, s'.length = N.val → (back s').val = s'.val ⦄ := by
  simp [Array.Insts.CoreConvertAsMutSlice.as_mut, WP.spec_ok, Slice.length]
  intro s' hs'
  simp [hs']

@[simp, step_simps]
theorem Array.index_SliceIndexRangeUsizeSlice {T : Type} {N : Usize}
    (a : Array T N) (r : core.ops.range.Range Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeUsizeSlice.index r a.to_slice := by rfl

@[step]
theorem Array.index_SliceIndexRangeUsizeSlice.step {T : Type} {N : Usize} [Inhabited T]
    (a : Array T N) (r : core.ops.range.Range Usize)
    (h0 : r.start ≤ r.end) (h1 : r.end ≤ N) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice T)) a r
    ⦃ (s : Slice T) =>
      s.val = a.val.slice r.start r.end ∧
      s.length = r.end.val - r.start.val ⦄ := by
  simp only [Array.index_SliceIndexRangeUsizeSlice]
  have hts : a.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index, UScalar.le_equiv, Slice.length]
  split
  · simp [spec_ok, Array.to_slice]; scalar_tac
  · scalar_tac

@[step]
theorem Array.index_mut_SliceIndexRangeUsizeSlice.step {T : Type} {N : Usize} [Inhabited T]
    (a : Array T N) (r : core.ops.range.Range Usize)
    (h0 : r.start ≤ r.end) (h1 : r.end ≤ N) :
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice T)) a r
    ⦃ (s : Slice T) (back : Slice T → Array T N) =>
      s.val = a.val.slice r.start r.end ∧
      s.length = r.end.val - r.start.val ∧
      ∀ s', (back s').val = a.val.setSlice! r.start.val s'.val ⦄ := by
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut]
  have hts : a.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    UScalar.le_equiv, Slice.length]
  split
  · simp [spec_ok, Array.from_slice, Array.to_slice]
    simp_lists; scalar_tac
  · scalar_tac

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
    ⦃ (s : Slice T) (back : Slice T → Array T N) =>
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
    ⦃ (s : Slice T) (back : Slice T → Array T N) =>
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

@[reducible, rust_trait_impl "core::convert::AsRef<[@T; @N], [@T]>"]
def Array.Insts.CoreConvertAsRefSlice (T : Type) (N : Std.Usize) :
  core.convert.AsRef (Array T N) (Slice T) := {
  as_ref := Array.Insts.CoreConvertAsRefSlice.as_ref
}

@[reducible, rust_trait_impl "core::convert::AsMut<[@T; @N], [@T]>"]
def Array.Insts.CoreConvertAsMutSlice (T : Type) (N : Std.Usize) :
  core.convert.AsMut (Array T N) (Slice T) := {
  as_mut := Array.Insts.CoreConvertAsMutSlice.as_mut
}

end Aeneas.Std
