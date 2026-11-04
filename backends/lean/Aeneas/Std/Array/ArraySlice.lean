module
public import Aeneas.Std.Core.Fmt
public import Aeneas.Std.Array.Array
public import Aeneas.Std.Slice
public import Aeneas.Std.Range
public import Aeneas.Data.List.List
public import Aeneas.Std.Core.Convert
public import Aeneas.Std.Core.Cmp
import all Init.Data.List.Control
public section

/-! Array definitions which mention slices -/

namespace Aeneas.Std

open Result Error core.ops.range WP

attribute [-simp] List.getElem!_eq_getElem?_getD

/-! Array to slice/subslices -/

/-- Array to slice conversion on raw values (used by the compiler for the unsizing casts).
    See `Array.as_slice` for the model of `<[T; N]>::as_slice`. -/
@[expose, step_pure_def]
def Array.to_slice {α : Type u} {n : Usize} (v : Array α n) : Slice α :=
  .from  v.val (by scalar_tac)

@[expose] def Array.from_slice {α : Type u} {n : Usize} (a : Array α n) (s : Slice α) : Array α n :=
  if h: s.val.length = n.val then
    .from s.val (by simp [*])
  else a -- Unreachable case

@[simp]
theorem Array.from_slice_val {α : Type u} {n : Usize} (a : Array α n) (ns : Slice α) (h : ns.val.length = n.val) :
  (from_slice a ns).val = ns.val
  := by simp [from_slice, *]

/-- Array to mutable slice conversion on raw values.
    See `Array.as_mut_slice` for the model of `<[T; N]>::as_mut_slice`. -/
@[expose]
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

/-- Model of `<[T; N]>::as_slice` -/
@[expose, step_pure_def, rust_fun "core::array::{[@T; @N]}::as_slice" -canFail]
def Array.as_slice {α : Type u} {n : Usize} (a : SharedBorrow (Array α n)) :
  SharedBorrow (Slice α) :=
  SharedBorrow.mk a.val.to_slice

/-- Model of `<[T; N]>::as_mut_slice` -/
@[expose, rust_fun "core::array::{[@T; @N]}::as_mut_slice" -canFail]
def Array.as_mut_slice {α : Type u} {n : Usize} (a : MutBorrow (Array α n)) :
  MutBorrow (Slice α) × (Slice α → Array α n) :=
  (MutBorrow.mk a.val.to_slice, Array.from_slice a.val)

/-- Step theorem for `lift (Array.as_mut_slice a)` with curried postcondition. -/
@[step]
theorem Array.as_mut_slice_spec {α : Type u} {n : Usize} (a : MutBorrow (Array α n)) :
  (lift (Array.as_mut_slice a))
  ⦃ (s : MutBorrow (Slice α)) (back : Slice α → Array α n) =>
    s.val.val = a.val.val ∧ back = Array.from_slice a.val ⦄ := by
  simp [lift, as_mut_slice, to_slice, WP.spec_ok]

@[expose] def Array.subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) : Result (Slice α) :=
  if r.start.val < r.end.val ∧ r.end.val ≤ a.val.length then
    ok (.from (a.val.slice r.start.val r.end.val)
          (by
            have := a.val.slice_length_le r.start.val r.end.val
            scalar_tac))
  else
    fail panic

@[step]
theorem Array.subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize)
  (h0 : r.start.val < r.end.val) (h1 : r.end.val ≤ a.val.length) :
  subslice a r ⦃ s =>
  s.val = a.val.slice r.start.val r.end.val ∧
  (∀ i, i + r.start.val < r.end.val → s.val[i]! = a.val[r.start.val + i]!) ⦄
  := by
  simp only [Slice.from_val, subslice, true_and, h0, h1, ↓reduceIte, spec_ok, true_and]
  intro i _
  have := List.getElem!_slice r.start.val r.end.val i a.val (by scalar_tac)
  simp only [this]


@[expose] def Array.update_subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) (s : Slice α) : Result (Array α n) :=
  -- TODO: not completely sure here
  if h: r.start.val < r.end.val ∧ r.end.val ≤ a.length ∧ s.val.length = r.end.val - r.start.val then
    ok (.from (a.val.setSlice! r.start s.val) (by scalar_tac))
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

@[expose, rust_fun "core::array::{core::ops::index::Index<[@T; @N], @I, @O>}::index"]
def core.array.Array.index
  {T I Output : Type _} {N : Usize} (inst : core.ops.index.Index (Slice T) I Output)
  (a : SharedBorrow (Array T N)) (i : I) : Result (SharedBorrow Output) :=
  inst.index (SharedBorrow.mk a.val.to_slice) i

@[expose, rust_fun "core::array::{core::ops::index::IndexMut<[@T; @N], @I, @O>}::index_mut"]
def core.array.Array.index_mut
  {T I Output : Type _} {N : Usize} (inst : core.ops.index.IndexMut (Slice T) I Output)
  (a : MutBorrow (Array T N)) (i : I) :
  Result (MutBorrow Output × (Output → Array T N)) := do
  let (s, back) ← inst.index_mut (MutBorrow.mk a.val.to_slice) i
  ok (s, fun o => Array.from_slice a.val (back o))

@[expose, rust_trait_impl "core::ops::index::Index<[@T; @N], @I, @O>"]
def core.ops.index.IndexArray {T I Output : Type _} {N : Usize}
  (inst : core.ops.index.Index (Slice T) I Output) :
  core.ops.index.Index (Array T N) I Output := {
  index := core.array.Array.index inst
}

@[expose, rust_trait_impl "core::ops::index::IndexMut<[@T; @N], @I, @O>"]
def core.ops.index.IndexMutArray {T I Output : Type _} {N : Usize}
  (inst : core.ops.index.IndexMut (Slice T) I Output) :
  core.ops.index.IndexMut (Array T N) I Output := {
  indexInst := core.ops.index.IndexArray inst.indexInst
  index_mut := core.array.Array.index_mut inst
}

@[expose, reducible, rust_type "core::array::TryFromSliceError"]
def core.array.TryFromSliceError := Unit

@[simp, simp_lists_safe, grind =, agrind =]
theorem Array.val_to_slice {α} {n} (a : Array α n) : a.to_slice.val = a.val := by
  simp only [Array.to_slice, Slice.from_val]

@[simp, simp_lists_safe, simp_scalar_safe, scalar_tac a.to_slice, grind =, agrind =]
theorem Array.length_to_slice (a : Array α n) :
  a.to_slice.length = n := by
  simp only [Slice.length, Array.to_slice, Slice.from_val, Array.property]

@[expose, rust_fun "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::eq"]
def core.array.equality.PartialEqArray.eq
  {T : Type _} {U : Type _} {N : Usize} (partialEqInst : core.cmp.PartialEq T U)
  (a0 : SharedBorrow (Array T N)) (a1 : SharedBorrow (Array U N)) : Result Bool := do
  if a0.val.length = a1.val.length then
    -- We mimick as much as possible the Rust implementation
    List.allM (fun (x, y) => do let b ← partialEqInst.ne (SharedBorrow.mk x) (SharedBorrow.mk y); ok (¬ b))
      (List.zip a0.val.val a1.val.val)
  else .ok false

@[expose, rust_fun "core::array::equality::{core::cmp::PartialEq<[@T; @N], [@U; @N]>}::ne"]
def core.array.equality.PartialEqArray.ne
  {T : Type _} {U : Type _} {N : Usize} (partialEqInst : core.cmp.PartialEq T U)
  (a0 : SharedBorrow (Array T N)) (a1 : SharedBorrow (Array U N)) : Result Bool := do
  let b ← core.array.equality.PartialEqArray.eq partialEqInst a0 a1
  ok (¬ b)

/-- `<[T] as PartialEq<[U]>>::eq`: two slices are equal iff they have the same
    length and are elementwise equal (per the element `PartialEq`). -/
@[expose, rust_fun "core::slice::cmp::{core::cmp::PartialEq<[@T], [@U]>}::eq"]
def core.slice.cmp.PartialEqSlice.eq
  {T : Type _} {U : Type _} (partialEqInst : core.cmp.PartialEq T U)
  (s0 : SharedBorrow (Slice T)) (s1 : SharedBorrow (Slice U)) : Result Bool := do
  if s0.val.length = s1.val.length then
    -- We mimick as much as possible the Rust implementation
    List.allM (fun (x, y) => do let b ← partialEqInst.ne (SharedBorrow.mk x) (SharedBorrow.mk y); ok (¬ b))
      (List.zip s0.val.val s1.val.val)
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
  {α} (partialEq : core.cmp.PartialEq α α) (s1 s2 : SharedBorrow (Slice α))
  (hNe : ∀ x y, partialEq.ne x y ⦃ b => b ↔ ¬ (x.val = y.val) ⦄) :
  core.slice.cmp.PartialEqSlice.eq partialEq s1 s2 ⦃ (b : Bool) => b ↔ (s1.val = s2.val) ⦄ := by
  unfold core.slice.cmp.PartialEqSlice.eq
  by_cases hlen : s1.val.length = s2.val.length
  · simp only [hlen, ↓reduceIte]
    apply spec_mono (core.slice.cmp.allM_pairs_eq_spec
      (fun x y => do let b ← partialEq.ne (SharedBorrow.mk x) (SharedBorrow.mk y); ok (¬ b))
      (by
        intro x y
        apply spec_bind (hNe (SharedBorrow.mk x) (SharedBorrow.mk y))
        intro b hb
        simp only [spec_ok]
        cases b <;> simp_all)
      s1.val.val s2.val.val hlen)
    intro b hb
    rw [Slice.eq_iff]; exact hb
  · simp only [hlen, ↓reduceIte, spec_ok]
    have hne : s1.val ≠ s2.val := fun h => hlen (by rw [h])
    simp [hne]

/-- `<[T] as PartialEq<[U]>>::ne`: negation of slice equality. -/
@[expose, rust_fun "core::slice::cmp::{core::cmp::PartialEq<[@T], [@U]>}::ne"]
def core.slice.cmp.PartialEqSlice.ne
  {T : Type _} {U : Type _} (partialEqInst : core.cmp.PartialEq T U)
  (s0 : SharedBorrow (Slice T)) (s1 : SharedBorrow (Slice U)) : Result Bool := do
  if s0.val.length = s1.val.length then
    List.anyM (fun (x, y) => partialEqInst.ne (SharedBorrow.mk x) (SharedBorrow.mk y))
      (List.zip s0.val.val s1.val.val)
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
  {α} (partialEq : core.cmp.PartialEq α α) (s1 s2 : SharedBorrow (Slice α))
  (hNe : ∀ x y, partialEq.ne x y ⦃ b => b ↔ ¬ (x.val = y.val) ⦄) :
  core.slice.cmp.PartialEqSlice.ne partialEq s1 s2 ⦃ (b : Bool) => b ↔ ¬ (s1.val = s2.val) ⦄ := by
  unfold core.slice.cmp.PartialEqSlice.ne
  by_cases hlen : s1.val.length = s2.val.length
  · simp only [hlen, ↓reduceIte]
    apply spec_mono (core.slice.cmp.anyM_pairs_ne_spec
      (fun x y => partialEq.ne (SharedBorrow.mk x) (SharedBorrow.mk y))
      (fun x y => hNe (SharedBorrow.mk x) (SharedBorrow.mk y)) s1.val.val s2.val.val hlen)
    intro b hb
    rw [Slice.eq_iff]; exact hb
  · simp only [hlen, ↓reduceIte, spec_ok]
    have hne : s1.val ≠ s2.val := fun h => hlen (by rw [h])
    simp [hne]

@[expose, rust_fun "core::array::{core::fmt::Debug<core::array::TryFromSliceError>}::fmt"]
def core.array.DebugTryFromSliceError.fmt
  (_ : SharedBorrow core.array.TryFromSliceError) (fmt : MutBorrow core.fmt.Formatter) :
  Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  -- TODO: this model is simplistic
  .ok (.Ok (), fmt.val)

@[expose, reducible, rust_trait_impl
  "core::fmt::Debug<core::array::TryFromSliceError>"]
def core.fmt.DebugTryFromSliceError : core.fmt.Debug
  core.array.TryFromSliceError := {
  fmt := core.array.DebugTryFromSliceError.fmt
}

@[expose, rust_fun "core::array::{core::convert::TryFrom<[@T; @N], &'0 [@T], core::array::TryFromSliceError>}::try_from"]
def core.array.TryFromArrayCopySlice.try_from
  {T : Type _} (N : Usize) (_copyInst : core.marker.Copy T) (s : SharedBorrow (Slice T)) :
  Result (core.result.Result (Array T N) core.array.TryFromSliceError) := do
  if h0: s.val.length = N then
    .ok (.Ok (.from s.val.val (by scalar_tac)))
  else .ok (.Err ())

@[step]
theorem core.array.TryFromArrayCopySlice.try_from.step
    {T : Type _} (N : Usize) (copyInst : core.marker.Copy T) (s : SharedBorrow (Slice T)) :
    core.array.TryFromArrayCopySlice.try_from N copyInst s
    ⦃ (result : core.result.Result (Array T N) core.array.TryFromSliceError) =>
      match result with
      | .Ok a =>
        a.val = s.val.val ∧ a.length = N
      | .Err () => s.val.length ≠ N ⦄ := by
  simp only [core.array.TryFromArrayCopySlice.try_from]
  grind only [usr Usize.cMax_bound, usr Usize.cMax_bound', = spec_ok, !Array.from_val]

@[expose, rust_fun "core::array::{core::convert::TryFrom<&'a [@T; @N], &'a [@T], core::array::TryFromSliceError>}::try_from"]
def core.array.TryFromSharedArraySlice.try_from
  {T : Type _} (N : Usize) (s : SharedBorrow (Slice T)) :
  Result (core.result.Result (SharedBorrow (Array T N)) core.array.TryFromSliceError) := do
  if h: s.val.length = N.val then .ok (.Ok (SharedBorrow.mk (.from s.val.val (by scalar_tac))))
  else .ok (.Err ())

@[expose, reducible, rust_trait_impl
  "core::convert::TryFrom<&'a [@T; @N], &'a [@T], core::array::TryFromSliceError>"]
def core.convert.TryFromSharedArraySliceTryFromSliceError (T : Type _) (N : Usize) :
  core.convert.TryFrom (SharedBorrow (Array T N)) (SharedBorrow (Slice T))
  core.array.TryFromSliceError := {
  try_from := core.array.TryFromSharedArraySlice.try_from N
}

@[expose, rust_fun "core::array::{core::convert::TryFrom<&'a mut [@T; @N], &'a mut [@T], core::array::TryFromSliceError>}::try_from"]
def core.array.TryFromMutArraySlice.try_from
  {T : Type _} (N : Usize) (s : MutBorrow (Slice T)) :
  Result (
    core.result.Result (MutBorrow (Array T N)) core.array.TryFromSliceError ×
    (core.result.Result (MutBorrow (Array T N)) core.array.TryFromSliceError → Slice T)) :=
  if h: s.val.length = N.val then
    let back (a : core.result.Result (MutBorrow (Array T N)) core.array.TryFromSliceError) :
      Slice T :=
      match a with
      | .Ok a =>
        if a.val.length = s.val.length then .from a.val.val (by scalar_tac)
        else s.val
      | _ => s.val
    ok ((.Ok (MutBorrow.mk (.from s.val.val (by scalar_tac))), back))
  else ok ((.Err (), fun _ => s.val))

/-- Model for `<[T; N] as AsRef<[T]>>::as_ref`: returns the array viewed as a slice. -/
@[expose, rust_fun "core::array::{core::convert::AsRef<[@T; @N], [@T]>}::as_ref"]
def Array.Insts.CoreConvertAsRefSlice.as_ref
    {T : Type _} {N : Usize} (a : SharedBorrow (Array T N)) : Result (SharedBorrow (Slice T)) :=
  ok (SharedBorrow.mk (.from a.val.val (by scalar_tac)))

/-- Model for `<[T; N] as AsMut<[T]>>::as_mut`: returns the array as a mutable slice
    plus a back-conversion that restores it to an array. -/
@[expose, rust_fun "core::array::{core::convert::AsMut<[@T; @N], [@T]>}::as_mut"]
def Array.Insts.CoreConvertAsMutSlice.as_mut
    {T : Type _} {N : Usize} (a : MutBorrow (Array T N)) :
    Result ((MutBorrow (Slice T)) × (Slice T → Array T N)) :=
  let back (s : Slice T) : Array T N :=
    if h : s.length = N then .from  s.val (by scalar_tac)
    else a.val
  ok (MutBorrow.mk (.from a.val.val (by scalar_tac)), back)

@[step]
theorem Array.Insts.CoreConvertAsRefSlice.as_ref.spec
    {T : Type _} {N : Usize} (a : SharedBorrow (Array T N)) :
    Array.Insts.CoreConvertAsRefSlice.as_ref a
    ⦃ (s : SharedBorrow (Slice T)) => s.val.val = a.val.val ⦄ := by
  simp [Array.Insts.CoreConvertAsRefSlice.as_ref, WP.spec_ok]

@[step]
theorem Array.Insts.CoreConvertAsMutSlice.as_mut.spec
    {T : Type _} {N : Usize} (a : MutBorrow (Array T N)) :
    Array.Insts.CoreConvertAsMutSlice.as_mut a
    ⦃ (s : MutBorrow (Slice T)) (back : Slice T → Array T N) =>
      s.val.val = a.val.val ∧
      s.val.length = N.val ∧
      ∀ s' : Slice T, s'.length = N.val → (back s').val = s'.val ⦄ := by
  simp [Array.Insts.CoreConvertAsMutSlice.as_mut, WP.spec_ok, Slice.length]
  intro s' hs'
  simp [hs']

@[simp, step_simps]
theorem Array.index_SliceIndexRangeUsizeSlice {T : Type _} {N : Usize}
    (a : SharedBorrow (Array T N)) (r : core.ops.range.Range Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeUsizeSlice.index r (SharedBorrow.mk a.val.to_slice) := by rfl

@[step]
theorem Array.index_SliceIndexRangeUsizeSlice.step {T : Type _} {N : Usize} [Inhabited T]
    (a : SharedBorrow (Array T N)) (r : core.ops.range.Range Usize)
    (h0 : r.start ≤ r.end) (h1 : r.end ≤ N) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice T)) a r
    ⦃ (s : SharedBorrow (Slice T)) =>
      s.val.val = a.val.val.slice r.start r.end ∧
      s.val.length = r.end.val - r.start.val ⦄ := by
  simp only [Array.index_SliceIndexRangeUsizeSlice]
  have hts : a.val.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index, UScalar.le_equiv, Slice.length]
  split
  · simp [spec_ok, Array.to_slice]; scalar_tac
  · scalar_tac

@[step]
theorem Array.index_mut_SliceIndexRangeUsizeSlice.step {T : Type _} {N : Usize} [Inhabited T]
    (a : MutBorrow (Array T N)) (r : core.ops.range.Range Usize)
    (h0 : r.start ≤ r.end) (h1 : r.end ≤ N) :
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice T)) a r
    ⦃ (s : MutBorrow (Slice T)) (back : Slice T → Array T N) =>
      s.val.val = a.val.val.slice r.start r.end ∧
      s.val.length = r.end.val - r.start.val ∧
      ∀ s', (back s').val = a.val.val.setSlice! r.start.val s'.val ⦄ := by
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut]
  have hts : a.val.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    UScalar.le_equiv, Slice.length]
  split
  · simp [spec_ok, Array.from_slice, Array.to_slice]
    simp_lists; scalar_tac
  · scalar_tac

-- Array index/index_mut with RangeTo

@[simp, step_simps]
theorem Array.index_SliceIndexRangeToUsizeSlice {T : Type _} {N : Usize}
    (a : SharedBorrow (Array T N)) (r : core.ops.range.RangeTo Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeToUsizeSlice.index r (SharedBorrow.mk a.val.to_slice) := by rfl

@[step]
theorem Array.index_mut_SliceIndexRangeToUsizeSlice {T : Type _} {N : Usize}
    (a : MutBorrow (Array T N)) (r : core.ops.range.RangeTo Usize)
    (h : r.end ≤ N) :
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice T)) a r
    ⦃ (s : MutBorrow (Slice T)) (back : Slice T → Array T N) =>
      s.val.val = a.val.val.slice 0 r.end ∧
      s.val.length = r.end.val ∧
      ∀ s', (back s').val = a.val.val.setSlice! 0 s'.val ⦄ := by
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut]
  have hts : a.val.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  simp only [core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    show (r.end : Usize) ≤ a.val.to_slice.length from by scalar_tac]
  simp
  assumption

-- Array index/index_mut with RangeFrom

@[simp, step_simps]
theorem Array.index_SliceIndexRangeFromUsizeSlice {T : Type _} {N : Usize}
    (a : SharedBorrow (Array T N)) (r : core.ops.range.RangeFrom Usize) :
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice T)) a r =
    core.slice.index.SliceIndexRangeFromUsizeSlice.index r (SharedBorrow.mk a.val.to_slice) := by rfl

@[step]
theorem Array.index_mut_SliceIndexRangeFromUsizeSlice {T : Type _} {N : Usize}
    (a : MutBorrow (Array T N)) (r : core.ops.range.RangeFrom Usize)
    (h : r.start ≤ N) :
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice T)) a r
    ⦃ (s : MutBorrow (Slice T)) (back : Slice T → Array T N) =>
      s.val.val = a.val.val.drop r.start ∧
      s.val.length = N.val - r.start.val ∧
      ∀ s', (back s').val = a.val.val.setSlice! r.start.val s'.val ⦄ := by
  simp only [core.array.Array.index_mut, core.ops.index.IndexMutSlice,
    core.slice.index.Slice.index_mut]
  have hts : a.val.to_slice.length = N := by simp [Array.to_slice, Slice.length]
  simp only [core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    Slice.drop,
    show (r.start : Usize) ≤ a.val.to_slice.length from by scalar_tac]
  simp

@[expose, reducible, rust_trait_impl "core::convert::AsRef<[@T; @N], [@T]>"]
def Array.Insts.CoreConvertAsRefSlice (T : Type _) (N : Std.Usize) :
  core.convert.AsRef (Array T N) (Slice T) := {
  as_ref := Array.Insts.CoreConvertAsRefSlice.as_ref
}

@[expose, reducible, rust_trait_impl "core::convert::AsMut<[@T; @N], [@T]>"]
def Array.Insts.CoreConvertAsMutSlice (T : Type _) (N : Std.Usize) :
  core.convert.AsMut (Array T N) (Slice T) := {
  as_mut := Array.Insts.CoreConvertAsMutSlice.as_mut
}

end Aeneas.Std
