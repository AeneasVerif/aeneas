/- Arrays/Slices -/
import Aeneas.Data.List
import Aeneas.Std.Array.Core
import Aeneas.Std.Range
import Aeneas.Std.Core.Ops
import Aeneas.Std.RawPtr
import Aeneas.Tactic.Simp.SimpScalar.SimpScalar

namespace Aeneas.Std

open Result Error core.ops.range WP

attribute [-simp] List.getElem!_eq_getElem?_getD

/-!
# Slice
-/

def Slice (α : Type u) := { l : List α // l.length ≤ Usize.max }

/-- We need this to coerce slices to lists without marking `Slice` as reducible.
    Also not that we *do not* want to mark `Slice` as reducible: it triggers issues.
-/
instance (α : Type u) : CoeOut (Slice α) (List α) where
  coe := λ v => v.val

instance [BEq α] : BEq (Slice α) := SubtypeBEq _

instance [BEq α] [LawfulBEq α] : LawfulBEq (Slice α) := SubtypeLawfulBEq _

theorem Slice.length_ineq {α : Type u} (s : Slice α) : s.val.length ≤ Usize.max := by
  cases s; simp[*]

@[simp, scalar_tac_simps, simp_scalar_safe, simp_lists_safe]
abbrev Slice.length {α : Type u} (v : Slice α) : Nat := v.val.length

@[simp, scalar_tac_simps, simp_scalar_safe, simp_lists_safe]
abbrev Slice.v {α : Type u} (v : Slice α) : List α := v.val

example {a: Type u} (v : Slice a) : v.length ≤ Usize.max := by
  scalar_tac

def Slice.new (α : Type u) : Slice α := ⟨ [], by simp ⟩

@[rust_fun "core::slice::{[@T]}::len" -canFail -lift]
abbrev Slice.len {α : Type u} (v : Slice α) : Usize :=
  Usize.ofNatCore v.val.length (by scalar_tac)

@[simp, scalar_tac_simps]
theorem Slice.len_val {α : Type u} (v : Slice α) : (Slice.len v).val = v.length :=
  by simp

@[reducible] instance {α : Type u} : GetElem (Slice α) Nat α (fun a i => i < a.val.length) where
  getElem a i h := getElem a.val i h

@[simp, grind =, simp_lists_safe]
theorem Slice.getElem_Nat_eq {α : Type u} (v : Slice α) (i : Nat) (h : i < v.val.length) :
    v[i] = v.val[i] := rfl

@[reducible] instance {α : Type u} : GetElem? (Slice α) Nat α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Slice.getElem?_Nat_eq {α : Type u} (v : Slice α) (i : Nat) : v[i]? = v.val[i]? := by rfl

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Slice.getElem!_Nat_eq {α : Type u} [Inhabited α] (v : Slice α) (i : Nat) : v[i]! = v.val[i]! := by
  simp only [instGetElem?SliceNatLtLengthValListLeMax, List.getElem!_eq_getElem?_getD]; split <;> simp_all
  rfl

@[reducible] instance {α : Type u} : GetElem (Slice α) Usize α (fun a i => i.val < a.val.length) where
  getElem a i h := getElem a.val i.val h

@[reducible] instance {α : Type u} : GetElem? (Slice α) Usize α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i.val

@[simp, scalar_tac_simps, simp_lists_hyps_simps] theorem Slice.getElem?_Usize_eq {α : Type u} (v : Slice α) (i : Usize) : v[i]? = v.val[i.val]? := by rfl
@[simp, scalar_tac_simps, simp_lists_hyps_simps] theorem Slice.getElem!_Usize_eq {α : Type u} [Inhabited α] (v : Slice α) (i : Usize) : v[i]! = v.val[i.val]! := by
  simp only [instGetElem?SliceUsizeLtNatValLengthValListLeMax, List.getElem!_eq_getElem?_getD]; split <;> simp_all
  rfl

@[simp, scalar_tac_simps, simp_lists_hyps_simps] abbrev Slice.get? {α : Type u} (v : Slice α) (i : Nat) : Option α := getElem? v i
@[simp, scalar_tac_simps, simp_lists_hyps_simps] abbrev Slice.get! {α : Type u} [Inhabited α] (v : Slice α) (i : Nat) : α := getElem! v i

def Slice.setAtNat {α : Type u} (v: Slice α) (i: Nat) (x: α) : Slice α :=
  ⟨ v.val.set i x, by have := v.property; simp [*] ⟩

def Slice.set {α : Type u} (v: Slice α) (i: Usize) (x: α) : Slice α :=
  Slice.setAtNat v i.val x

def Slice.set_opt {α : Type u} (v: Slice α) (i: Usize) (x: Option α) : Slice α :=
  ⟨ v.val.set_opt i.val x, by have := v.property; simp [*] ⟩

def Slice.drop {α} (s : Slice α) (i : Usize) : Slice α :=
  ⟨ s.val.drop i.val, by scalar_tac ⟩

@[simp, simp_lists_safe]
theorem Slice.getElem!_val_drop {T} (s : Slice T) (i : Usize) :
  (s.drop i).val = s.val.drop i := by
  simp [drop]

@[simp]
abbrev Slice.slice {α : Type u} [Inhabited α] (s : Slice α) (i j : Nat) : List α :=
  s.val.slice i j

def Slice.index_usize {α : Type u} (v: Slice α) (i: Usize) : Result α :=
  match v[i]? with
  | none => fail .arrayOutOfBounds
  | some x => ok x

theorem Slice.eq_iff {α} (s0 s1 : Slice α) : s0 = s1 ↔ s0.val = s1.val := by
  simp only [Slice, Subtype.ext_iff]

@[rust_fun "core::slice::{[@T]}::is_empty", simp]
def core.slice.Slice.is_empty {T : Type} (s : Slice T) : Result Bool := ok (s.length = 0)

@[step]
theorem core.slice.Slice.is_empty_spec {T : Type} (s : Slice T) :
  core.slice.Slice.is_empty s ⦃ b => b = (s.length = 0) ⦄ := by
  simp only [is_empty, Slice.length, List.length_eq_zero_iff, eq_iff_iff, spec_ok,
    decide_eq_true_eq]

@[step]
theorem Slice.index_usize_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.val < v.length) :
  v.index_usize i ⦃ x => x = v.val[i.val]! ⦄ := by
  simp only [index_usize]
  simp only [length, getElem?_Usize_eq] at *
  simp only [List.getElem?_eq_getElem, List.getElem!_eq_getElem?_getD, Option.getD_some, hbound, spec_ok]

@[simp, scalar_tac_simps, simp_lists_hyps_simps, grind =]
theorem Slice.set_val_eq {α : Type u} (v: Slice α) (i: Usize) (x: α) :
  (v.set i x) = v.val.set i.val x := by
  simp [set, setAtNat]

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Slice.set_opt_val_eq {α : Type u} (v: Slice α) (i: Usize) (x: Option α) :
  (v.set_opt i x) = v.val.set_opt i.val x := by
  simp [set_opt]


/-- Using `↓` to eagerly simplify combinations of `set` and `getElem!` in expressions like:
`(((l.set i0 x0) ...).set in xn)[j]!`

Otherwise we might lose a lot of time reordering the `set` expressions.
-/
@[simp↓, simp_lists_safe↓]
theorem Slice.getElem!_Usize_set_ne
  {α : Type u} [Inhabited α] (a: Slice α) (i j : Usize) (x: α)
  (h : i.val ≠ j.val) : (a.set i x)[j]! = a[j]!
  := by
  simp only [getElem!_Usize_eq, set_val_eq]; grind

@[simp↓, simp_lists_safe↓]
theorem Slice.getElem!_Usize_set_eq
  {α : Type u} [Inhabited α] (a: Slice α) (i i' : Usize) (x: α)
  (h : i = i' ∧ i'.val < a.length) : getElem! (a.set i x) i' = x
  := by
  simp only [getElem!_Usize_eq, set_val_eq]; grind

/-- Using `↓` to eagerly simplify combinations of `set` and `getElem!` in expressions like:
`(((l.set i0 x0) ...).set in xn)[j]!`

Otherwise we might lose a lot of time reordering the `set` expressions.
-/
@[simp↓, simp_lists_safe↓]
theorem Slice.getElem!_Nat_set_ne
  {α : Type u} [Inhabited α] (a: Slice α) (i : Usize) (j : Nat) (x: α)
  (h : i.val ≠ j) : (a.set i x)[j]! = a[j]!
  := by simp only [getElem!_Nat_eq, set_val_eq]; grind

@[simp↓, simp_lists_safe↓]
theorem Slice.getElem!_Nat_set_eq
  {α : Type u} [Inhabited α] (a: Slice α) (i : Usize) (i' : Nat) (x: α)
  (h : i.val = i' ∧ i' < a.length) : getElem! (a.set i x) i' = x
  := by simp only [getElem!_Nat_eq, set_val_eq]; grind

@[simp_lists_safe]
theorem Slice.Inhabited_getElem_eq_getElem! {α} [Inhabited α] (v : Slice α) (i : ℕ) (hi : i < v.length) :
    v[i] = v[i]! := by
  rw [Slice.getElem!_Nat_eq]
  exact List.Inhabited_getElem_eq_getElem! v.val i hi

theorem Slice.ext_getElem {α} {s1 s2 : Slice α}
    (hlen : s1.length = s2.length)
    (hget : ∀ (i : Nat) (h1 : i < s1.length) (h2 : i < s2.length), s1[i] = s2[i]) :
    s1 = s2 := by
  apply Subtype.ext
  exact List.ext_getElem (by simp_all) fun i h1 h2 => hget i h1 h2

@[simp, scalar_tac_simps, simp_lists_safe, grind =, agrind =]
theorem Slice.set_length {α : Type u} (v: Slice α) (i: Usize) (x: α) :
  (v.set i x).length = v.length := by simp

def Slice.update {α : Type u} (v: Slice α) (i: Usize) (x: α) : Result (Slice α) :=
  match v.val[i.val]? with
  | none => fail .arrayOutOfBounds
  | some _ =>
    ok ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

@[step]
theorem Slice.update_spec {α : Type u} (v: Slice α) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  v.update i x ⦃ nv => nv = v.set i x ⦄ := by
  simp only [update, set, setAtNat]
  simp at *
  simp [*]

def Slice.index_mut_usize {α : Type u} (v: Slice α) (i: Usize) :
  Result (α × (α → Slice α)) := do
  let x ← Slice.index_usize v i
  ok (x, Slice.set v i)

@[step]
theorem Slice.index_mut_usize_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.val < v.length) :
  v.index_mut_usize i ⦃ p => p = (v.val[i.val]!, Slice.set v i) ⦄ := by
  simp only [index_mut_usize, Bind.bind, bind]
  have ⟨ x, h ⟩ := spec_imp_exists (Slice.index_usize_spec v i hbound)
  simp [h]

@[simp]
theorem Slice.update_index_eq α [Inhabited α] (x : Slice α) (i : Usize) :
  x.set i (x.val[i.val]!) = x := by
  simp only [Slice, Subtype.ext_iff, set_val_eq, List.set_getElem!]

def Slice.subslice {α : Type u} (s : Slice α) (r : Range Usize) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end.val ∧ r.end.val ≤ s.length then
    ok ⟨ s.val.slice r.start.val r.end.val,
          by
            have := s.val.slice_length_le r.start.val r.end.val
            scalar_tac ⟩
  else
    fail panic

@[step]
theorem Slice.subslice_spec {α : Type u} [Inhabited α] (s : Slice α) (r : Range Usize)
  (h0 : r.start.val < r.end.val) (h1 : r.end.val ≤ s.val.length) :
  subslice s r ⦃ ns => ns.val = s.slice r.start.val r.end.val ∧
  (∀ i, i + r.start.val < r.end.val → ns[i]! = s[r.start.val + i]!) ⦄
  := by
  simp_all only [subslice, length, and_self, ite_true, slice, spec_ok, true_and]
  intro i _
  have := List.getElem!_slice r.start.val r.end.val i s.val (by scalar_tac)
  simp only [List.getElem!_eq_getElem?_getD, getElem!_Nat_eq] at *
  apply this

def Slice.update_subslice {α : Type u} (s : Slice α) (r : Range Usize) (ss : Slice α) : Result (Slice α) :=
  -- TODO: not completely sure here
  if h: r.start.val < r.end.val ∧ r.end.val ≤ s.length ∧ ss.val.length = r.end.val - r.start.val then
    ok ⟨ s.val.setSlice! r.start.val ss.val, by scalar_tac ⟩
  else
    fail panic

@[step]
theorem Slice.update_subslice_spec {α : Type u} [Inhabited α] (a : Slice α) (r : Range Usize) (ss : Slice α)
  (_ : r.start.val < r.end.val) (_ : r.end.val ≤ a.length) (_ : ss.length = r.end.val - r.start.val) :
  update_subslice a r ss ⦃ na =>
    (∀ i, i < r.start.val → na[i]! = a[i]!) ∧
    (∀ i, r.start.val ≤ i → i < r.end.val → na[i]! = ss[i - r.start.val]!) ∧
    (∀ i, r.end.val ≤ i → i < a.length → na[i]! = a[i]!) ⦄ := by
  simp only [update_subslice, length, and_self, ↓reduceDIte, getElem!_Nat_eq,
    spec_ok, *]
  simp_lists

@[rust_fun "core::slice::{[@T]}::reverse" -canFail]
def core.slice.Slice.reverse {T : Type} (s : Slice T) : Slice T :=
  ⟨ s.val.reverse, by scalar_tac ⟩

@[rust_trait "core::slice::index::private_slice_index::Sealed"]
structure core.slice.index.private_slice_index.Sealed (Self : Type) where

@[rust_trait "core::slice::index::SliceIndex" (parentClauses := ["sealedInst"])]
structure core.slice.index.SliceIndex (Self T Output : Type) where
  sealedInst : core.slice.index.private_slice_index.Sealed Self
  get : Self → T → Result (Option Output)
  get_mut : Self → T → Result (Option Output × (Option Output → T))
  get_unchecked : Self → ConstRawPtr T → Result (ConstRawPtr Output)
  get_unchecked_mut : Self → MutRawPtr T → Result (MutRawPtr Output)
  index : Self → T → Result Output
  index_mut : Self → T → Result (Output × (Output → T))

@[rust_fun "core::slice::index::{core::ops::index::Index<[@T], @I, @O>}::index"]
def core.slice.index.Slice.index
  {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (slice : Slice T) (i : I) : Result Output :=
  inst.index i slice

@[rust_fun "core::slice::{[@T]}::get"]
def core.slice.Slice.get
  {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : Result (Option Output) :=
  inst.get i s

@[rust_fun "core::slice::{[@T]}::get_unchecked"]
def core.slice.Slice.get_unchecked
  {T : Type} {I : Type} {Output : Type}
  (SliceIndexInst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : Result Output :=
  -- TODO: we should actually use the `SliceIndexInst.get_unchecked` method
  sorry

@[rust_fun "core::slice::{[@T]}::get_mut"]
def core.slice.Slice.get_mut
  {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : Result ((Option Output) × (Option Output → Slice T)) :=
  inst.get_mut i s

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::get"]
def core.slice.index.SliceIndexRangeUsizeSlice.get {T : Type} (r : Range Usize) (s : Slice T) :
  Result (Option (Slice T)) :=
  if r.start ≤ r.end ∧ r.end ≤ s.length then
    ok (some ⟨ s.val.slice r.start r.end, by scalar_tac⟩)
  else ok none

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::get_mut"]
def core.slice.index.SliceIndexRangeUsizeSlice.get_mut
  {T : Type} (r : Range Usize) (s : Slice T) : Result (Option (Slice T) × (Option (Slice T) → Slice T)) :=
  if r.start ≤ r.end ∧ r.end ≤ s.length then
    ok (some ⟨ s.val.slice r.start r.end, by scalar_tac⟩,
        fun s' =>
        match s' with
        | none => s
        | some s' =>
          if h: s'.length = r.end - r.start then
            ⟨ List.setSlice! s.val r.start s'.val, by scalar_tac ⟩
          else s )
  else ok (none, fun _ => s)

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::get_unchecked"]
def core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked {T : Type} :
  Range Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr (Slice T)) :=
  -- Don't know what the model should be - for now we always fail
  fun _ _ => fail .undef

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::get_unchecked_mut"]
def core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked_mut {T : Type} :
  Range Usize → MutRawPtr (Slice T) → Result (MutRawPtr (Slice T)) :=
  -- Don't know what the model should be - for now we always fail
  fun _ _ => fail .undef

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::index"]
def core.slice.index.SliceIndexRangeUsizeSlice.index {T : Type} (r : Range Usize) (s : Slice T) : Result (Slice T) :=
  if r.start ≤ r.end ∧ r.end ≤ s.length then
    ok (⟨ s.val.slice r.start r.end, by scalar_tac⟩)
  else fail .panic

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::index_mut"]
def core.slice.index.SliceIndexRangeUsizeSlice.index_mut {T : Type} (r : Range Usize) (s : Slice T) :
  Result (Slice T × (Slice T → Slice T)) :=
  if r.start ≤ r.end ∧ r.end ≤ s.length then
    ok (⟨ s.val.slice r.start r.end, by scalar_tac⟩,
        /- The back function expects a slice of the same length as the returned subslice.
           We don't enforce this with a guard because we want totality; `setSlice!` handles
           any length gracefully. The model is correct when this condition holds, which is
           always the case for code generated by Aeneas. -/
        fun s' => ⟨ List.setSlice! s.val r.start s', by scalar_tac ⟩)
  else fail .panic

/- [core::slice::index::[T]::index_mut] -/
@[rust_fun "core::slice::index::{core::ops::index::IndexMut<[@T], @I, @O>}::index_mut"]
def core.slice.index.Slice.index_mut
  {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : Result (Output × (Output → Slice T)) :=
  inst.index_mut i s

@[rust_trait_impl "core::slice::index::private_slice_index::Sealed<core::ops::range::Range<usize>>"]
def core.slice.index.private_slice_index.SealedRangeUsize
  : core.slice.index.private_slice_index.Sealed (Range Usize) := {}

@[reducible, rust_trait_impl "core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>"]
def core.slice.index.SliceIndexRangeUsizeSlice (T : Type) :
  core.slice.index.SliceIndex (Range Usize) (Slice T) (Slice T) := {
  sealedInst := core.slice.index.private_slice_index.SealedRangeUsize
  get := core.slice.index.SliceIndexRangeUsizeSlice.get
  get_mut := core.slice.index.SliceIndexRangeUsizeSlice.get_mut
  get_unchecked := core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked
  get_unchecked_mut := core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexRangeUsizeSlice.index
  index_mut := core.slice.index.SliceIndexRangeUsizeSlice.index_mut
}

@[reducible, rust_trait_impl "core::slice::index::private_slice_index::Sealed<core::ops::range::RangeTo<usize>>"]
def core.slice.index.private_slice_index.SealedRangeToUsize :
  core.slice.index.private_slice_index.Sealed (core.ops.range.RangeTo Usize)
  := {}

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get"]
def core.slice.index.SliceIndexRangeToUsizeSlice.get
  {T : Type} (r : core.ops.range.RangeTo Usize) (s : Slice T) : Result (Option (Slice T)) :=
  if r.end ≤ s.length then
    ok (some ⟨ s.val.slice 0 r.end, by scalar_tac⟩)
  else ok none

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get_mut"]
def core.slice.index.SliceIndexRangeToUsizeSlice.get_mut
  {T : Type} (r : core.ops.range.RangeTo Usize) (s : Slice T) :
  Result ((Option (Slice T)) × (Option (Slice T) → Slice T)) :=
  if r.end ≤ s.length then
    ok (some ⟨ s.val.slice 0 r.end, by scalar_tac⟩,
        fun s' =>
        match s' with
        | none => s
        | some s' =>
          if h: s'.length = r.end then
            ⟨ List.setSlice! s.val 0 s'.val, by scalar_tac ⟩
          else s )
  else ok (none, fun _ => s)

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get_unchecked"]
def core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked
  {T : Type} (_ : core.ops.range.RangeTo Usize) (_ : ConstRawPtr (Slice T)) : Result (ConstRawPtr (Slice T)) :=
  -- TODO: update once we make the model of computation more stateful (for now we just fail)
  fail .undef

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get_unchecked_mut"]
def core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked_mut
  {T : Type} (_ : core.ops.range.RangeTo Usize) (_ : MutRawPtr (Slice T)) :
  Result (MutRawPtr (Slice T)) :=
  -- TODO: update once we make the model of computation more stateful (for now we just fail)
  fail .undef

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::index"]
def core.slice.index.SliceIndexRangeToUsizeSlice.index
  {T : Type} (r : core.ops.range.RangeTo Usize) (s : Slice T) : Result (Slice T) :=
  if r.end ≤ s.length then
    ok (⟨ s.val.slice 0 r.end, by scalar_tac⟩)
  else fail .panic

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::index_mut"]
def core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
  {T : Type} (r : core.ops.range.RangeTo Usize) (s : Slice T) :
  Result ((Slice T) × (Slice T → Slice T)) :=
  if r.end ≤ s.length then
    ok (⟨ s.val.slice 0 r.end, by scalar_tac⟩,
        /- The back function expects a slice of the same length as the returned subslice.
           We don't enforce this with a guard because we want totality; `setSlice!` handles
           any length gracefully. The model is correct when this condition holds, which is
           always the case for code generated by Aeneas. -/
        fun s' => ⟨ List.setSlice! s.val 0 s'.val, by scalar_tac ⟩)
  else fail .panic

@[reducible, rust_trait_impl "core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>"]
def core.slice.index.SliceIndexRangeToUsizeSlice (T : Type) :
  core.slice.index.SliceIndex (core.ops.range.RangeTo Usize) (Slice T) (Slice
  T) := {
  sealedInst := core.slice.index.private_slice_index.SealedRangeToUsize
  get := core.slice.index.SliceIndexRangeToUsizeSlice.get
  get_mut := core.slice.index.SliceIndexRangeToUsizeSlice.get_mut
  get_unchecked := core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked
  get_unchecked_mut := core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexRangeToUsizeSlice.index
  index_mut := core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
}

@[rust_trait_impl "core::ops::index::Index<[@T], @I, @O>"]
def core.ops.index.IndexSlice {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output) :
  core.ops.index.Index (Slice T) I Output := {
  index := core.slice.index.Slice.index inst
}

@[rust_trait_impl "core::ops::index::IndexMut<[@T], @I, @O>"]
def core.ops.index.IndexMutSlice {T I Output : Type}
  (inst : core.slice.index.SliceIndex I (Slice T) Output) :
  core.ops.index.IndexMut (Slice T) I Output := {
  indexInst := core.ops.index.IndexSlice inst
  index_mut := core.slice.index.Slice.index_mut inst
}

@[simp, step_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::get"]
abbrev core.slice.index.Usize.get
  {T : Type} (i : Usize) (s : Slice T) : Result (Option T) :=
  ok s[i]?

@[simp, step_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::get_mut"]
abbrev core.slice.index.Usize.get_mut
  {T : Type} (i : Usize) (s : Slice T) : Result (Option T × (Option T → Slice T)) :=
  ok (s[i]?, s.set_opt i)

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::get_unchecked"]
def core.slice.index.Usize.get_unchecked
  {T : Type} : Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr T) :=
  -- We don't have a model for now
  fun _ _ => fail .undef

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::get_unchecked_mut"]
def core.slice.index.Usize.get_unchecked_mut
  {T : Type} : Usize → MutRawPtr (Slice T) → Result (MutRawPtr T) :=
  -- We don't have a model for now
  fun _ _ => fail .undef

@[simp, step_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::index"]
abbrev core.slice.index.Usize.index {T : Type} (i : Usize) (s : Slice T) : Result T :=
  Slice.index_usize s i

@[simp, step_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::index_mut"]
abbrev core.slice.index.Usize.index_mut {T : Type}
  (i : Usize) (s : Slice T) : Result (T × (T → (Slice T))) :=
  Slice.index_mut_usize s i

@[rust_trait_impl "core::slice::index::private_slice_index::Sealed<usize>"]
def core.slice.index.private_slice_index.SealedUsize
  : core.slice.index.private_slice_index.Sealed Usize := {}

@[reducible, rust_trait_impl "core::slice::index::SliceIndex<usize, [@T], @T>"]
def core.slice.index.SliceIndexUsizeSlice (T : Type) :
  core.slice.index.SliceIndex Usize (Slice T) T := {
  sealedInst := core.slice.index.private_slice_index.SealedUsize
  get := core.slice.index.Usize.get
  get_mut := core.slice.index.Usize.get_mut
  get_unchecked := core.slice.index.Usize.get_unchecked
  get_unchecked_mut := core.slice.index.Usize.get_unchecked_mut
  index := core.slice.index.Usize.index
  index_mut := core.slice.index.Usize.index_mut
}

@[step]
theorem core.slice.Slice.get_unchecked_SliceIndexUsizeSlice_spec {T s i} [Inhabited T]
  (h : i.val < s.length) :
  core.slice.Slice.get_unchecked  (core.slice.index.SliceIndexUsizeSlice T) s i
  ⦃ x => x = s[i] ⦄ := by
  sorry

@[rust_fun "core::slice::{[@T]}::copy_from_slice"]
def core.slice.Slice.copy_from_slice {T : Type} (_ : core.marker.Copy T)
  (s : Slice T) (src: Slice T) : Result (Slice T) :=
  if s.len = src.len then ok src
  else fail panic

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::get"]
def core.slice.index.SliceIndexRangeFromUsizeSlice.get {T : Type} (r : core.ops.range.RangeFrom Usize) (s : Slice T) : Result (Option (Slice T)) :=
  if  r.start ≤ s.length then
    ok (some (s.drop r.start))
  else ok none

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::get_mut"]
def core.slice.index.SliceIndexRangeFromUsizeSlice.get_mut
  {T : Type} (r : core.ops.range.RangeFrom Usize) (s : Slice T) :
  Result ((Option (Slice T)) × (Option (Slice T) → Slice T)) :=
  if r.start ≤ s.length then
    ok (some (s.drop r.start),
        fun s' => match s' with
        | none => s
        | some s' =>
          if h: s'.length + s.length - r.start.val ≤ Usize.max then
            ⟨ s'.val ++ s.val.drop r.start.val, by scalar_tac ⟩
          else s)
  else ok (none, fun _ => s)

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::get_unchecked"]
def core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked {T : Type} :
  core.ops.range.RangeFrom Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr (Slice T)) :=
  -- We don't have a model for now
  fun _ _ => fail .undef

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::get_unchecked_mut"]
def core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked_mut {T : Type} :
  core.ops.range.RangeFrom Usize → MutRawPtr (Slice T) → Result (MutRawPtr (Slice T)) :=
  -- We don't have a model for now
  fun _ _ => fail .undef

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::index"]
def core.slice.index.SliceIndexRangeFromUsizeSlice.index {T : Type}
  (r : core.ops.range.RangeFrom Usize) (s : Slice T) : Result (Slice T) :=
  if r.start.val ≤ s.length then
    ok (s.drop r.start)
  else fail .undef

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>}::index_mut"]
def core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut {T : Type}
  (r : core.ops.range.RangeFrom Usize) (s : Slice T) : Result ((Slice T) × (Slice T → Slice T)) :=
  if r.start ≤ s.length then
    let s1 := s.drop r.start
    ok ( s1,
         /- The back function expects a slice of the same length as the returned subslice.
            We don't enforce this with a guard because we want totality; `setSlice!` handles
            any length gracefully. The model is correct when this condition holds, which is
            always the case for code generated by Aeneas. -/
         fun s2 => ⟨ s.val.setSlice! r.start s2, by scalar_tac ⟩)
  else fail .panic

theorem _SliceIndexRangeFromUsizeSlice.index_mut.test {T} (s : Slice T) (r : core.ops.range.RangeFrom Usize) (h : r.start ≤ s.length) :
  match core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut r s with
  | ok (s1, back) =>
    back s1 = s
  | _ => False := by
  unfold core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut
  simp [h]

@[reducible, rust_trait_impl "core::slice::index::private_slice_index::Sealed<core::ops::range::RangeFrom<usize>>"]
def core.slice.index.private_slice_index.SealedRangeFromUsize :
  core.slice.index.private_slice_index.Sealed (core.ops.range.RangeFrom Usize)
  := {}

@[reducible, rust_trait_impl "core::slice::index::SliceIndex<core::ops::range::RangeFrom<usize>, [@T], [@T]>"]
def core.slice.index.SliceIndexRangeFromUsizeSlice (T : Type) :
  core.slice.index.SliceIndex (core.ops.range.RangeFrom Usize) (Slice T) (Slice T) := {
  sealedInst :=
    core.slice.index.private_slice_index.SealedRangeFromUsize
  get := core.slice.index.SliceIndexRangeFromUsizeSlice.get
  get_mut := core.slice.index.SliceIndexRangeFromUsizeSlice.get_mut
  get_unchecked :=
    core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked
  get_unchecked_mut :=
    core.slice.index.SliceIndexRangeFromUsizeSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexRangeFromUsizeSlice.index
  index_mut :=
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut
}

/-- Small helper (this function doesn't model a specific Rust function) -/
def Slice.clone {T : Type} (clone : T → Result T) (s : Slice T) : Result (Slice T) := do
  let s' ← List.clone clone s.val
  ok ⟨ s', by scalar_tac ⟩

theorem Slice.clone_length {T : Type} {clone : T → Result T} {s s' : Slice T} (h : Slice.clone clone s = ok s') :
  s'.length = s.length := by
  simp [Slice.clone] at h
  simp [List.clone] at h
  split at h <;> simp_all
  rename_i heq
  have := List.mapM_Result_length heq
  cases s'; simp_all
  cases h; simp_all

@[step]
theorem Slice.clone_spec {T : Type} {clone : T → Result T} {s : Slice T} (h : ∀ x ∈ s.val, clone x = ok x) :
  Slice.clone clone s ⦃ s' => s = s' ⦄ := by
  simp only [Slice.clone]
  have ⟨ _, h ⟩ := spec_imp_exists (List.clone_spec h)
  simp [h]

@[rust_fun "core::slice::{[@T]}::split_at"]
def core.slice.Slice.split_at {T : Type} (s : Slice T) (n : Usize) :
  Result ((Slice T) × (Slice T)) :=
  if h0 : n ≤ s.length then
    let s0 := (s.val.splitAt n.val).fst
    let s1 := (s.val.splitAt n.val).snd
    let s0 : Slice T := ⟨ s0, by have := List.splitAt_length n.val s.val; have := s.property; simp +zetaDelta at *; omega  ⟩
    let s1 : Slice T := ⟨ s1, by have := List.splitAt_length n.val s.val; have := s.property; simp +zetaDelta at *; omega  ⟩
    ok (s0, s1)
  else fail .panic

@[rust_fun "core::slice::{[@T]}::split_at_mut"]
def core.slice.Slice.split_at_mut {T : Type} (s : Slice T) (n : Usize) :
  Result (((Slice T) × (Slice T)) × (((Slice T) × (Slice T)) → Slice T)) :=
  if h0 : n ≤ s.length then
    let s0 := (s.val.splitAt n.val).fst
    let s1 := (s.val.splitAt n.val).snd
    let back (s' : Slice T × Slice T) : Slice T :=
      let s0' := s'.fst
      let s1' := s'.snd
      if h1 : s0'.length = s0.length ∧ s1'.length = s1.length then
        -- TODO: scalar_tac is super slow below
        ⟨ s0'.val ++ s1'.val, by have := List.splitAt_length n.val s.val; have := s.property; simp +zetaDelta at *; omega ⟩
      else s
    let s0 : Slice T := ⟨ s0, by have := List.splitAt_length n.val s.val; have := s.property; simp +zetaDelta at *; omega  ⟩
    let s1 : Slice T := ⟨ s1, by have := List.splitAt_length n.val s.val; have := s.property; simp +zetaDelta at *; omega  ⟩
    ok ((s0, s1), back)
  else fail .panic

/-- **Spec theorem for `core::slice::{[@T]}::split_at`** -/
@[step]
theorem core.slice.Slice.split_at.spec {T : Type} (s : Slice T) (n : Usize)
    (h : n ≤ s.length) :
    core.slice.Slice.split_at s n
      ⦃ (s0 : Slice T) (s1 : Slice T) =>
        s0.length = n.val ∧ s1.length = s.length - n.val ∧
        s0.val = s.val.take n.val ∧ s1.val = s.val.drop n.val ⦄ := by
  unfold core.slice.Slice.split_at
  simp only [h, ↓reduceDIte, WP.spec_ok, predn_pair]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Slice.length, List.splitAt_eq] <;> scalar_tac

/-- **Spec theorem for `core::slice::{[@T]}::split_at_mut`** -/
-- TODO: ideally the postcondition binder would decompose the result pair as
-- `(s0 : Slice T) (s1 : Slice T) (back : ...)`, but the `⦃ ⦄` notation's
-- `predn` only handles right-associated products, so the left-associated
-- `((Slice T × Slice T) × BackFn)` return type cannot be split into three
-- separate binders. We keep projectors for now.
@[step]
theorem core.slice.Slice.split_at_mut.spec {T : Type} (s : Slice T) (n : Usize)
    (h : n ≤ s.length) :
    core.slice.Slice.split_at_mut s n
      ⦃ (res : Slice T × Slice T) (back : (Slice T × Slice T) → Slice T) =>
        res.1.length = n.val ∧ res.2.length = s.length - n.val ∧
        res.1.val = s.val.take n.val ∧ res.2.val = s.val.drop n.val ∧
        (∀ s0' s1', s0'.length = n.val → s1'.length = s.length - n.val →
          (back (s0', s1')).val = s0'.val ++ s1'.val ∧
          (back (s0', s1')).length = s.length) ⦄ := by
  unfold core.slice.Slice.split_at_mut
  simp only [h, ↓reduceDIte, WP.spec_ok, predn_pair]
  refine ⟨?_, ?_, ?_, ?_, fun s0' s1' hs0' hs1' => ?_⟩
  · simp [Slice.length, List.splitAt_eq]; scalar_tac
  · simp [Slice.length, List.splitAt_eq]
  · simp [List.splitAt_eq]
  · simp [List.splitAt_eq]
  · split_ifs with hcond
    · exact ⟨rfl, by simp [Slice.length, List.length_append]; scalar_tac⟩
    · exfalso; apply hcond
      simp [Slice.length, List.splitAt_eq] at *
      exact ⟨by scalar_tac, by scalar_tac⟩

@[rust_fun "core::slice::{[@T]}::swap"]
def core.slice.Slice.swap {T : Type} (s : Slice T) (a b : Usize) : Result (Slice T) := do
  let av ← Slice.index_usize s a
  let bv ← Slice.index_usize s b
  let s1 ← Slice.update s a bv
  Slice.update s1 b av

@[step]
theorem core.slice.Slice.swap_spec {T : Type} [Inhabited T] (s : Slice T) (a b : Usize)
    (ha : a.val < s.length) (hb : b.val < s.length) :
    core.slice.Slice.swap s a b ⦃ s' =>
      s'.length = s.length ∧
      s'.val[a.val]! = s.val[b.val]! ∧
      s'.val[b.val]! = s.val[a.val]! ∧
      ∀ i, i ≠ a.val → i ≠ b.val → s'.val[i]! = s.val[i]! ⦄ := by
  simp only [core.slice.Slice.swap, Bind.bind, bind]
  have ⟨av, hav⟩ := spec_imp_exists (Slice.index_usize_spec s a ha)
  simp only [hav, spec_ok]
  have ⟨bv, hbv⟩ := spec_imp_exists (Slice.index_usize_spec s b hb)
  simp only [hbv, spec_ok]
  have ⟨s1, hs1⟩ := spec_imp_exists (Slice.update_spec s a (s.val[b.val]!) ha)
  simp only [hs1, spec_ok]
  have hlen1 : b.val < s1.length := by rw [hs1.2, Slice.set_length]; exact hb
  have ⟨s', hs'⟩ := spec_imp_exists (Slice.update_spec s1 b (s.val[a.val]!) hlen1)
  rw [hs1.2] at hs'
  simp only [hs', spec_ok]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [hs'.2, Slice.set_length]
  · by_cases hab : (↑a : ℕ) = ↑b
    · simp only [Slice.getElem!_Nat_eq, Slice.set_val_eq, hab]; grind
    · simp only [Slice.getElem!_Nat_eq, Slice.set_val_eq]
      grind
  · simp only [Slice.getElem!_Nat_eq, Slice.set_val_eq]; grind
  · intro i hia hib
    simp only [Slice.getElem!_Nat_eq, Slice.set_val_eq]
    grind

@[simp, step_simps]
theorem Slice.index_mut_SliceIndexRangeUsizeSliceInst (s : Slice α) (r : core.ops.range.Range Usize) :
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice α) s r = core.slice.index.SliceIndexRangeUsizeSlice.index_mut r s := by
  rfl

@[simp, step_simps]
theorem Slice.index_SliceIndexRangeUsizeSliceInst (s : Slice α) (r : core.ops.range.Range Usize) :
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice α) s r = core.slice.index.SliceIndexRangeUsizeSlice.index r s := by
  rfl

def Slice.setSlice! {α : Type u} (s : Slice α) (i : ℕ) (s' : List α) : Slice α :=
  ⟨s.val.setSlice! i s', by scalar_tac⟩

@[simp_lists_safe]
theorem Slice.setSlice!_getElem!_prefix {α} [Inhabited α]
  (s : Slice α) (s' : List α) (i j : ℕ) (h : j < i) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [Slice.setSlice!, Slice.getElem!_Nat_eq]
  simp_lists

@[simp_lists_safe]
theorem Slice.setSlice!_getElem!_middle {α} [Inhabited α]
  (s : Slice α) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.length) :
  (s.setSlice! i s')[j]! = s'[j - i]! := by
  simp only [Slice.setSlice!, Slice.getElem!_Nat_eq]
  simp_lists

theorem Slice.setSlice!_getElem!_suffix {α} [Inhabited α]
  (s : Slice α) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [Slice.setSlice!, Slice.getElem!_Nat_eq]
  simp_lists

@[simp, simp_lists_safe]
theorem Slice.setSlice!_val (s : Slice α) (i : ℕ) (s' : List α) :
  (s.setSlice! i s').val = s.val.setSlice! i s' := by
  simp only [setSlice!]

@[step]
theorem core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec (r : core.ops.range.Range Usize) (s : Slice α)
  (h0 : r.start ≤ r.end) (h1 : r.end ≤ s.length) :
  core.slice.index.SliceIndexRangeUsizeSlice.index_mut r s ⦃ (s1, index_mut_back) =>
  s1.val = s.val.slice r.start r.end ∧
  s1.length = r.end - r.start ∧
  ∀ s2, index_mut_back s2 = s.setSlice! r.start.val s2 ⦄ := by
  simp only [index_mut, UScalar.le_equiv, Slice.length]
  split
  . simp only [spec_ok, true_and]
    simp_lists
    simp_scalar
    simp_lists [Slice.eq_iff]
  . scalar_tac

@[step]
theorem core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec {α : Type}
    (r : core.ops.range.Range Usize) (s : Slice α) (h0 : r.start ≤ r.end) (h1 : r.end ≤ s.length) :
    core.slice.index.SliceIndexRangeUsizeSlice.index r s ⦃ (s1 : Slice α) =>
      s1.val = s.val.slice r.start r.end ∧
      s1.length = r.end - r.start ⦄ := by
  simp only [core.slice.index.SliceIndexRangeUsizeSlice.index, UScalar.le_equiv, Slice.length]
  split
  · simp only [spec_ok, true_and]
    simp_lists
    omega
  · simp only [spec_fail]
    scalar_tac

-- RangeTo step specs

@[simp, step_simps]
theorem Slice.index_mut_SliceIndexRangeToUsizeSliceInst (s : Slice α) (r : core.ops.range.RangeTo Usize) :
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice α) s r =
  core.slice.index.SliceIndexRangeToUsizeSlice.index_mut r s := by rfl

@[simp, step_simps]
theorem Slice.index_SliceIndexRangeToUsizeSliceInst (s : Slice α) (r : core.ops.range.RangeTo Usize) :
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice α) s r =
  core.slice.index.SliceIndexRangeToUsizeSlice.index r s := by rfl

@[step]
theorem core.slice.index.SliceIndexRangeToUsizeSlice.index_mut.step_spec
    (r : core.ops.range.RangeTo Usize) (s : Slice α) (h : r.end ≤ s.length) :
  core.slice.index.SliceIndexRangeToUsizeSlice.index_mut r s
    ⦃ (s1, back) =>
      s1.val = s.val.slice 0 r.end ∧
      s1.length = r.«end» ∧
      ∀ s', (back s').val = s.val.setSlice! 0 s'.val ⦄ := by
  simp only [index_mut]
  split
  · simp only [spec_ok]
    refine ⟨trivial, ?_, ?_⟩
    · simp [Slice.length]; scalar_tac
    · intro s'; simp
  · scalar_tac

@[step]
theorem core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
    (r : core.ops.range.RangeTo Usize) (s : Slice α) (h : r.end ≤ s.length) :
  core.slice.index.SliceIndexRangeToUsizeSlice.index r s
    ⦃ s1 =>
      s1.val = s.val.slice 0 r.end ∧
      s1.length = r.end ⦄ := by
  simp only [index]
  split
  · simp only [spec_ok, Slice.length, true_and]
    simp; scalar_tac
  · scalar_tac

-- RangeFrom step specs

@[simp, step_simps]
theorem Slice.index_mut_SliceIndexRangeFromUsizeSliceInst (s : Slice α) (r : core.ops.range.RangeFrom Usize) :
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeFromUsizeSlice α) s r =
  core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut r s := by rfl

@[simp, step_simps]
theorem Slice.index_SliceIndexRangeFromUsizeSliceInst (s : Slice α) (r : core.ops.range.RangeFrom Usize) :
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeFromUsizeSlice α) s r =
  core.slice.index.SliceIndexRangeFromUsizeSlice.index r s := by rfl

@[step]
theorem core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut.step_spec
    (r : core.ops.range.RangeFrom Usize) (s : Slice α) (h : r.start ≤ s.length) :
  core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut r s
    ⦃ (s1, back) =>
      s1.val = s.val.drop r.start ∧
      s1.length = s.length - r.start.val ∧
      ∀ s', (back s').val = s.val.setSlice! r.start.val s'.val ⦄ := by
  simp only [index_mut, Slice.drop]
  split
  · simp only [spec_ok]
    refine ⟨trivial, ?_, ?_⟩
    · simp [Slice.length, List.length_drop]
    · intro s'; simp
  · scalar_tac

@[step]
theorem core.slice.index.SliceIndexRangeFromUsizeSlice.index.step_spec
    (r : core.ops.range.RangeFrom Usize) (s : Slice α) (h : r.start ≤ s.length) :
  core.slice.index.SliceIndexRangeFromUsizeSlice.index r s
    ⦃ s1 =>
      s1.val = s.val.drop r.start ∧
      s1.length = s.length - r.start.val ⦄ := by
  simp only [index]
  split
  · simp only [spec_ok, Slice.drop, true_and]
    simp [Slice.length, List.length_drop]
  · scalar_tac

@[step]
theorem core.slice.Slice.copy_from_slice.step_spec (copyInst : core.marker.Copy α) (s0 s1 : Slice α)
  (h : s0.length = s1.length) :
  core.slice.Slice.copy_from_slice copyInst s0 s1 ⦃ s1' => s1 = s1' ⦄ := by
  simp only [copy_from_slice]
  simp at h
  simp only [Slice.len]
  simp [h]

@[simp, scalar_tac_simps, simp_scalar_safe, simp_lists_safe]
theorem Slice.setSlice!_length {α : Type u} (s : Slice α) (i : ℕ) (s' : List α) :
  (s.setSlice! i s').length = s.length := by
  simp only [Slice.length, Slice.setSlice!, List.length_setSlice!]

def Slice.mapM  {α β} (f : α → Result β) (x : Slice α) : Result (Slice β) :=
  match h : x.val.mapM f with
  | ok xs  => ok ⟨xs, List.mapM_Result_length h ▸ x.prop⟩
  | fail e => fail e
  | div    => div

@[step]
theorem Slice.mapM_spec {α β} {f : α → Result β} {s : Slice α} {post : Nat → β → Prop}
    (hf : ∀ i (hi : i < s.len), f s[i] ⦃ post i ⦄) :
    s.mapM f ⦃ s' => s'.len = s.len ∧ ∀ i (hi : i < s'.len), post i s'[i] ⦄ := by
  simp only [mapM]
  have hmapM_ok : ∃ l', List.mapM f s.val = ok l' := by
    suffices ∀ (l : List α), (∀ i (hi : i < l.length), ∃ b, f l[i] = ok b) → ∃ l', l.mapM f = ok l' by
      apply this; intro i hi
      let i' : Usize := Usize.ofNatCore i (by scalar_tac)
      have hf' := hf i' (by scalar_tac)
      simp [spec, theta] at hf'
      show ∃ b, f s[i'] = ok b
      cases hfi : f s[i'] <;> simp_all
    intro l; induction l with
    | nil => exact fun _ => ⟨[], rfl⟩
    | cons a t ih =>
      intro hall
      obtain ⟨b, hb⟩ := hall 0 (by simp); simp at hb
      obtain ⟨ts, hts⟩ := ih (fun i hi => hall (i + 1) (by simp; omega))
      exact ⟨b :: ts, by simp [List.mapM_cons, hb, hts, pure, bind, Bind.bind]⟩
  obtain ⟨l', hl'⟩ := hmapM_ok
  split
  case h_1 xs heq =>
    simp only [UScalar.lt_equiv, Usize.ofNatCore_val_eq, spec_ok]
    refine ⟨by grind [List.mapM_Result_length], fun i hi => ?_⟩
    have hlen : i < s.len := by have := List.mapM_Result_length heq; simp [Slice.len] at *; omega
    have : f s[i] = ok xs[↑i] := List.mapM_Result_ok heq (↑i) (by scalar_tac)
    specialize hf i hlen; simp [spec, theta, this] at hf
    convert hf using 1
  case h_2 e heq => simp [hl'] at heq
  case h_3 heq => simp [hl'] at heq

end Aeneas.Std
