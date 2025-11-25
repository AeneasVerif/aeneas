/- Arrays/Slices -/
import Aeneas.List
import Aeneas.Std.Array.Core
import Aeneas.Std.Range
import Aeneas.Std.Core.Ops
import Aeneas.SimpScalar.SimpScalar

namespace Aeneas.Std

open Result Error core.ops.range

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

@[simp, scalar_tac_simps, simp_scalar_simps, simp_lists_simps]
abbrev Slice.length {α : Type u} (v : Slice α) : Nat := v.val.length

@[simp, scalar_tac_simps, simp_scalar_simps, simp_lists_simps]
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

def Slice.set {α : Type u} (v: Slice α) (i: Usize) (x: α) : Slice α :=
  ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

def Slice.set_opt {α : Type u} (v: Slice α) (i: Usize) (x: Option α) : Slice α :=
  ⟨ v.val.set_opt i.val x, by have := v.property; simp [*] ⟩

def Slice.drop {α} (s : Slice α) (i : Usize) : Slice α :=
  ⟨ s.val.drop i.val, by scalar_tac ⟩

@[simp, simp_lists_simps]
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
  simp only [Slice, Subtype.eq_iff]

/- In the theorems below: we don't always need the `∃ ..`, but we use one
   so that `progress` introduces an opaque variable and an equality. This
   helps control the context.
 -/

@[progress]
theorem Slice.index_usize_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val[i.val]! := by
  simp only [index_usize]
  simp only [length, getElem?_Usize_eq, exists_eq_right] at *
  simp only [List.getElem?_eq_getElem, List.getElem!_eq_getElem?_getD, Option.getD_some, hbound]

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Slice.set_val_eq {α : Type u} (v: Slice α) (i: Usize) (x: α) :
  (v.set i x) = v.val.set i.val x := by
  simp [set]

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Slice.set_opt_val_eq {α : Type u} (v: Slice α) (i: Usize) (x: Option α) :
  (v.set_opt i x) = v.val.set_opt i.val x := by
  simp [set_opt]

@[simp, scalar_tac_simps, simp_lists_simps]
theorem Slice.set_length {α : Type u} (v: Slice α) (i: Usize) (x: α) :
  (v.set i x).length = v.length := by simp

def Slice.update {α : Type u} (v: Slice α) (i: Usize) (x: α) : Result (Slice α) :=
  match v.val[i.val]? with
  | none => fail .arrayOutOfBounds
  | some _ =>
    ok ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

@[progress]
theorem Slice.update_spec {α : Type u} (v: Slice α) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.update i x = ok nv ∧
  nv = v.set i x
  := by
  simp only [update, set]
  simp at *
  simp [*]

def Slice.index_mut_usize {α : Type u} (v: Slice α) (i: Usize) :
  Result (α × (α → Slice α)) := do
  let x ← Slice.index_usize v i
  ok (x, Slice.set v i)

@[progress]
theorem Slice.index_mut_usize_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_mut_usize i = ok (x, Slice.set v i) ∧
  x = v.val[i.val]! := by
  simp only [index_mut_usize, Bind.bind, bind]
  have ⟨ x, h ⟩ := Slice.index_usize_spec v i hbound
  simp [h]

@[simp]
theorem Slice.update_index_eq α [Inhabited α] (x : Slice α) (i : Usize) :
  x.set i (x.val[i.val]!) = x := by
  simp only [Slice, Subtype.eq_iff, set_val_eq, List.set_getElem!]

def Slice.subslice {α : Type u} (s : Slice α) (r : Range Usize) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end_.val ∧ r.end_.val ≤ s.length then
    ok ⟨ s.val.slice r.start.val r.end_.val,
          by
            have := s.val.slice_length_le r.start.val r.end_.val
            scalar_tac ⟩
  else
    fail panic

@[progress]
theorem Slice.subslice_spec {α : Type u} [Inhabited α] (s : Slice α) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ s.val.length) :
  ∃ ns, subslice s r = ok ns ∧
  ns.val = s.slice r.start.val r.end_.val ∧
  (∀ i, i + r.start.val < r.end_.val → ns[i]! = s[r.start.val + i]!)
  := by
  simp_all only [subslice, length, and_self, ite_true, ok.injEq, slice, exists_eq_left', true_and]
  intro i _
  have := List.getElem!_slice r.start.val r.end_.val i s.val (by scalar_tac)
  simp only [List.getElem!_eq_getElem?_getD, getElem!_Nat_eq] at *
  apply this

def Slice.update_subslice {α : Type u} (s : Slice α) (r : Range Usize) (ss : Slice α) : Result (Slice α) :=
  -- TODO: not completely sure here
  if h: r.start.val < r.end_.val ∧ r.end_.val ≤ s.length ∧ ss.val.length = r.end_.val - r.start.val then
    ok ⟨ s.val.setSlice! r.start.val ss.val, by scalar_tac ⟩
  else
    fail panic

@[progress]
theorem Slice.update_subslice_spec {α : Type u} [Inhabited α] (a : Slice α) (r : Range Usize) (ss : Slice α)
  (_ : r.start.val < r.end_.val) (_ : r.end_.val ≤ a.length) (_ : ss.length = r.end_.val - r.start.val) :
  ∃ na, update_subslice a r ss = ok na ∧
  (∀ i, i < r.start.val → na[i]! = a[i]!) ∧
  (∀ i, r.start.val ≤ i → i < r.end_.val → na[i]! = ss[i - r.start.val]!) ∧
  (∀ i, r.end_.val ≤ i → i < a.length → na[i]! = a[i]!) := by
  simp only [update_subslice, length, and_self, ↓reduceDIte, ok.injEq, getElem!_Nat_eq,
    exists_eq_left', *]
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

@[rust_fun "core::slice::{[@T]}::get_mut"]
def core.slice.Slice.get_mut
  {T I Output : Type} (inst : core.slice.index.SliceIndex I (Slice T) Output)
  (s : Slice T) (i : I) : Result ((Option Output) × (Option Output → Slice T)) :=
  inst.get_mut i s

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::get"]
def core.slice.index.SliceIndexRangeUsizeSlice.get {T : Type} (r : Range Usize) (s : Slice T) :
  Result (Option (Slice T)) :=
  if r.start ≤ r.end_ ∧ r.end_ ≤ s.length then
    ok (some ⟨ s.val.slice r.start r.end_, by scalar_tac⟩)
  else ok none

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::get_mut"]
def core.slice.index.SliceIndexRangeUsizeSlice.get_mut
  {T : Type} (r : Range Usize) (s : Slice T) : Result (Option (Slice T) × (Option (Slice T) → Slice T)) :=
  if r.start ≤ r.end_ ∧ r.end_ ≤ s.length then
    ok (some ⟨ s.val.slice r.start r.end_, by scalar_tac⟩,
        fun s' =>
        match s' with
        | none => s
        | some s' =>
          if h: s'.length = r.end_ - r.start then
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
  if r.start ≤ r.end_ ∧ r.end_ ≤ s.length then
    ok (⟨ s.val.slice r.start r.end_, by scalar_tac⟩)
  else fail .panic

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::Range<usize>, [@T], [@T]>}::index_mut"]
def core.slice.index.SliceIndexRangeUsizeSlice.index_mut {T : Type} (r : Range Usize) (s : Slice T) :
  Result (Slice T × (Slice T → Slice T)) :=
  if r.start ≤ r.end_ ∧ r.end_ ≤ s.length then
    ok (⟨ s.val.slice r.start r.end_, by scalar_tac⟩,
        fun s' =>
        if h: s'.length = r.end_ - r.start then
          ⟨ List.setSlice! s.val r.start s', by scalar_tac ⟩
        else s )
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
  if r.end_ ≤ s.length then
    ok (some ⟨ s.val.slice r.end_ s.length, by scalar_tac⟩)
  else ok none

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get_mut"]
def core.slice.index.SliceIndexRangeToUsizeSlice.get_mut
  {T : Type} (r : core.ops.range.RangeTo Usize) (s : Slice T) :
  Result ((Option (Slice T)) × (Option (Slice T) → Slice T)) :=
  if r.end_ ≤ s.length then
    ok (some ⟨ s.val.slice r.end_ s.length, by scalar_tac⟩,
        fun s' =>
        match s' with
        | none => s
        | some s' =>
          if h: s'.length = s.length - r.end_ then
            ⟨ List.setSlice! s.val r.end_ s'.val, by scalar_tac ⟩
          else s )
  else ok (none, fun _ => s)

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get_unchecked"]
def core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked
  {T : Type} (_ : core.ops.range.RangeTo Usize) (_ : ConstRawPtr (Slice T)) : Result (ConstRawPtr (Slice T)) :=
  -- Don't know what the model should be - for now we always fail
  fail .undef

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::get_unchecked_mut"]
def core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked_mut
  {T : Type} (_ : core.ops.range.RangeTo Usize) (_ : MutRawPtr (Slice T)) :
  Result (MutRawPtr (Slice T)) :=
  -- Don't know what the model should be - for now we always fail
  fail .undef

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::index"]
def core.slice.index.SliceIndexRangeToUsizeSlice.index
  {T : Type} (r : core.ops.range.RangeTo Usize) (s : Slice T) : Result (Slice T) :=
  if r.end_ ≤ s.length then
    ok (⟨ s.val.slice r.end_ s.length, by scalar_tac⟩)
  else fail .panic

@[rust_fun "core::slice::index::{core::slice::index::SliceIndex<core::ops::range::RangeTo<usize>, [@T], [@T]>}::index_mut"]
def core.slice.index.SliceIndexRangeToUsizeSlice.index_mut
  {T : Type} (r : core.ops.range.RangeTo Usize) (s : Slice T) :
  Result ((Slice T) × (Slice T → Slice T)) :=
  if r.end_ ≤ s.length then
    ok (⟨ s.val.slice r.end_ s.length, by scalar_tac⟩,
        fun s' =>
        if h: s'.length = s.length - r.end_ then
          ⟨ List.setSlice! s.val r.end_ s', by scalar_tac ⟩
        else s )
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

@[simp, progress_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::get"]
abbrev core.slice.index.Usize.get
  {T : Type} (i : Usize) (s : Slice T) : Result (Option T) :=
  ok s[i]?

@[simp, progress_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::get_mut"]
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

@[simp, progress_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::index"]
abbrev core.slice.index.Usize.index {T : Type} (i : Usize) (s : Slice T) : Result T :=
  Slice.index_usize s i

@[simp, progress_simps, rust_fun "core::slice::index::{core::slice::index::SliceIndex<usize, [@T], @T>}::index_mut"]
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
         fun s2 =>
         if s2.length = s1.length then
            ⟨ s.val.setSlice! r.start s2, by scalar_tac ⟩
         else s )
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

@[progress]
theorem Slice.clone_spec {T : Type} {clone : T → Result T} {s : Slice T} (h : ∀ x ∈ s.val, clone x = ok x) :
  Slice.clone clone s = ok s := by
  simp only [Slice.clone]
  have ⟨ l', h ⟩ := List.clone_spec h
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

@[rust_fun "core::slice::{[@T]}::swap"]
def core.slice.Slice.swap {T : Type} (s : Slice T) (a b : Usize) : Result (Slice T) := do
  let av ← Slice.index_usize s a
  let bv ← Slice.index_usize s b
  let s1 ← Slice.update s a av
  Slice.update s1 b bv

@[simp, progress_simps]
theorem Slice.index_mut_SliceIndexRangeUsizeSliceInst (s : Slice α) (r : core.ops.range.Range Usize) :
  core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice α) s r = core.slice.index.SliceIndexRangeUsizeSlice.index_mut r s := by
  rfl

def Slice.setSlice! {α : Type u} (s : Slice α) (i : ℕ) (s' : List α) : Slice α :=
  ⟨s.val.setSlice! i s', by scalar_tac⟩

@[simp_lists_simps]
theorem Slice.setSlice!_getElem!_prefix {α} [Inhabited α]
  (s : Slice α) (s' : List α) (i j : ℕ) (h : j < i) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [Slice.setSlice!, Slice.getElem!_Nat_eq]
  simp_lists

@[simp_lists_simps]
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

@[simp, simp_lists_simps]
theorem Slice.setSlice!_val (s : Slice α) (i : ℕ) (s' : List α) :
  (s.setSlice! i s').val = s.val.setSlice! i s' := by
  simp only [setSlice!]

@[progress]
theorem core.slice.index.SliceIndexRangeUsizeSlice.index_mut.progress_spec (r : core.ops.range.Range Usize) (s : Slice α)
  (h0 : r.start ≤ r.end_) (h1 : r.end_ ≤ s.length) :
  ∃ s1 index_mut_back, core.slice.index.SliceIndexRangeUsizeSlice.index_mut r s = ok (s1, index_mut_back) ∧
  s1.val = s.val.slice r.start r.end_ ∧
  s1.length = r.end_ - r.start ∧
  ∀ s2, s2.length = s1.length → index_mut_back s2 = s.setSlice! r.start.val s2 := by
  simp only [index_mut, UScalar.le_equiv, Slice.length, dite_eq_ite]
  split
  . simp only [ok.injEq, Prod.mk.injEq, and_assoc, exists_and_left, exists_eq_left', true_and]
    simp_lists
    simp_scalar
    simp_lists [Slice.eq_iff]
  . simp only [reduceCtorEq, false_and, exists_false]
    scalar_tac

@[progress]
theorem core.slice.Slice.copy_from_slice.progress_spec (copyInst : core.marker.Copy α) (s0 s1 : Slice α)
  (h : s0.length = s1.length) :
  core.slice.Slice.copy_from_slice copyInst s0 s1 = ok s1 := by
  simp only [copy_from_slice, ite_eq_left_iff, UScalar.neq_to_neq_val, Usize.ofNat_val_eq, h,
    Slice.length, not_true_eq_false, reduceCtorEq, imp_self]

@[simp, scalar_tac_simps, simp_scalar_simps, simp_lists_simps]
theorem Slice.setSlice!_length {α : Type u} (s : Slice α) (i : ℕ) (s' : List α) :
  (s.setSlice! i s').length = s.length := by
  simp only [Slice.length, Slice.setSlice!, List.length_setSlice!]

@[rust_type "core::slice::iter::Iter"]
structure core.slice.iter.Iter (T : Type) where
  /- We need to remember the slice and an index inside the slice (this is necessary)
     for double ended iterators) -/
  slice : Slice T
  i : Nat

@[rust_type "core::slice::iter::IterMut"]
structure core.slice.iter.IterMut (T : Type) where
  /- We need to remember the slice and an index inside the slice (this is necessary)
     for double ended iterators) -/
  slice : Slice T
  i : Nat

@[rust_fun "core::slice::{[@T]}::iter"]
def core.slice.Slice.iter {T : Type} (s : Slice T) : Result (core.slice.iter.Iter T) :=
  ok ⟨ s, 0 ⟩

@[rust_fun "core::slice::{[@T]}::contains"]
def core.slice.Slice.contains {T : Type} (partialEqInst : core.cmp.PartialEq T T)
  (s : Slice T) (x : T) : Result Bool :=
  List.anyM (partialEqInst.eq x) s.val

end Aeneas.Std
