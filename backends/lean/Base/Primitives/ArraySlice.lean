/- Arrays/Slices -/
import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Linarith
import Base.IList
import Base.Primitives.Scalar
import Base.Primitives.Range
import Base.Primitives.CoreOps
import Base.Arith
import Base.Progress.Base

namespace Primitives

open Result Error core.ops.range

def Array (α : Type u) (n : Usize) := { l : List α // l.length = n.val }

instance (a : Type u) (n : Usize) : Arith.HasIntProp (Array a n) where
  prop_ty := λ v => v.val.len = n.val
  prop := λ ⟨ _, l ⟩ => by simp[Scalar.max, List.len_eq_length, *]

instance {α : Type u} {n : Usize} (p : Array α n → Prop) : Arith.HasIntProp (Subtype p) where
  prop_ty := λ x => p x
  prop := λ x => x.property

@[simp]
abbrev Array.length {α : Type u} {n : Usize} (v : Array α n) : Int := v.val.len

@[simp]
abbrev Array.v {α : Type u} {n : Usize} (v : Array α n) : List α := v.val

example {α: Type u} {n : Usize} (v : Array α n) : v.length ≤ Scalar.max ScalarTy.Usize := by
  scalar_tac

def Array.make (α : Type u) (n : Usize) (init : List α) (hl : init.len = n.val := by decide) :
  Array α n := ⟨ init, by simp [← List.len_eq_length]; apply hl ⟩

example : Array Int (Usize.ofInt 2) := Array.make Int (Usize.ofInt 2) [0, 1]

@[simp]
abbrev Array.index_s {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i : Int) : α :=
  v.val.index i

@[simp]
abbrev Array.slice {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i j : Int) : List α :=
  v.val.slice i j

def Array.index_usize (α : Type u) (n : Usize) (v: Array α n) (i: Usize) : Result α :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some x => ret x

-- For initialization
def Array.repeat (α : Type u) (n : Usize) (x : α) : Array α n :=
  ⟨ List.ireplicate n.val x, by have h := n.hmin; simp_all [Scalar.min] ⟩

@[pspec]
theorem Array.repeat_spec {α : Type u} (n : Usize) (x : α) :
  ∃ a, Array.repeat α n x = a ∧ a.val = List.ireplicate n.val x := by
  simp [Array.repeat]

/- In the theorems below: we don't always need the `∃ ..`, but we use one
   so that `progress` introduces an opaque variable and an equality. This
   helps control the context.
 -/

@[pspec]
theorem Array.index_usize_spec {α : Type u} {n : Usize} [Inhabited α] (v: Array α n) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_usize α n i = ret x ∧ x = v.val.index i.val := by
  simp only [index_usize]
  -- TODO: dependent rewrite
  have h := List.indexOpt_eq_index v.val i.val (by scalar_tac) (by simp [*])
  simp [*]

def Array.update_usize (α : Type u) (n : Usize) (v: Array α n) (i: Usize) (x: α) : Result (Array α n) :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some _ =>
    .ret ⟨ v.val.update i.val x, by have := v.property; simp [*] ⟩

@[pspec]
theorem Array.update_usize_spec {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.update_usize α n i x = ret nv ∧
  nv.val = v.val.update i.val x
  := by
  simp only [update_usize]
  have h := List.indexOpt_bounds v.val i.val
  split
  . simp_all [length]; cases h <;> scalar_tac
  . simp_all

def Array.index_mut_usize (α : Type u) (n : Usize) (v: Array α n) (i: Usize) :
  Result (α × (α -> Result (Array α n))) := do
  let x ← index_usize α n v i
  ret (x, update_usize α n v i)

@[pspec]
theorem Array.index_mut_usize_spec {α : Type u} {n : Usize} [Inhabited α] (v: Array α n) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x back, v.index_mut_usize α n i = ret (x, back) ∧
  x = v.val.index i.val ∧
  back = update_usize α n v i := by
  simp only [index_mut_usize, Bind.bind, bind]
  have ⟨ x, h ⟩ := index_usize_spec v i hbound
  simp [h]

def Slice (α : Type u) := { l : List α // l.length ≤ Usize.max }

instance (a : Type u) : Arith.HasIntProp (Slice a) where
  prop_ty := λ v => 0 ≤ v.val.len ∧ v.val.len ≤ Scalar.max ScalarTy.Usize
  prop := λ ⟨ _, l ⟩ => by simp[Scalar.max, List.len_eq_length, *]

instance {α : Type u} (p : Slice α → Prop) : Arith.HasIntProp (Subtype p) where
  prop_ty := λ x => p x
  prop := λ x => x.property

@[simp]
abbrev Slice.length {α : Type u} (v : Slice α) : Int := v.val.len

@[simp]
abbrev Slice.v {α : Type u} (v : Slice α) : List α := v.val

example {a: Type u} (v : Slice a) : v.length ≤ Scalar.max ScalarTy.Usize := by
  scalar_tac

def Slice.new (α : Type u): Slice α := ⟨ [], by apply Scalar.cMax_suffices .Usize; simp; decide ⟩

-- TODO: very annoying that the α is an explicit parameter
def Slice.len (α : Type u) (v : Slice α) : Usize :=
  Usize.ofIntCore v.val.len (by constructor <;> scalar_tac)

@[simp]
theorem Slice.len_val {α : Type u} (v : Slice α) : (Slice.len α v).val = v.length :=
  by rfl

@[simp]
abbrev Slice.index_s {α : Type u} [Inhabited α] (v: Slice α) (i: Int) : α :=
  v.val.index i

@[simp]
abbrev Slice.slice {α : Type u} [Inhabited α] (s : Slice α) (i j : Int) : List α :=
  s.val.slice i j

def Slice.index_usize (α : Type u) (v: Slice α) (i: Usize) : Result α :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some x => ret x

/- In the theorems below: we don't always need the `∃ ..`, but we use one
   so that `progress` introduces an opaque variable and an equality. This
   helps control the context.
 -/

@[pspec]
theorem Slice.index_usize_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_usize α i = ret x ∧ x = v.val.index i.val := by
  simp only [index_usize]
  -- TODO: dependent rewrite
  have h := List.indexOpt_eq_index v.val i.val (by scalar_tac) (by simp [*])
  simp [*]

def Slice.update_usize (α : Type u) (v: Slice α) (i: Usize) (x: α) : Result (Slice α) :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some _ =>
    .ret ⟨ v.val.update i.val x, by have := v.property; simp [*] ⟩

@[pspec]
theorem Slice.update_usize_spec {α : Type u} (v: Slice α) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.update_usize α i x = ret nv ∧
  nv.val = v.val.update i.val x
  := by
  simp only [update_usize]
  have h := List.indexOpt_bounds v.val i.val
  split
  . simp_all [length]; cases h <;> scalar_tac
  . simp_all

def Slice.index_mut_usize (α : Type u) (v: Slice α) (i: Usize) :
  Result (α × (α → Result (Slice α))) := do
  let x ← Slice.index_usize α v i
  ret (x, Slice.update_usize α v i)

@[pspec]
theorem Slice.index_mut_usize_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x back, v.index_mut_usize α i = ret (x, back) ∧
  x = v.val.index i.val ∧
  back = Slice.update_usize α v i := by
  simp only [index_mut_usize, Bind.bind, bind]
  have ⟨ x, h ⟩ := Slice.index_usize_spec v i hbound
  simp [h]

/- Array to slice/subslices -/

/- We could make this function not use the `Result` type. By making it monadic, we
   push the user to use the `Array.to_slice_spec` spec theorem below (through the
   `progress` tactic), meaning `Array.to_slice` should be considered as opaque.
   All what the spec theorem reveals is that the "representative" lists are the same. -/
def Array.to_slice (α : Type u) (n : Usize) (v : Array α n) : Result (Slice α) :=
  ret ⟨ v.val, by simp [← List.len_eq_length]; scalar_tac ⟩

@[pspec]
theorem Array.to_slice_spec {α : Type u} {n : Usize} (v : Array α n) :
  ∃ s, to_slice α n v = ret s ∧ v.val = s.val := by simp [to_slice]

def Array.from_slice (α : Type u) (n : Usize) (_ : Array α n) (s : Slice α) : Result (Array α n) :=
  if h: s.val.len = n.val then
    ret ⟨ s.val, by simp [← List.len_eq_length, *] ⟩
  else fail panic

@[pspec]
theorem Array.from_slice_spec {α : Type u} {n : Usize} (a : Array α n) (ns : Slice α) (h : ns.val.len = n.val) :
  ∃ na, from_slice α n a ns = ret na ∧ na.val = ns.val
  := by simp [from_slice, *]

def Array.to_slice_mut (α : Type u) (n : Usize) (a : Array α n) :
  Result (Slice α × (Slice α → Result (Array α n))) := do
  let s ← Array.to_slice α n a
  ret (s, Array.from_slice α n a)

@[pspec]
theorem Array.to_slice_mut_spec {α : Type u} {n : Usize} (v : Array α n) :
  ∃ s back, to_slice_mut α n v = ret (s, back) ∧
  v.val = s.val ∧
  back = Array.from_slice α n v
  := by simp [to_slice_mut, to_slice]

def Array.subslice (α : Type u) (n : Usize) (a : Array α n) (r : Range Usize) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end_.val ∧ r.end_.val ≤ a.val.len then
    ret ⟨ a.val.slice r.start.val r.end_.val,
          by
            simp [← List.len_eq_length]
            have := a.val.slice_len_le r.start.val r.end_.val
            scalar_tac ⟩
  else
    fail panic

@[pspec]
theorem Array.subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ a.val.len) :
  ∃ s, subslice α n a r = ret s ∧
  s.val = a.val.slice r.start.val r.end_.val ∧
  (∀ i, 0 ≤ i → i + r.start.val < r.end_.val → s.val.index i = a.val.index (r.start.val + i))
  := by
  simp [subslice, *]
  intro i _ _
  have := List.index_slice r.start.val r.end_.val i a.val (by scalar_tac) (by scalar_tac) (by trivial) (by scalar_tac)
  simp [*]

def Array.update_subslice (α : Type u) (n : Usize) (a : Array α n) (r : Range Usize) (s : Slice α) : Result (Array α n) :=
  -- TODO: not completely sure here
  if h: r.start.val < r.end_.val ∧ r.end_.val ≤ a.length ∧ s.val.len = r.end_.val - r.start.val then
    let s_beg := a.val.itake r.start.val
    let s_end := a.val.idrop r.end_.val
    have : s_beg.len = r.start.val := by
      apply List.itake_len
      . simp_all; scalar_tac
      . scalar_tac
    have : s_end.len = a.val.len - r.end_.val := by
      apply List.idrop_len
      . scalar_tac
      . scalar_tac
    let na := s_beg.append (s.val.append s_end)
    have : na.len = a.val.len := by simp [na, *]
    ret ⟨ na, by simp_all [← List.len_eq_length]; scalar_tac ⟩
  else
    fail panic

-- TODO: it is annoying to write `.val` everywhere. We could leverage coercions,
-- but: some symbols like `+` are already overloaded to be notations for monadic
-- operations/
-- We should introduce special symbols for the monadic arithmetic operations
-- (the user will never write those symbols directly).
@[pspec]
theorem Array.update_subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize) (s : Slice α)
  (_ : r.start.val < r.end_.val) (_ : r.end_.val ≤ a.length) (_ : s.length = r.end_.val - r.start.val) :
  ∃ na, update_subslice α n a r s = ret na ∧
  (∀ i, 0 ≤ i → i < r.start.val → na.index_s i = a.index_s i) ∧
  (∀ i, r.start.val ≤ i → i < r.end_.val → na.index_s i = s.index_s (i - r.start.val)) ∧
  (∀ i, r.end_.val ≤ i → i < n.val → na.index_s i = a.index_s i) := by
  simp [update_subslice, *]
  have h := List.replace_slice_index r.start.val r.end_.val a.val s.val
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
  simp [List.replace_slice] at h
  have ⟨ h0, h1, h2 ⟩ := h
  clear h
  split_conjs
  . intro i _ _
    have := h0 i (by int_tac) (by int_tac)
    simp [*]
  . intro i _ _
    have := h1 i (by int_tac) (by int_tac)
    simp [*]
  . intro i _ _
    have := h2 i (by int_tac) (by int_tac)
    simp [*]

def Slice.subslice (α : Type u) (s : Slice α) (r : Range Usize) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end_.val ∧ r.end_.val ≤ s.length then
    ret ⟨ s.val.slice r.start.val r.end_.val,
          by
            simp [← List.len_eq_length]
            have := s.val.slice_len_le r.start.val r.end_.val
            scalar_tac ⟩
  else
    fail panic

@[pspec]
theorem Slice.subslice_spec {α : Type u} [Inhabited α] (s : Slice α) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ s.val.len) :
  ∃ ns, subslice α s r = ret ns ∧
  ns.val = s.slice r.start.val r.end_.val ∧
  (∀ i, 0 ≤ i → i + r.start.val < r.end_.val → ns.index_s i = s.index_s (r.start.val + i))
  := by
  simp [subslice, *]
  intro i _ _
  have := List.index_slice r.start.val r.end_.val i s.val (by scalar_tac) (by scalar_tac) (by trivial) (by scalar_tac)
  simp [*]

attribute [pp_dot] List.len List.length List.index -- use the dot notation when printing
set_option pp.coercions false -- do not print coercions with ↑ (this doesn't parse)

def Slice.update_subslice (α : Type u) (s : Slice α) (r : Range Usize) (ss : Slice α) : Result (Slice α) :=
  -- TODO: not completely sure here
  if h: r.start.val < r.end_.val ∧ r.end_.val ≤ s.length ∧ ss.val.len = r.end_.val - r.start.val then
    let s_beg := s.val.itake r.start.val
    let s_end := s.val.idrop r.end_.val
    have : s_beg.len = r.start.val := by
      apply List.itake_len
      . simp_all; scalar_tac
      . scalar_tac
    have : s_end.len = s.val.len - r.end_.val := by
      apply List.idrop_len
      . scalar_tac
      . scalar_tac
    let ns := s_beg.append (ss.val.append s_end)
    have : ns.len = s.val.len := by simp [ns, *]
    ret ⟨ ns, by simp_all [← List.len_eq_length]; scalar_tac ⟩
  else
    fail panic

@[pspec]
theorem Slice.update_subslice_spec {α : Type u} [Inhabited α] (a : Slice α) (r : Range Usize) (ss : Slice α)
  (_ : r.start.val < r.end_.val) (_ : r.end_.val ≤ a.length) (_ : ss.length = r.end_.val - r.start.val) :
  ∃ na, update_subslice α a r ss = ret na ∧
  (∀ i, 0 ≤ i → i < r.start.val → na.index_s i = a.index_s i) ∧
  (∀ i, r.start.val ≤ i → i < r.end_.val → na.index_s i = ss.index_s (i - r.start.val)) ∧
  (∀ i, r.end_.val ≤ i → i < a.length → na.index_s i = a.index_s i) := by
  simp [update_subslice, *]
  have h := List.replace_slice_index r.start.val r.end_.val a.val ss.val
    (by scalar_tac) (by scalar_tac) (by scalar_tac) (by scalar_tac)
  simp [List.replace_slice, *] at h
  have ⟨ h0, h1, h2 ⟩ := h
  clear h
  split_conjs
  . intro i _ _
    have := h0 i (by int_tac) (by int_tac)
    simp [*]
  . intro i _ _
    have := h1 i (by int_tac) (by int_tac)
    simp [*]
  . intro i _ _
    have := h2 i (by int_tac) (by int_tac)
    simp [*]

/- Trait declaration: [core::slice::index::private_slice_index::Sealed] -/
structure core.slice.index.private_slice_index.Sealed (Self : Type) where

/- Trait declaration: [core::slice::index::SliceIndex] -/
structure core.slice.index.SliceIndex (Self T : Type) where
  sealedInst : core.slice.index.private_slice_index.Sealed Self
  Output : Type
  get : Self → T → Result (Option Output)
  get_mut : Self → T → Result (Option Output × (Option Output → Result T))
  get_unchecked : Self → ConstRawPtr T → Result (ConstRawPtr Output)
  get_unchecked_mut : Self → MutRawPtr T → Result (MutRawPtr Output)
  index : Self → T → Result Output
  index_mut : Self → T → Result (Output × (Output → Result T))

/- [core::slice::index::[T]::index]: forward function -/
def core.slice.index.Slice.index
  (T I : Type) (inst : core.slice.index.SliceIndex I (Slice T))
  (slice : Slice T) (i : I) : Result inst.Output := do
  let x ← inst.get i slice
  match x with
  | none => fail panic
  | some x => ret x

/- [core::slice::index::Range:::get]: forward function -/
def core.slice.index.RangeUsize.get (T : Type) (i : Range Usize) (slice : Slice T) :
  Result (Option (Slice T)) :=
  sorry -- TODO

/- [core::slice::index::Range::get_mut]: forward function -/
def core.slice.index.RangeUsize.get_mut
  (T : Type) : Range Usize → Slice T → Result (Option (Slice T) × (Option (Slice T) → Result (Slice T))) :=
  sorry -- TODO

/- [core::slice::index::Range::get_unchecked]: forward function -/
def core.slice.index.RangeUsize.get_unchecked
  (T : Type) :
  Range Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr (Slice T)) :=
  -- Don't know what the model should be - for now we always fail to make
  -- sure code which uses it fails
  fun _ _ => fail panic

/- [core::slice::index::Range::get_unchecked_mut]: forward function -/
def core.slice.index.RangeUsize.get_unchecked_mut
  (T : Type) :
  Range Usize → MutRawPtr (Slice T) → Result (MutRawPtr (Slice T)) :=
  -- Don't know what the model should be - for now we always fail to make
  -- sure code which uses it fails
  fun _ _ => fail panic

/- [core::slice::index::Range::index]: forward function -/
def core.slice.index.RangeUsize.index
  (T : Type) : Range Usize → Slice T → Result (Slice T) :=
  sorry -- TODO

/- [core::slice::index::Range::index_mut]: forward function -/
def core.slice.index.RangeUsize.index_mut
  (T : Type) : Range Usize → Slice T → Result (Slice T × (Slice T → Result (Slice T))) :=
  sorry -- TODO

/- [core::slice::index::[T]::index_mut]: forward function -/
def core.slice.index.Slice.index_mut
  (T I : Type) (inst : core.slice.index.SliceIndex I (Slice T)) :
  Slice T → I → Result (inst.Output × (inst.Output → Result (Slice T))) :=
  sorry -- TODO

/- [core::array::[T; N]::index]: forward function -/
def core.array.Array.index
  (T I : Type) (N : Usize) (inst : core.ops.index.Index (Slice T) I)
  (a : Array T N) (i : I) : Result inst.Output :=
  sorry -- TODO

/- [core::array::[T; N]::index_mut]: forward function -/
def core.array.Array.index_mut
  (T I : Type) (N : Usize) (inst : core.ops.index.IndexMut (Slice T) I)
  (a : Array T N) (i : I) :
  Result (inst.indexInst.Output × (inst.indexInst.Output → Result (Array T N))) :=
  sorry -- TODO

/- Trait implementation: [core::slice::index::private_slice_index::Range] -/
def core.slice.index.private_slice_index.SealedRangeUsizeInst
  : core.slice.index.private_slice_index.Sealed (Range Usize) := {}

/- Trait implementation: [core::slice::index::Range] -/
def core.slice.index.SliceIndexRangeUsizeSliceTInst (T : Type) :
  core.slice.index.SliceIndex (Range Usize) (Slice T) := {
  sealedInst := core.slice.index.private_slice_index.SealedRangeUsizeInst
  Output := Slice T
  get := core.slice.index.RangeUsize.get T
  get_mut := core.slice.index.RangeUsize.get_mut T
  get_unchecked := core.slice.index.RangeUsize.get_unchecked T
  get_unchecked_mut := core.slice.index.RangeUsize.get_unchecked_mut T
  index := core.slice.index.RangeUsize.index T
  index_mut := core.slice.index.RangeUsize.index_mut T
}

/- Trait implementation: [core::slice::index::[T]] -/
def core.ops.index.IndexSliceTIInst (T I : Type)
  (inst : core.slice.index.SliceIndex I (Slice T)) :
  core.ops.index.Index (Slice T) I := {
  Output := inst.Output
  index := core.slice.index.Slice.index T I inst
}

/- Trait implementation: [core::slice::index::[T]] -/
def core.ops.index.IndexMutSliceTIInst (T I : Type)
  (inst : core.slice.index.SliceIndex I (Slice T)) :
  core.ops.index.IndexMut (Slice T) I := {
  indexInst := core.ops.index.IndexSliceTIInst T I inst
  index_mut := core.slice.index.Slice.index_mut T I inst
}

/- Trait implementation: [core::array::[T; N]] -/
def core.ops.index.IndexArrayIInst (T I : Type) (N : Usize)
  (inst : core.ops.index.Index (Slice T) I) :
  core.ops.index.Index (Array T N) I := {
  Output := inst.Output
  index := core.array.Array.index T I N inst
}

/- Trait implementation: [core::array::[T; N]] -/
def core.ops.index.IndexMutArrayIInst (T I : Type) (N : Usize)
  (inst : core.ops.index.IndexMut (Slice T) I) :
  core.ops.index.IndexMut (Array T N) I := {
  indexInst := core.ops.index.IndexArrayIInst T I N inst.indexInst
  index_mut := core.array.Array.index_mut T I N inst
}

/- [core::slice::index::usize::get]: forward function -/
def core.slice.index.Usize.get
  (T : Type) : Usize → Slice T → Result (Option T) :=
  sorry -- TODO

/- [core::slice::index::usize::get_mut]: forward function -/
def core.slice.index.Usize.get_mut
  (T : Type) : Usize → Slice T → Result (Option T × (Option T → Result (Slice T))) :=
  sorry -- TODO

/- [core::slice::index::usize::get_unchecked]: forward function -/
def core.slice.index.Usize.get_unchecked
  (T : Type) : Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr T) :=
  sorry -- TODO

/- [core::slice::index::usize::get_unchecked_mut]: forward function -/
def core.slice.index.Usize.get_unchecked_mut
  (T : Type) : Usize → MutRawPtr (Slice T) → Result (MutRawPtr T) :=
  sorry -- TODO

/- [core::slice::index::usize::index]: forward function -/
def core.slice.index.Usize.index (T : Type) : Usize → Slice T → Result T :=
  sorry -- TODO

/- [core::slice::index::usize::index_mut]: forward function -/
def core.slice.index.Usize.index_mut (T : Type) :
  Usize → Slice T → Result (T × (T → Result (Slice T))) :=
  sorry -- TODO

/- Trait implementation: [core::slice::index::private_slice_index::usize] -/
def core.slice.index.private_slice_index.SealedUsizeInst
  : core.slice.index.private_slice_index.Sealed Usize := {}

/- Trait implementation: [core::slice::index::usize] -/
def core.slice.index.SliceIndexUsizeSliceTInst (T : Type) :
  core.slice.index.SliceIndex Usize (Slice T) := {
  sealedInst := core.slice.index.private_slice_index.SealedUsizeInst
  Output := T
  get := core.slice.index.Usize.get T
  get_mut := core.slice.index.Usize.get_mut T
  get_unchecked := core.slice.index.Usize.get_unchecked T
  get_unchecked_mut := core.slice.index.Usize.get_unchecked_mut T
  index := core.slice.index.Usize.index T
  index_mut := core.slice.index.Usize.index_mut T
}

end Primitives
