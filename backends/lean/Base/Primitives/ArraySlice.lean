/- Arrays/Slices -/
import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd
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
abbrev Array.index {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i : Int) : α :=
  v.val.index i

@[simp]
abbrev Array.slice {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i j : Int) : List α :=
  v.val.slice i j

def Array.index_shared (α : Type u) (n : Usize) (v: Array α n) (i: Usize) : Result α :=
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
theorem Array.index_shared_spec {α : Type u} {n : Usize} [Inhabited α] (v: Array α n) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_shared α n i = ret x ∧ x = v.val.index i.val := by
  simp only [index_shared]
  -- TODO: dependent rewrite
  have h := List.indexOpt_eq_index v.val i.val (by scalar_tac) (by simp [*])
  simp [*]

-- This shouldn't be used
def Array.index_shared_back (α : Type u) (n : Usize) (v: Array α n) (i: Usize) (_: α) : Result Unit :=
  if i.val < List.length v.val then
    .ret ()
  else
    .fail arrayOutOfBounds

def Array.index_mut (α : Type u) (n : Usize) (v: Array α n) (i: Usize) : Result α :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some x => ret x

@[pspec]
theorem Array.index_mut_spec {α : Type u} {n : Usize} [Inhabited α] (v: Array α n) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_mut α n i = ret x ∧ x = v.val.index i.val := by
  simp only [index_mut]
  -- TODO: dependent rewrite
  have h := List.indexOpt_eq_index v.val i.val (by scalar_tac) (by simp [*])
  simp [*]

def Array.index_mut_back (α : Type u) (n : Usize) (v: Array α n) (i: Usize) (x: α) : Result (Array α n) :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some _ =>
    .ret ⟨ v.val.update i.val x, by have := v.property; simp [*] ⟩

@[pspec]
theorem Array.index_mut_back_spec {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.index_mut_back α n i x = ret nv ∧
  nv.val = v.val.update i.val x
  := by
  simp only [index_mut_back]
  have h := List.indexOpt_bounds v.val i.val
  split
  . simp_all [length]; cases h <;> scalar_tac
  . simp_all

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

def Slice.new (α : Type u): Slice α := ⟨ [], by apply Scalar.cMax_suffices .Usize; simp ⟩

-- TODO: very annoying that the α is an explicit parameter
def Slice.len (α : Type u) (v : Slice α) : Usize :=
  Usize.ofIntCore v.val.len (by scalar_tac) (by scalar_tac)

@[simp]
theorem Slice.len_val {α : Type u} (v : Slice α) : (Slice.len α v).val = v.length :=
  by rfl

@[simp]
abbrev Slice.index {α : Type u} [Inhabited α] (v: Slice α) (i: Int) : α :=
  v.val.index i

@[simp]
abbrev Slice.slice {α : Type u} [Inhabited α] (s : Slice α) (i j : Int) : List α :=
  s.val.slice i j

def Slice.index_shared (α : Type u) (v: Slice α) (i: Usize) : Result α :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some x => ret x

/- In the theorems below: we don't always need the `∃ ..`, but we use one
   so that `progress` introduces an opaque variable and an equality. This
   helps control the context.
 -/

@[pspec]
theorem Slice.index_shared_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_shared α i = ret x ∧ x = v.val.index i.val := by
  simp only [index_shared]
  -- TODO: dependent rewrite
  have h := List.indexOpt_eq_index v.val i.val (by scalar_tac) (by simp [*])
  simp [*]

-- This shouldn't be used
def Slice.index_shared_back (α : Type u) (v: Slice α) (i: Usize) (_: α) : Result Unit :=
  if i.val < List.length v.val then
    .ret ()
  else
    .fail arrayOutOfBounds

def Slice.index_mut (α : Type u) (v: Slice α) (i: Usize) : Result α :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some x => ret x

@[pspec]
theorem Slice.index_mut_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_mut α i = ret x ∧ x = v.val.index i.val := by
  simp only [index_mut]
  -- TODO: dependent rewrite
  have h := List.indexOpt_eq_index v.val i.val (by scalar_tac) (by simp [*])
  simp [*]

def Slice.index_mut_back (α : Type u) (v: Slice α) (i: Usize) (x: α) : Result (Slice α) :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some _ =>
    .ret ⟨ v.val.update i.val x, by have := v.property; simp [*] ⟩

@[pspec]
theorem Slice.index_mut_back_spec {α : Type u} (v: Slice α) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.index_mut_back α i x = ret nv ∧
  nv.val = v.val.update i.val x
  := by
  simp only [index_mut_back]
  have h := List.indexOpt_bounds v.val i.val
  split
  . simp_all [length]; cases h <;> scalar_tac
  . simp_all

/- Array to slice/subslices -/

/- We could make this function not use the `Result` type. By making it monadic, we
   push the user to use the `Array.to_slice_shared_spec` spec theorem below (through the
   `progress` tactic), meaning `Array.to_slice_shared` should be considered as opaque.
   All what the spec theorem reveals is that the "representative" lists are the same. -/
def Array.to_slice_shared (α : Type u) (n : Usize) (v : Array α n) : Result (Slice α) :=
  ret ⟨ v.val, by simp [← List.len_eq_length]; scalar_tac ⟩

@[pspec]
theorem Array.to_slice_shared_spec {α : Type u} {n : Usize} (v : Array α n) :
  ∃ s, to_slice_shared α n v = ret s ∧ v.val = s.val := by simp [to_slice_shared]

def Array.to_slice_mut (α : Type u) (n : Usize) (v : Array α n) : Result (Slice α) :=
  to_slice_shared α n v

@[pspec]
theorem Array.to_slice_mut_spec {α : Type u} {n : Usize} (v : Array α n) :
  ∃ s, Array.to_slice_shared α n v = ret s ∧ v.val = s.val := to_slice_shared_spec v

def Array.to_slice_mut_back (α : Type u) (n : Usize) (_ : Array α n) (s : Slice α) : Result (Array α n) :=
  if h: s.val.len = n.val then
    ret ⟨ s.val, by simp [← List.len_eq_length, *] ⟩
  else fail panic

@[pspec]
theorem Array.to_slice_mut_back_spec {α : Type u} {n : Usize} (a : Array α n) (ns : Slice α) (h : ns.val.len = n.val) :
  ∃ na, to_slice_mut_back α n a ns = ret na ∧ na.val = ns.val
  := by simp [to_slice_mut_back, *]

def Array.subslice_shared (α : Type u) (n : Usize) (a : Array α n) (r : Range Usize) : Result (Slice α) :=
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
theorem Array.subslice_shared_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ a.val.len) :
  ∃ s, subslice_shared α n a r = ret s ∧
  s.val = a.val.slice r.start.val r.end_.val ∧
  (∀ i, 0 ≤ i → i + r.start.val < r.end_.val → s.val.index i = a.val.index (r.start.val + i))
  := by
  simp [subslice_shared, *]
  intro i _ _
  have := List.index_slice r.start.val r.end_.val i a.val (by scalar_tac) (by scalar_tac) (by trivial) (by scalar_tac)
  simp [*]

def Array.subslice_mut (α : Type u) (n : Usize) (a : Array α n) (r : Range Usize) : Result (Slice α) :=
  Array.subslice_shared α n a r

@[pspec]
theorem Array.subslice_mut_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ a.val.len) :
  ∃ s, subslice_mut α n a r = ret s ∧
  s.val = a.slice r.start.val r.end_.val ∧
  (∀ i, 0 ≤ i → i + r.start.val < r.end_.val → s.val.index i = a.val.index (r.start.val + i))
  := subslice_shared_spec a r h0 h1

def Array.subslice_mut_back (α : Type u) (n : Usize) (a : Array α n) (r : Range Usize) (s : Slice α) : Result (Array α n) :=
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
    have : na.len = a.val.len := by simp [*]
    ret ⟨ na, by simp_all [← List.len_eq_length]; scalar_tac ⟩
  else
    fail panic

-- TODO: it is annoying to write `.val` everywhere. We could leverage coercions,
-- but: some symbols like `+` are already overloaded to be notations for monadic
-- operations/
-- We should introduce special symbols for the monadic arithmetic operations
-- (the use will never write those symbols directly).
@[pspec]
theorem Array.subslice_mut_back_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize) (s : Slice α)
  (_ : r.start.val < r.end_.val) (_ : r.end_.val ≤ a.length) (_ : s.length = r.end_.val - r.start.val) :
  ∃ na, subslice_mut_back α n a r s = ret na ∧
  (∀ i, 0 ≤ i → i < r.start.val → na.index i = a.index i) ∧
  (∀ i, r.start.val ≤ i → i < r.end_.val → na.index i = s.index (i - r.start.val)) ∧
  (∀ i, r.end_.val ≤ i → i < n.val → na.index i = a.index i) := by
  simp [subslice_mut_back, *]
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

def Slice.subslice_shared (α : Type u) (s : Slice α) (r : Range Usize) : Result (Slice α) :=
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
theorem Slice.subslice_shared_spec {α : Type u} [Inhabited α] (s : Slice α) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ s.val.len) :
  ∃ ns, subslice_shared α s r = ret ns ∧
  ns.val = s.slice r.start.val r.end_.val ∧
  (∀ i, 0 ≤ i → i + r.start.val < r.end_.val → ns.index i = s.index (r.start.val + i))
  := by
  simp [subslice_shared, *]
  intro i _ _
  have := List.index_slice r.start.val r.end_.val i s.val (by scalar_tac) (by scalar_tac) (by trivial) (by scalar_tac)
  simp [*]

def Slice.subslice_mut (α : Type u) (s : Slice α) (r : Range Usize) : Result (Slice α) :=
  Slice.subslice_shared α s r

@[pspec]
theorem Slice.subslice_mut_spec {α : Type u} [Inhabited α] (s : Slice α) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ s.val.len) :
  ∃ ns, subslice_mut α s r = ret ns ∧
  ns.val = s.slice r.start.val r.end_.val ∧
  (∀ i, 0 ≤ i → i + r.start.val < r.end_.val → ns.index i = s.index (r.start.val + i))
  := subslice_shared_spec s r h0 h1

attribute [pp_dot] List.len List.length List.index -- use the dot notation when printing
set_option pp.coercions false -- do not print coercions with ↑ (this doesn't parse)

def Slice.subslice_mut_back (α : Type u) (s : Slice α) (r : Range Usize) (ss : Slice α) : Result (Slice α) :=
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
    have : ns.len = s.val.len := by simp [*]
    ret ⟨ ns, by simp_all [← List.len_eq_length]; scalar_tac ⟩
  else
    fail panic

@[pspec]
theorem Slice.subslice_mut_back_spec {α : Type u} [Inhabited α] (a : Slice α) (r : Range Usize) (ss : Slice α)
  (_ : r.start.val < r.end_.val) (_ : r.end_.val ≤ a.length) (_ : ss.length = r.end_.val - r.start.val) :
  ∃ na, subslice_mut_back α a r ss = ret na ∧
  (∀ i, 0 ≤ i → i < r.start.val → na.index i = a.index i) ∧
  (∀ i, r.start.val ≤ i → i < r.end_.val → na.index i = ss.index (i - r.start.val)) ∧
  (∀ i, r.end_.val ≤ i → i < a.length → na.index i = a.index i) := by
  simp [subslice_mut_back, *]
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
structure core.slice.index.SliceIndex (Self T0 : Type) where
  sealedInst : core.slice.index.private_slice_index.Sealed Self
  Output : Type
  get : Self → T0 → Result (Option Output)
  get_mut : Self → T0 → Result (Option Output)
  get_mut_back : Self → T0 → Option Output → Result T0
  get_unchecked : Self → ConstRawPtr T0 → Result (ConstRawPtr Output)
  get_unchecked_mut : Self → MutRawPtr T0 → Result (MutRawPtr Output)
  index : Self → T0 → Result Output
  index_mut : Self → T0 → Result Output
  index_mut_back : Self → T0 → Output → Result T0

/- [core::slice::index::[T]::index]: forward function -/
def core.slice.index.Slice.index
  (T0 I : Type) (inst : core.slice.index.SliceIndex I (Slice T0))
  (slice : Slice T0) (i : I) : Result inst.Output := do
  let x ← inst.get i slice
  match x with
  | none => fail panic
  | some x => ret x

/- [core::slice::index::Range:::get]: forward function -/
def core.slice.index.Range.get (T0 : Type) (i : Range Usize) (slice : Slice T0) :
  Result (Option (Slice T0)) :=
  sorry -- TODO

/- [core::slice::index::Range::get_mut]: forward function -/
def core.slice.index.Range.get_mut
  (T0 : Type) : Range Usize → Slice T0 → Result (Option (Slice T0)) :=
  sorry -- TODO

/- [core::slice::index::Range::get_mut]: backward function 0 -/
def core.slice.index.Range.get_mut_back
  (T0 : Type) :
  Range Usize → Slice T0 → Option (Slice T0) → Result (Slice T0) :=
  sorry -- TODO

/- [core::slice::index::Range::get_unchecked]: forward function -/
def core.slice.index.Range.get_unchecked
  (T0 : Type) :
  Range Usize → ConstRawPtr (Slice T0) → Result (ConstRawPtr (Slice T0)) :=
  -- Don't know what the model should be - for now we always fail to make
  -- sure code which uses it fails
  fun _ _ => fail panic

/- [core::slice::index::Range::get_unchecked_mut]: forward function -/
def core.slice.index.Range.get_unchecked_mut
  (T0 : Type) :
  Range Usize → MutRawPtr (Slice T0) → Result (MutRawPtr (Slice T0)) :=
  -- Don't know what the model should be - for now we always fail to make
  -- sure code which uses it fails
  fun _ _ => fail panic

/- [core::slice::index::Range::index]: forward function -/
def core.slice.index.Range.index
  (T0 : Type) : Range Usize → Slice T0 → Result (Slice T0) :=
  sorry -- TODO

/- [core::slice::index::Range::index_mut]: forward function -/
def core.slice.index.Range.index_mut
  (T0 : Type) : Range Usize → Slice T0 → Result (Slice T0) :=
  sorry -- TODO

/- [core::slice::index::Range::index_mut]: backward function 0 -/
def core.slice.index.Range.index_mut_back
  (T0 : Type) : Range Usize → Slice T0 → Slice T0 → Result (Slice T0) :=
  sorry -- TODO

/- [core::slice::index::[T]::index_mut]: forward function -/
def core.slice.index.Slice.index_mut
  (T0 I : Type) (inst : core.slice.index.SliceIndex I (Slice T0)) :
  Slice T0 → I → Result inst.Output :=
  sorry -- TODO

/- [core::slice::index::[T]::index_mut]: backward function 0 -/
def core.slice.index.Slice.index_mut_back
  (T0 I : Type) (inst : core.slice.index.SliceIndex I (Slice T0)) :
  Slice T0 → I → inst.Output → Result (Slice T0) :=
  sorry -- TODO

/- [core::array::[T; N]::index]: forward function -/
def core.array.Array.index
  (T0 I : Type) (N : Usize) (inst : core.ops.index.Index (Slice T0) I) :
  Array T0 N → I → Result inst.Output :=
  sorry -- TODO

/- [core::array::[T; N]::index_mut]: forward function -/
def core.array.Array.index_mut
  (T0 I : Type) (N : Usize) (inst : core.ops.index.IndexMut (Slice T0) I) :
  Array T0 N → I → Result inst.indexInst.Output :=
  sorry -- TODO

/- [core::array::[T; N]::index_mut]: backward function 0 -/
def core.array.Array.index_mut_back
  (T0 I : Type) (N : Usize) (inst : core.ops.index.IndexMut (Slice T0) I) :
  Array T0 N → I → inst.indexInst.Output → Result (Array T0 N) :=
  sorry -- TODO

/- Trait implementation: [core::slice::index::[T]] -/
def core.slice.index.Slice.coreopsindexIndexInst (T0 I : Type)
  (inst : core.slice.index.SliceIndex I (Slice T0)) :
  core.ops.index.Index (Slice T0) I := {
  Output := inst.Output
  index := core.slice.index.Slice.index T0 I inst
}

/- Trait implementation: [core::slice::index::private_slice_index::Range] -/
def core.slice.index.private_slice_index.Range.coresliceindexprivate_slice_indexSealedInst
  : core.slice.index.private_slice_index.Sealed (Range Usize) := {}

/- Trait implementation: [core::slice::index::Range] -/
def core.slice.index.Range.coresliceindexSliceIndexInst (T0 : Type) :
  core.slice.index.SliceIndex (Range Usize) (Slice T0) := {
  sealedInst :=
    core.slice.index.private_slice_index.Range.coresliceindexprivate_slice_indexSealedInst
  Output := Slice T0
  get := core.slice.index.Range.get T0
  get_mut := core.slice.index.Range.get_mut T0
  get_mut_back := core.slice.index.Range.get_mut_back T0
  get_unchecked := core.slice.index.Range.get_unchecked T0
  get_unchecked_mut := core.slice.index.Range.get_unchecked_mut T0
  index := core.slice.index.Range.index T0
  index_mut := core.slice.index.Range.index_mut T0
  index_mut_back := core.slice.index.Range.index_mut_back T0
}

/- Trait implementation: [core::slice::index::[T]] -/
def core.slice.index.Slice.coreopsindexIndexMutInst (T0 I : Type)
  (inst : core.slice.index.SliceIndex I (Slice T0)) :
  core.ops.index.IndexMut (Slice T0) I := {
  indexInst := core.slice.index.Slice.coreopsindexIndexInst T0 I inst
  index_mut := core.slice.index.Slice.index_mut T0 I inst
  index_mut_back := core.slice.index.Slice.index_mut_back T0 I inst
}

/- Trait implementation: [core::array::[T; N]] -/
def core.array.Array.coreopsindexIndexInst (T0 I : Type) (N : Usize)
  (inst : core.ops.index.Index (Slice T0) I) :
  core.ops.index.Index (Array T0 N) I := {
  Output := inst.Output
  index := core.array.Array.index T0 I N inst
}

/- Trait implementation: [core::array::[T; N]] -/
def core.array.Array.coreopsindexIndexMutInst (T0 I : Type) (N : Usize)
  (inst : core.ops.index.IndexMut (Slice T0) I) :
  core.ops.index.IndexMut (Array T0 N) I := {
  indexInst := core.array.Array.coreopsindexIndexInst T0 I N inst.indexInst
  index_mut := core.array.Array.index_mut T0 I N inst
  index_mut_back := core.array.Array.index_mut_back T0 I N inst
}

/- [core::slice::index::usize::get]: forward function -/
def core.slice.index.Usize.get
  (T : Type) : Usize → Slice T → Result (Option T) :=
  sorry -- TODO

/- [core::slice::index::usize::get_mut]: forward function -/
def core.slice.index.Usize.get_mut
  (T : Type) : Usize → Slice T → Result (Option T) :=
  sorry -- TODO

/- [core::slice::index::usize::get_mut]: backward function 0 -/
def core.slice.index.Usize.get_mut_back
  (T : Type) : Usize → Slice T → Option T → Result (Slice T) :=
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
def core.slice.index.Usize.index_mut (T : Type) : Usize → Slice T → Result T :=
  sorry -- TODO

/- [core::slice::index::usize::index_mut]: backward function 0 -/
def core.slice.index.Usize.index_mut_back
  (T : Type) : Usize → Slice T → T → Result (Slice T) :=
  sorry -- TODO

/- Trait implementation: [core::slice::index::private_slice_index::usize] -/
def core.slice.index.private_slice_index.usize.coresliceindexprivate_slice_indexSealedInst
  : core.slice.index.private_slice_index.Sealed Usize := {}

/- Trait implementation: [core::slice::index::usize] -/
def core.slice.index.usize.coresliceindexSliceIndexInst (T : Type) :
  core.slice.index.SliceIndex Usize (Slice T) := {
  sealedInst := core.slice.index.private_slice_index.usize.coresliceindexprivate_slice_indexSealedInst
  Output := T
  get := core.slice.index.Usize.get T
  get_mut := core.slice.index.Usize.get_mut T
  get_mut_back := core.slice.index.Usize.get_mut_back T
  get_unchecked := core.slice.index.Usize.get_unchecked T
  get_unchecked_mut := core.slice.index.Usize.get_unchecked_mut T
  index := core.slice.index.Usize.index T
  index_mut := core.slice.index.Usize.index_mut T
  index_mut_back := core.slice.index.Usize.index_mut_back T
}

end Primitives
