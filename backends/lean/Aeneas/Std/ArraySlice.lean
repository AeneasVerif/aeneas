/- Arrays/Slices -/
import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Linarith
import Aeneas.List
import Aeneas.Std.Scalar
import Aeneas.Std.Range
import Aeneas.Std.Core
import Aeneas.Arith
import Aeneas.Progress.Base

namespace Aeneas

namespace Std

open Result Error core.ops.range

def Array (α : Type u) (n : Usize) := { l : List α // l.length = n.val }

/-- We need this to coerce arrays to lists without marking `Array` as reducible.
    Also not that we *do not* want to mark `Array` as reducible: it triggers issues.
-/
instance (α : Type u) (n : Usize) : CoeOut (Array α n) (List α) where
  coe := λ v => v.val

instance [BEq α] : BEq (Array α n) := SubtypeBEq _

instance [BEq α] [LawfulBEq α] : LawfulBEq (Array α n) := SubtypeLawfulBEq _

/- Registering some theorems for `scalar_tac` -/
@[scalar_tac a]
theorem Array.length_eq {α : Type u} {n : Usize} (a : Array α n) : a.val.length = n.val := by
  cases a; simp[*]

-- TODO: move/remove?
@[scalar_tac a]
theorem Array.subtype_property {α : Type u} {n : Usize} {p : Array α n → Prop} (a : Subtype p) : p a.val := a.property

@[simp]
abbrev Array.length {α : Type u} {n : Usize} (v : Array α n) : Nat := v.val.length

@[simp]
abbrev Array.v {α : Type u} {n : Usize} (v : Array α n) : List α := v.val

example {α: Type u} {n : Usize} (v : Array α n) : v.length ≤ Scalar.max ScalarTy.Usize := by
  scalar_tac

def Array.make {α : Type u} (n : Usize) (init : List α) (hl : init.length = n.val := by rfl) :
  Array α n := ⟨ init, by apply hl ⟩

example : Array Int (Usize.ofInt 2) := Array.make (Usize.ofInt 2) [0, 1]

example : Array Int (Usize.ofInt 2) :=
  let x := 0
  let y := 1
  Array.make (Usize.ofInt 2) [x, y]

example : Result (Array Int (Usize.ofInt 2)) := do
  let x ← ok 0
  let y ← ok 1
  ok (Array.make (Usize.ofInt 2) [x, y])

@[simp]
abbrev Array.index_s {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i : Nat) : α :=
  v.val.index i

@[simp]
abbrev Array.slice {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i j : Nat) : List α :=
  v.val.slice i j

def Array.index_usize {α : Type u} {n : Usize} (v: Array α n) (i: Usize) : Result α :=
  match v.val.indexOpt i.toNat with
  | none => fail .arrayOutOfBounds
  | some x => ok x

-- For initialization
def Array.repeat {α : Type u} (n : Usize) (x : α) : Array α n :=
  ⟨ List.replicate n.toNat x, by have h := n.hmin; simp_all [Scalar.min] ⟩

@[pspec]
theorem Array.repeat_spec {α : Type u} (n : Usize) (x : α) :
  ∃ a, Array.repeat n x = a ∧ a.val = List.replicate n.toNat x := by
  simp [Array.repeat]

/- In the theorems below: we don't always need the `∃ ..`, but we use one
   so that `progress` introduces an opaque variable and an equality. This
   helps control the context.
 -/

@[pspec]
theorem Array.index_usize_spec {α : Type u} {n : Usize} [Inhabited α] (v: Array α n) (i: Usize)
  (hbound : i.toNat < v.length) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val.index i.toNat := by
  simp only [index_usize]
  -- TODO: dependent rewrite
  have h := List.indexOpt_eq_index v.val i.toNat (by scalar_tac)
  simp [*]

def Array.update_usize {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) : Result (Array α n) :=
  match v.val.indexOpt i.toNat with
  | none => fail .arrayOutOfBounds
  | some _ =>
    ok ⟨ v.val.update i.toNat x, by have := v.property; simp [*] ⟩

def Array.update {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) : Array α n :=
  ⟨ v.val.update i.toNat x, by have := v.property; simp [*] ⟩

@[simp]
theorem Array.update_val_eq {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) :
  (v.update i x).val = v.val.update i.toNat x := by
  simp [update]

@[scalar_tac v.update i x]
theorem Array.update_length {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) :
  (v.update i x).length = v.length := by simp

@[pspec]
theorem Array.update_usize_spec {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x : α)
  (hbound : i.toNat < v.length) :
  ∃ nv, v.update_usize i x = ok nv ∧
  nv.val = v.val.update i.toNat x
  := by
  simp only [update_usize]
  have h := List.indexOpt_bounds v.val i.toNat
  split
  . simp_all [length]
    scalar_tac
  . simp_all

def Array.index_mut_usize {α : Type u} {n : Usize} (v: Array α n) (i: Usize) :
  Result (α × (α -> Array α n)) := do
  let x ← index_usize v i
  ok (x, update v i)

@[pspec]
theorem Array.index_mut_usize_spec {α : Type u} {n : Usize} [Inhabited α] (v: Array α n) (i: Usize)
  (hbound : i.toNat < v.length) :
  ∃ x, v.index_mut_usize i = ok (x, update v i) ∧
  x = v.val.index i.toNat := by
  simp only [index_mut_usize, Bind.bind, bind]
  have ⟨ x, h ⟩ := index_usize_spec v i hbound
  simp [h]

def Slice (α : Type u) := { l : List α // l.length ≤ Usize.max }

/-- We need this to coerce slices to lists without marking `Slice` as reducible.
    Also not that we *do not* want to mark `Slice` as reducible: it triggers issues.
-/
instance (α : Type u) : CoeOut (Slice α) (List α) where
  coe := λ v => v.val

instance [BEq α] : BEq (Slice α) := SubtypeBEq _

instance [BEq α] [LawfulBEq α] : LawfulBEq (Slice α) := SubtypeLawfulBEq _

@[scalar_tac s]
theorem Slice.length_ineq {α : Type u} (s : Slice α) : s.val.length ≤ Scalar.max ScalarTy.Usize := by
  cases s; simp[Scalar.max, *]

-- TODO: move/remove?
@[scalar_tac s]
theorem Slice.subtype_property {α : Type u} {p : Slice α → Prop} (s : Subtype p) : p s.val := s.property

@[simp]
abbrev Slice.length {α : Type u} (v : Slice α) : Nat := v.val.length

@[simp]
abbrev Slice.v {α : Type u} (v : Slice α) : List α := v.val

example {a: Type u} (v : Slice a) : v.length ≤ Scalar.max ScalarTy.Usize := by
  scalar_tac

def Slice.new (α : Type u) : Slice α := ⟨ [], by apply Scalar.cMax_suffices .Usize; simp ⟩

-- TODO: very annoying that the α is an explicit parameter
abbrev Slice.len {α : Type u} (v : Slice α) : Usize :=
  Usize.ofIntCore v.val.length (by constructor <;> scalar_tac)

@[simp]
theorem Slice.len_val {α : Type u} (v : Slice α) : (Slice.len v).val = v.length :=
  by rfl

@[simp]
abbrev Slice.index_s {α : Type u} [Inhabited α] (v: Slice α) (i: Nat) : α :=
  v.val.index i

@[simp]
abbrev Slice.slice {α : Type u} [Inhabited α] (s : Slice α) (i j : Nat) : List α :=
  s.val.slice i j

def Slice.index_usize {α : Type u} (v: Slice α) (i: Usize) : Result α :=
  match v.val.indexOpt i.toNat with
  | none => fail .arrayOutOfBounds
  | some x => ok x

/- In the theorems below: we don't always need the `∃ ..`, but we use one
   so that `progress` introduces an opaque variable and an equality. This
   helps control the context.
 -/

@[pspec]
theorem Slice.index_usize_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.toNat < v.length) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val.index i.toNat := by
  simp only [index_usize]
  -- TODO: dependent rewrite
  have h := List.indexOpt_eq_index v.val i.toNat (by scalar_tac)
  simp [*]

def Slice.update_usize {α : Type u} (v: Slice α) (i: Usize) (x: α) : Result (Slice α) :=
  match v.val.indexOpt i.toNat with
  | none => fail .arrayOutOfBounds
  | some _ =>
    ok ⟨ v.val.update i.toNat x, by have := v.property; simp [*] ⟩

def Slice.update {α : Type u} (v: Slice α) (i: Usize) (x: α) : Slice α :=
  ⟨ v.val.update i.toNat x, by have := v.property; simp [*] ⟩

@[simp]
theorem Slice.update_val_eq {α : Type u} (v: Slice α) (i: Usize) (x: α) :
  (v.update i x) = v.val.update i.toNat x := by
  simp [update]

@[scalar_tac v.update i x]
theorem Slice.update_length {α : Type u} (v: Slice α) (i: Usize) (x: α) :
  (v.update i x).length = v.length := by simp

@[pspec]
theorem Slice.update_usize_spec {α : Type u} (v: Slice α) (i: Usize) (x : α)
  (hbound : i.toNat < v.length) :
  ∃ nv, v.update_usize i x = ok nv ∧
  nv.val = v.val.update i.toNat x
  := by
  simp only [update_usize]
  have h := List.indexOpt_bounds v.val i.toNat
  split
  . simp_all [length]; scalar_tac
  . simp_all

def Slice.index_mut_usize {α : Type u} (v: Slice α) (i: Usize) :
  Result (α × (α → Slice α)) := do
  let x ← Slice.index_usize v i
  ok (x, Slice.update v i)

@[pspec]
theorem Slice.index_mut_usize_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.toNat < v.length) :
  ∃ x, v.index_mut_usize i = ok (x, Slice.update v i) ∧
  x = v.val.index i.toNat := by
  simp only [index_mut_usize, Bind.bind, bind]
  have ⟨ x, h ⟩ := Slice.index_usize_spec v i hbound
  simp [h]

/- Array to slice/subslices -/

/- We could make this function not use the `Result` type. By making it monadic, we
   push the user to use the `Array.to_slice_spec` spec theorem below (through the
   `progress` tactic), meaning `Array.to_slice` should be considered as opaque.
   All what the spec theorem reveals is that the "representative" lists are the same. -/
def Array.to_slice {α : Type u} {n : Usize} (v : Array α n) : Result (Slice α) :=
  ok ⟨ v.val, by scalar_tac ⟩

@[pspec]
theorem Array.to_slice_spec {α : Type u} {n : Usize} (v : Array α n) :
  ∃ s, to_slice v = ok s ∧ v.val = s.val := by simp [to_slice]

def Array.from_slice {α : Type u} {n : Usize} (a : Array α n) (s : Slice α) : Array α n :=
  if h: s.val.length = n.val then
    ⟨ s.val, by simp [*] ⟩
  else a -- Unreachable case

@[simp]
theorem Array.from_slice_val {α : Type u} {n : Usize} (a : Array α n) (ns : Slice α) (h : ns.val.length = n.val) :
  (from_slice a ns).val = ns.val
  := by simp [from_slice, *]

def Array.to_slice_mut {α : Type u} {n : Usize} (a : Array α n) :
  Result (Slice α × (Slice α → Array α n)) := do
  let s ← Array.to_slice a
  ok (s, Array.from_slice a)

@[pspec]
theorem Array.to_slice_mut_spec {α : Type u} {n : Usize} (v : Array α n) :
  ∃ s, to_slice_mut v = ok (s, Array.from_slice v) ∧
  v.val = s.val
  := by simp [to_slice_mut, to_slice]

def Array.subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end_.val ∧ r.end_.val ≤ a.val.length then
    ok ⟨ a.val.slice r.start.toNat r.end_.toNat,
          by
            have := a.val.slice_length_le r.start.toNat r.end_.toNat
            scalar_tac ⟩
  else
    fail panic

@[pspec]
theorem Array.subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ a.val.length) :
  ∃ s, subslice a r = ok s ∧
  s.val = a.val.slice r.start.toNat r.end_.toNat ∧
  (∀ i, 0 ≤ i → i + r.start.val < r.end_.val → s.val.index i.toNat = a.val.index (r.start.toNat + i.toNat))
  := by
  simp [subslice, *]
  intro i _ _
  have := List.index_slice r.start.toNat r.end_.toNat i.toNat a.val (by scalar_tac) (by scalar_tac)
  simp [*]

set_option maxHeartbeats 500000

def Array.update_subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) (s : Slice α) : Result (Array α n) :=
  -- TODO: not completely sure here
  if h: r.start.toNat < r.end_.toNat ∧ r.end_.toNat ≤ a.length ∧ s.val.length = r.end_.toNat - r.start.toNat then
    let s_beg := a.val.take r.start.toNat
    let s_end := a.val.drop r.end_.toNat
    have : s_beg.length = r.start.toNat := by
      scalar_tac
    have : s_end.length = a.val.length - r.end_.toNat := by
      scalar_tac
    let na := s_beg.append (s.val.append s_end)
    have : na.length = a.val.length:= by
      simp [na]; scalar_tac
    ok ⟨ na, by simp_all; scalar_tac ⟩
  else
    fail panic

-- TODO: it is annoying to write `.val` everywhere. We could leverage coercions,
-- but: some symbols like `+` are already overloaded to be notations for monadic
-- operations/
-- We should introduce special symbols for the monadic arithmetic operations
-- (the user will never write those symbols directly).
@[pspec]
theorem Array.update_subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize) (s : Slice α)
  (_ : r.start.toNat < r.end_.toNat) (_ : r.end_.toNat ≤ a.length) (_ : s.length = r.end_.toNat - r.start.toNat) :
  ∃ na, update_subslice a r s = ok na ∧
  (∀ i, 0 ≤ i → i < r.start.toNat → na.index_s i = a.index_s i) ∧
  (∀ i, r.start.toNat ≤ i → i < r.end_.toNat → na.index_s i = s.index_s (i - r.start.toNat)) ∧
  (∀ i, r.end_.toNat ≤ i → i < n.toNat → na.index_s i = a.index_s i) := by
  simp [update_subslice, *]
  have h := List.replace_slice_index r.start.toNat r.end_.toNat a.val s.val
    (by scalar_tac) (by scalar_tac) (by scalar_tac)
  simp [List.replace_slice] at h
  have ⟨ h0, h1, h2 ⟩ := h
  clear h
  split_conjs
  . intro i _
    have := h0 i (by int_tac)
    simp_all
  . intro i _ _
    have := h1 i (by int_tac) (by int_tac)
    simp [*]
  . intro i _ _
    have := h2 i (by int_tac) (by int_tac)
    simp [*]

def Slice.subslice {α : Type u} (s : Slice α) (r : Range Usize) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end_.val ∧ r.end_.val ≤ s.length then
    ok ⟨ s.val.slice r.start.toNat r.end_.toNat,
          by
            have := s.val.slice_length_le r.start.toNat r.end_.toNat
            scalar_tac ⟩
  else
    fail panic

@[pspec]
theorem Slice.subslice_spec {α : Type u} [Inhabited α] (s : Slice α) (r : Range Usize)
  (h0 : r.start.toNat < r.end_.toNat) (h1 : r.end_.toNat ≤ s.val.length) :
  ∃ ns, subslice s r = ok ns ∧
  ns.val = s.slice r.start.toNat r.end_.toNat ∧
  (∀ i, i + r.start.toNat < r.end_.toNat → ns.index_s i = s.index_s (r.start.toNat + i))
  := by
  simp_all [subslice]
  intro i _
  have := List.index_slice r.start.toNat r.end_.toNat i s.val (by scalar_tac) (by scalar_tac)
  simp [*]

def Slice.update_subslice {α : Type u} (s : Slice α) (r : Range Usize) (ss : Slice α) : Result (Slice α) :=
  -- TODO: not completely sure here
  if h: r.start.toNat < r.end_.toNat ∧ r.end_.toNat ≤ s.length ∧ ss.val.length = r.end_.toNat - r.start.toNat then
    let s_beg := s.val.take r.start.toNat
    let s_end := s.val.drop r.end_.toNat
    have : s_beg.length = r.start.toNat := by scalar_tac
    have : s_end.length = s.val.length - r.end_.val := by scalar_tac
    let ns := s_beg.append (ss.val.append s_end)
    have : ns.length = s.val.length := by simp [ns, *]; scalar_tac
    ok ⟨ ns, by simp_all; scalar_tac ⟩
  else
    fail panic

@[pspec]
theorem Slice.update_subslice_spec {α : Type u} [Inhabited α] (a : Slice α) (r : Range Usize) (ss : Slice α)
  (_ : r.start.toNat < r.end_.toNat) (_ : r.end_.toNat ≤ a.length) (_ : ss.length = r.end_.toNat - r.start.toNat) :
  ∃ na, update_subslice a r ss = ok na ∧
  (∀ i, i < r.start.toNat → na.index_s i = a.index_s i) ∧
  (∀ i, r.start.toNat ≤ i → i < r.end_.toNat → na.index_s i = ss.index_s (i - r.start.toNat)) ∧
  (∀ i, r.end_.toNat ≤ i → i < a.length → na.index_s i = a.index_s i) := by
  simp [update_subslice, *]
  have h := List.replace_slice_index r.start.toNat r.end_.toNat a.val ss.val
    (by scalar_tac) (by scalar_tac) (by scalar_tac)
  simp [List.replace_slice, *] at h
  have ⟨ h0, h1, h2 ⟩ := h
  clear h
  split_conjs
  . intro i _
    have := h0 i (by int_tac)
    simp [*]
  . intro i _ _
    have := h1 i (by int_tac) (by int_tac)
    simp [*]
  . intro i _ _
    have := h2 i (by int_tac) (by int_tac)
    simp [*]

@[simp]
theorem Array.update_index_eq α n [Inhabited α] (x : Array α n) (i : Usize) :
  x.update i (x.val.index i.toNat) = x := by
  simp [Array, Subtype.eq_iff]

@[simp]
theorem Slice.update_index_eq α [Inhabited α] (x : Slice α) (i : Usize) :
  x.update i (x.val.index i.toNat) = x := by
  simp [Slice, Subtype.eq_iff]

/- Trait declaration: [core::slice::index::private_slice_index::Sealed] -/
structure core.slice.index.private_slice_index.Sealed (Self : Type) where

/- Trait declaration: [core::slice::index::SliceIndex] -/
structure core.slice.index.SliceIndex (Self T : Type) where
  sealedInst : core.slice.index.private_slice_index.Sealed Self
  Output : Type
  get : Self → T → Result (Option Output)
  get_mut : Self → T → Result (Option Output × (Option Output → T))
  get_unchecked : Self → ConstRawPtr T → Result (ConstRawPtr Output)
  get_unchecked_mut : Self → MutRawPtr T → Result (MutRawPtr Output)
  index : Self → T → Result Output
  index_mut : Self → T → Result (Output × (Output → T))

/- [core::slice::index::[T]::index]: forward function -/
def core.slice.index.Slice.index
  {T I : Type} (inst : core.slice.index.SliceIndex I (Slice T))
  (slice : Slice T) (i : I) : Result inst.Output := do
  let x ← inst.get i slice
  match x with
  | none => fail panic
  | some x => ok x

/- [core::slice::index::Range:::get]: forward function -/
def core.slice.index.RangeUsize.get {T : Type} (i : Range Usize) (slice : Slice T) :
  Result (Option (Slice T)) :=
  sorry -- TODO

/- [core::slice::index::Range::get_mut]: forward function -/
def core.slice.index.RangeUsize.get_mut
  {T : Type} : Range Usize → Slice T → Result (Option (Slice T) × (Option (Slice T) → Slice T)) :=
  sorry -- TODO

/- [core::slice::index::Range::get_unchecked]: forward function -/
def core.slice.index.RangeUsize.get_unchecked
  {T : Type} :
  Range Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr (Slice T)) :=
  -- Don't know what the model should be - for now we always fail to make
  -- sure code which uses it fails
  fun _ _ => fail panic

/- [core::slice::index::Range::get_unchecked_mut]: forward function -/
def core.slice.index.RangeUsize.get_unchecked_mut
  {T : Type} :
  Range Usize → MutRawPtr (Slice T) → Result (MutRawPtr (Slice T)) :=
  -- Don't know what the model should be - for now we always fail to make
  -- sure code which uses it fails
  fun _ _ => fail panic

/- [core::slice::index::Range::index]: forward function -/
def core.slice.index.RangeUsize.index
  {T : Type} : Range Usize → Slice T → Result (Slice T) :=
  sorry -- TODO

/- [core::slice::index::Range::index_mut]: forward function -/
def core.slice.index.RangeUsize.index_mut
  {T : Type} : Range Usize → Slice T → Result (Slice T × (Slice T → Slice T)) :=
  sorry -- TODO

/- [core::slice::index::[T]::index_mut]: forward function -/
def core.slice.index.Slice.index_mut
  {T I : Type} (inst : core.slice.index.SliceIndex I (Slice T)) :
  Slice T → I → Result (inst.Output × (inst.Output → Slice T)) :=
  sorry -- TODO

/- [core::array::[T; N]::index]: forward function -/
def core.array.Array.index
  {T I : Type} {N : Usize} (inst : core.ops.index.Index (Slice T) I)
  (a : Array T N) (i : I) : Result inst.Output :=
  sorry -- TODO

/- [core::array::[T; N]::index_mut]: forward function -/
def core.array.Array.index_mut
  {T I : Type} {N : Usize} (inst : core.ops.index.IndexMut (Slice T) I)
  (a : Array T N) (i : I) :
  Result (inst.indexInst.Output × (inst.indexInst.Output → Array T N)) :=
  sorry -- TODO

/- Trait implementation: [core::slice::index::private_slice_index::Range] -/
def core.slice.index.private_slice_index.SealedRangeUsizeInst
  : core.slice.index.private_slice_index.Sealed (Range Usize) := {}

/- Trait implementation: [core::slice::index::Range] -/
@[reducible]
def core.slice.index.SliceIndexRangeUsizeSliceTInst (T : Type) :
  core.slice.index.SliceIndex (Range Usize) (Slice T) := {
  sealedInst := core.slice.index.private_slice_index.SealedRangeUsizeInst
  Output := Slice T
  get := core.slice.index.RangeUsize.get
  get_mut := core.slice.index.RangeUsize.get_mut
  get_unchecked := core.slice.index.RangeUsize.get_unchecked
  get_unchecked_mut := core.slice.index.RangeUsize.get_unchecked_mut
  index := core.slice.index.RangeUsize.index
  index_mut := core.slice.index.RangeUsize.index_mut
}

/- Trait implementation: [core::slice::index::[T]] -/
def core.ops.index.IndexSliceTIInst {T I : Type}
  (inst : core.slice.index.SliceIndex I (Slice T)) :
  core.ops.index.Index (Slice T) I := {
  Output := inst.Output
  index := core.slice.index.Slice.index inst
}

/- Trait implementation: [core::slice::index::[T]] -/
def core.ops.index.IndexMutSliceTIInst {T I : Type}
  (inst : core.slice.index.SliceIndex I (Slice T)) :
  core.ops.index.IndexMut (Slice T) I := {
  indexInst := core.ops.index.IndexSliceTIInst inst
  index_mut := core.slice.index.Slice.index_mut inst
}

/- Trait implementation: [core::array::[T; N]] -/
def core.ops.index.IndexArrayIInst {T I : Type} {N : Usize}
  (inst : core.ops.index.Index (Slice T) I) :
  core.ops.index.Index (Array T N) I := {
  Output := inst.Output
  index := core.array.Array.index inst
}

/- Trait implementation: [core::array::[T; N]] -/
def core.ops.index.IndexMutArrayIInst {T I : Type} {N : Usize}
  (inst : core.ops.index.IndexMut (Slice T) I) :
  core.ops.index.IndexMut (Array T N) I := {
  indexInst := core.ops.index.IndexArrayIInst inst.indexInst
  index_mut := core.array.Array.index_mut inst
}

/- [core::slice::index::usize::get]: forward function -/
def core.slice.index.Usize.get
  {T : Type} : Usize → Slice T → Result (Option T) :=
  sorry -- TODO

/- [core::slice::index::usize::get_mut]: forward function -/
def core.slice.index.Usize.get_mut
  {T : Type} : Usize → Slice T → Result (Option T × (Option T → Slice T)) :=
  sorry -- TODO

/- [core::slice::index::usize::get_unchecked]: forward function -/
def core.slice.index.Usize.get_unchecked
  {T : Type} : Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr T) :=
  sorry -- TODO

/- [core::slice::index::usize::get_unchecked_mut]: forward function -/
def core.slice.index.Usize.get_unchecked_mut
  {T : Type} : Usize → MutRawPtr (Slice T) → Result (MutRawPtr T) :=
  sorry -- TODO

/- [core::slice::index::usize::index]: forward function -/
def core.slice.index.Usize.index {T : Type} : Usize → Slice T → Result T :=
  sorry -- TODO

/- [core::slice::index::usize::index_mut]: forward function -/
def core.slice.index.Usize.index_mut {T : Type} :
  Usize → Slice T → Result (T × (T → (Slice T))) :=
  sorry -- TODO

/- Trait implementation: [core::slice::index::private_slice_index::usize] -/
def core.slice.index.private_slice_index.SealedUsizeInst
  : core.slice.index.private_slice_index.Sealed Usize := {}

/- Trait implementation: [core::slice::index::usize] -/
@[reducible]
def core.slice.index.SliceIndexUsizeSliceTInst (T : Type) :
  core.slice.index.SliceIndex Usize (Slice T) := {
  sealedInst := core.slice.index.private_slice_index.SealedUsizeInst
  Output := T
  get := core.slice.index.Usize.get
  get_mut := core.slice.index.Usize.get_mut
  get_unchecked := core.slice.index.Usize.get_unchecked
  get_unchecked_mut := core.slice.index.Usize.get_unchecked_mut
  index := core.slice.index.Usize.index
  index_mut := core.slice.index.Usize.index_mut
}

def core.slice.Slice.copy_from_slice {T : Type} (_ : core.marker.Copy T)
  (s : Slice T) (src: Slice T) : Result (Slice T) :=
  if s.len = src.len then ok src
  else fail panic

/- [core::array::TryFromSliceError] -/
def core.array.TryFromSliceError := ()

end Std

end Aeneas
