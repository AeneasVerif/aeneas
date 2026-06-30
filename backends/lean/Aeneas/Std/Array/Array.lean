/- Arrays -/
import Aeneas.Data.List
import Aeneas.Tactic.Step.Init
import Aeneas.Std.Array.Core
import Aeneas.Std.Core.Default

namespace Aeneas.Std

open Result Error WP

local macro_rules
| `(tactic| get_elem_tactic) => `(tactic| grind)

/-!
# Array
-/

def Array (α : Type u) (n : Usize) := { l : List α // l.length = n.val }

/-- We need this to coerce arrays to lists without marking `Array` as reducible.
    Also not that we *do not* want to mark `Array` as reducible: it triggers issues.
-/
instance (α : Type u) (n : Usize) : CoeOut (Array α n) (List α) where
  coe := λ v => v.val

instance [BEq α] : BEq (Array α n) := SubtypeBEq _

instance [BEq α] [LawfulBEq α] : LawfulBEq (Array α n) := SubtypeLawfulBEq _

instance {α : Type u} {n : Usize} [Inhabited α] : Inhabited (Array α n) :=
  ⟨ ⟨ List.replicate n.val default, by simp ⟩ ⟩

def Array.empty (α : Type u) : Array α (Usize.ofNat 0) := ⟨ [], by simp ⟩

/- Registering some theorems for `scalar_tac` -/
@[scalar_tac_simps, grind =, agrind =]
theorem Array.length_eq {α : Type u} {n : Usize} (a : Array α n) : a.val.length = n.val := by
  cases a; simp[*]

@[simp, scalar_tac_simps, simp_scalar_safe, simp_lists_safe, grind, agrind]
abbrev Array.length {α : Type u} {n : Usize} (v : Array α n) : Nat := v.val.length

@[simp, scalar_tac_simps, simp_scalar_safe, simp_lists_safe, grind, agrind]
abbrev Array.v {α : Type u} {n : Usize} (v : Array α n) : List α := v.val

example {α: Type u} {n : Usize} (v : Array α n) : v.length ≤ Usize.max := by
  scalar_tac

def Array.make {α : Type u} (n : Usize) (init : List α) (hl : init.length = n.val := by simp) :
  Array α n := ⟨ init, by apply hl ⟩

example : Array Int (Usize.ofNat 2) := Array.make (Usize.ofNat 2) [0, 1] (by simp)

example : Array Int (Usize.ofNat 2) :=
  let x := 0
  let y := 1
  Array.make (Usize.ofNat 2) [x, y]

example : Result (Array Int (Usize.ofNat 2)) := do
  let x ← ok 0
  let y ← ok 1
  ok (Array.make (Usize.ofNat 2) [x, y])

instance {α : Type u} {n : Usize} : GetElem (Array α n) Nat α (fun a i => i < a.val.length) where
  getElem a i h := getElem a.val i h

@[simp, grind =, agrind =, simp_lists_safe, simp_lists_hyps_simps]
theorem Array.getElem_Nat_eq {α : Type u} {n : Usize} (v : Array α n) (i : Nat) (h : i < v.val.length) :
    v[i] = v.val[i] := rfl

instance {α : Type u} {n : Usize} : GetElem? (Array α n) Nat α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i

@[simp, scalar_tac_simps, simp_lists_hyps_simps, simp_lists_safe, grind =, agrind =]
theorem Array.getElem?_Nat_eq {α : Type u} {n : Usize} (v : Array α n) (i : Nat) : v[i]? = v.val[i]? := by rfl

@[simp, scalar_tac_simps, simp_lists_hyps_simps, simp_lists_safe, grind = _, agrind = _]
theorem Array.getElem!_Nat_eq {α : Type u} [Inhabited α] {n : Usize} (v : Array α n) (i : Nat) : v[i]! = v.val[i]! := by
  simp only [getElem!]; split <;> (simp_all; try rfl)

instance {α : Type u} {n : Usize} : GetElem (Array α n) Usize α (fun a i => i.val < a.val.length) where
  getElem a i h := getElem a.val i.val h

@[simp, grind =, agrind =, simp_lists_safe, simp_lists_hyps_simps]
theorem Array.getElem_Usize_eq {α : Type u} {n : Usize} (v : Array α n) (i : Usize) (h : i.val < v.val.length) :
    v[i]'h = v.val[i.val] := rfl

instance {α : Type u} {n : Usize} : GetElem? (Array α n) Usize α (fun a i => i.val < a.val.length) where
  getElem? a i := getElem? a.val i.val

@[simp, scalar_tac_simps, simp_lists_hyps_simps, simp_lists_safe, grind =, agrind =]
theorem Array.getElem?_Usize_eq {α : Type u} {n : Usize} (v : Array α n) (i : Usize) : v[i]? = v.val[i.val]? := by rfl

@[simp, scalar_tac_simps, simp_lists_hyps_simps, simp_lists_safe, grind = _, agrind = _]
theorem Array.getElem!_Usize_eq {α : Type u} [Inhabited α] {n : Usize} (v : Array α n) (i : Usize) : v[i]! = v.val[i.val]! := by
  simp only [getElem!]; split <;> (simp_all; try rfl)

@[simp, scalar_tac_simps, simp_lists_hyps_simps, grind, agrind] abbrev Array.get? {α : Type u} {n : Usize} (v : Array α n) (i : Nat) : Option α := getElem? v i
@[simp, scalar_tac_simps, simp_lists_hyps_simps, grind, agrind] abbrev Array.get! {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i : Nat) : α := getElem! v i

@[simp]
abbrev Array.slice {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i j : Nat) : List α :=
  v.val.slice i j

def Array.index_usize {α : Type u} {n : Usize} (v: Array α n) (i: Usize) : Result α :=
  match v[i]? with
  | none => fail .arrayOutOfBounds
  | some x => ok x

-- For initialization
def Array.repeat {α : Type u} (n : Usize) (x : α) : Array α n :=
  ⟨ List.replicate n.val x, by simp_all ⟩

@[simp]
theorem Array.repeat_val (n : Usize) (x : α) : (Array.repeat n x).val = List.replicate n.val x := by
  simp only [Array.repeat]

@[step]
theorem Array.index_usize_spec {α : Type u} {n : Usize} (v: Array α n) (i: Usize)
  (hbound : i.val < v.length) :
  (v.index_usize i) ⦃ x => x = v.val[i.val] ⦄ := by
  grind [index_usize]

def Array.set {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) : Array α n :=
  ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

def Array.set_opt {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: Option α) : Array α n :=
  ⟨ v.val.set_opt i.val x, by have := v.property; simp [*] ⟩

@[simp, scalar_tac_simps, simp_lists_hyps_simps, simp_lists_safe, grind =, agrind =]
theorem Array.set_val_eq {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) :
  (v.set i x).val = v.val.set i.val x := by
  simp [set]

@[simp, scalar_tac_simps, simp_lists_hyps_simps, simp_lists_safe, grind =, agrind =]
theorem Array.set_opt_val_eq {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: Option α) :
  (v.set_opt i x).val = v.val.set_opt i.val x := by
  simp [set_opt]


/-- Using `↓` to eagerly simplify combinations of `set` and `getElem!` in expressions like:
`(((l.set i0 x0) ...).set in xn)[j]!`

Otherwise we might lose a lot of time reordering the `set` expressions.
-/
@[simp↓, simp_lists_safe↓]
theorem Array.getElem!_Usize_set_ne
  {α : Type u} {N : Usize} [Inhabited α] (a: Array α N) (i j : Usize) (x: α)
  (h : i.val ≠ j.val) : (a.set i x)[j]! = a[j]!
  := by
  simp only [getElem!_Usize_eq, set_val_eq]; grind

@[simp↓, simp_lists_safe↓]
theorem Array.getElem_Usize_set_ne
  {α : Type u} {N : Usize} (a: Array α N) (i j : Usize) (x: α)
  (h : i.val ≠ j.val ∧ j.val < a.length) :
  (a.set i x)[j] = a[j]
  := by
  grind

@[simp↓, simp_lists_safe↓]
theorem Array.getElem!_Usize_set_eq
  {α : Type u} {N : Usize} [Inhabited α] (a: Array α N) (i i' : Usize) (x: α)
  (h : i = i' ∧ i'.val < a.length) : getElem! (a.set i x) i' = x
  := by
  simp only [getElem!_Usize_eq, set_val_eq]; grind

@[simp↓, simp_lists_safe↓]
theorem Array.getElem_Usize_set_eq
  {α : Type u} {N : Usize} (a: Array α N) (i j : Usize) (x: α)
  (h : i = j ∧ j.val < a.length) :
  (a.set i x)[j] = x
  := by
  grind

/-- Using `↓` to eagerly simplify combinations of `set` and `getElem!` in expressions like:
`(((l.set i0 x0) ...).set in xn)[j]!`

Otherwise we might lose a lot of time reordering the `set` expressions.
-/
@[simp↓, simp_lists_safe↓]
theorem Array.getElem!_Nat_set_ne
  {α : Type u} {N : Usize} [Inhabited α] (a: Array α N) (i : Usize) (j : Nat) (x: α)
  (h : i.val ≠ j) : (a.set i x)[j]! = a[j]!
  := by simp only [getElem!_Nat_eq, set_val_eq]; grind

@[simp↓, simp_lists_safe↓]
theorem Array.getElem_Nat_set_ne
  {α : Type u} {N : Usize} (a: Array α N) (i : Usize) (j : Nat) (x: α)
  (h0 : j < (a.set i x).length) (h1 : i.val ≠ j) :
  (a.set i x)[j]'h0 = a[j]
  := by grind

@[simp↓, simp_lists_safe↓]
theorem Array.getElem!_Nat_set_eq
  {α : Type u} {N : Usize} [Inhabited α] (a: Array α N) (i : Usize) (i' : Nat) (x: α)
  (h : i.val = i' ∧ i' < a.length) : getElem! (a.set i x) i' = x
  := by simp only [getElem!_Nat_eq, set_val_eq]; grind

@[simp↓, simp_lists_safe↓]
theorem Array.getElem_Nat_set_eq
  {α : Type u} {N : Usize} (a: Array α N) (i : Usize) (j : Nat) (x: α)
  (h0 : j < (a.set i x).length) (h1 : i.val = j) :
  (a.set i x)[j]'h0 = x
  := by grind

@[scalar_tac_simps, simp_lists_safe, grind =, agrind =]
theorem Array.set_length {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) :
  (v.set i x).length = v.length := by simp

def Array.update {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) : Result (Array α n) :=
  match v[i]? with
  | none => fail .arrayOutOfBounds
  | some _ =>
    ok ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

@[step]
theorem Array.update_spec {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  v.update i x ⦃ nv => nv = v.set i x ⦄
  := by
  simp only [update, set]
  simp at *
  split <;> simp_all

def Array.index_mut_usize {α : Type u} {n : Usize} (v: Array α n) (i: Usize) :
  Result (α × (α -> Array α n)) := do
  let x ← index_usize v i
  ok (x, set v i)

@[step]
theorem Array.index_mut_usize_spec {α : Type u} {n : Usize} (v: Array α n) (i: Usize)
  (hbound : i.val < v.length) :
  v.index_mut_usize i ⦃ x back => x = v.val[i.val] ∧ back = set v i ⦄ := by
  simp only [index_mut_usize, Bind.bind, bind]
  have ⟨ x, h ⟩ := spec_imp_exists (index_usize_spec v i hbound)
  simp [h]

@[simp]
theorem Array.set_getElem!_eq {α} {n : Usize} [Inhabited α] (x : Array α n) (i : Usize) :
  x.set i (x.val[i.val]!) = x := by
  have := @List.set_getElem_self _ x.val i.val
  simp only [Array, Subtype.ext_iff, set_val_eq, List.set_getElem!]

@[simp]
theorem Array.set_getElem_eq {α} {n : Usize} (x : Array α n) (i : Usize) (h : i.val < x.length) :
  x.set i x[i] = x := by
  have h' : i.val < x.val.length := by
    simpa using h
  have hself : x.val.set i.val x.val[i.val] = x.val :=
    List.set_getElem_self (as := x.val) (i := i.val) (h := h')
  simp only [Array, Subtype.ext_iff, set_val_eq] at hself ⊢
  exact hself

@[simp↓, simp_lists_safe↓]
theorem Array.getElem_set_eq {α} {n : Usize} (v : Array α n) (i : Usize) (x : α) (h : i.val < (v.set i x).length) :
  (v.set i x)[i]'h = x := by
  cases v
  unfold set getElem instGetElemArrayUsizeLtNatValLengthValListEq
  simp only [List.getElem_set_self]

@[simp↓, simp_lists_safe↓]
theorem Array.getElem_set_eq' {α} {n : Usize} (v : Array α n) (i j : Usize) (x : α) (h : j.val < (v.set i x).length)
  (h' : i = j) :
  (v.set i x)[j]'h = x := by
  simp only [↓getElem_set_eq, h']

@[simp↓, simp_lists_safe↓]
theorem Array.getElem_set_neq {α} {n : Usize} (v : Array α n) (i j : Usize) (x : α)
  (h : j.val < (v.set i x).length) (h' : i ≠ j) :
  (v.set i x)[j]'h = v[j] := by
  cases v
  unfold set getElem instGetElemArrayUsizeLtNatValLengthValListEq
  simp only [ne_eq, UScalar.neq_to_neq_val] at *
  simp_lists [List.getElem_set_ne]

/-- Small helper (this function doesn't model a specific Rust function) -/
def Array.clone {α : Type u} {n : Usize} (clone : α → Result α) (s : Array α n) : Result (Array α n) := do
  let s' ← List.clone clone s.val
  ok ⟨ s', by have:= s'.property; scalar_tac ⟩

theorem Array.clone_length {α : Type u} {n : Usize} (clone : α → Result α) (s s' : Array α n) (h : Array.clone clone s = ok s') :
  s'.length = s.length := by
  simp [Array.clone] at h
  simp [List.clone] at h
  split at h <;> simp_all

@[step]
theorem Array.clone_spec {α : Type u} {n : Usize} {clone : α → Result α} {s : Array α n} (h : ∀ x ∈ s.val, clone x = ok x) :
  Array.clone clone s ⦃ s' => s' = s ⦄ := by
  simp only [Array.clone]
  have ⟨ l', h ⟩ := spec_imp_exists (List.clone_spec h)
  simp [h]

@[rust_fun "core::array::{core::clone::Clone<[@T; @N]>}::clone"]
def core.array.CloneArray.clone
  {T : Type} {N : Usize} (cloneInst : core.clone.Clone T) (a : Array T N) : Result (Array T N) :=
  Array.clone cloneInst.clone a

@[step]
theorem core.array.CloneArray.clone_spec {T : Type} {N : Usize} (cloneInst : core.clone.Clone T) (a : Array T N)
  (h : ∀ x ∈ a.val, cloneInst.clone x = ok x) :
  core.array.CloneArray.clone cloneInst a ⦃ a' => a = a' ⦄:= by
  unfold clone
  have := spec_imp_exists (Array.clone_spec h)
  grind

@[rust_fun "core::array::{core::clone::Clone<[@T; @N]>}::clone_from"]
def core.array.CloneArray.clone_from {T : Type} {N : Usize} (cloneInst : core.clone.Clone T)
  (_self source : Array T N) : Result (Array T N) :=
  Array.clone cloneInst.clone source

@[step]
theorem core.array.CloneArray.clone_from_spec {T : Type} {N : Usize} (cloneInst : core.clone.Clone T)
  (self source : Array T N) (h : ∀ x ∈ source.val, cloneInst.clone x = ok x) :
  core.array.CloneArray.clone_from cloneInst self source ⦃ source' => source = source' ⦄ := by
  unfold clone_from
  have := spec_imp_exists (Array.clone_spec h)
  grind

@[reducible, rust_trait_impl "core::clone::Clone<[@T; @N]>"]
def core.clone.CloneArray {T : Type} (N : Usize)
  (cloneCloneInst : core.clone.Clone T) : core.clone.Clone (Array T N) := {
  clone := core.array.CloneArray.clone cloneCloneInst
  clone_from := core.array.CloneArray.clone_from cloneCloneInst
}

def Array.setSlice! {α : Type u} {n} (s : Array α n) (i : ℕ) (s' : List α) : Array α n :=
  ⟨s.val.setSlice! i s', by scalar_tac⟩

@[simp_lists_safe]
theorem Array.setSlice!_getElem!_prefix {α} {n} [Inhabited α]
  (s : Array α n) (s' : List α) (i j : ℕ) (h : j < i) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [Array.setSlice!, Array.getElem!_Nat_eq]
  simp_lists

@[simp_lists_safe]
theorem Array.setSlice!_getElem_prefix {α} {n}
  (s : Array α n) (s' : List α) (i j : ℕ) (h : j < i ∧ j < s.length) :
  (s.setSlice! i s')[j] = s[j] := by
  have hj' : j < (s.setSlice! i s').length := by scalar_tac
  have h1 : (s.setSlice! i s')[j]? = s[j]? := by
    simp only [Array.getElem?_Nat_eq, Array.setSlice!]
    simp_lists [List.setSlice!_getElem?_prefix]
  simpa [Array.getElem?_Nat_eq, Array.getElem_Nat_eq,
    List.getElem?_eq_getElem hj', List.getElem?_eq_getElem h.2] using h1

@[simp_lists_safe]
theorem Array.setSlice!_getElem!_middle {α} {n} [Inhabited α]
  (s : Array α n) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.length) :
  (s.setSlice! i s')[j]! = s'[j - i]! := by
  simp only [Array.setSlice!, Array.getElem!_Nat_eq]
  simp_lists

@[simp_lists_safe]
theorem Array.setSlice!_getElem_middle {α} {n}
  (s : Array α n) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.length) :
  (s.setSlice! i s')[j] = s'[j - i] := by
  have hj' : j < (s.setSlice! i s').length := by
    scalar_tac
  have hji : j - i < s'.length := h.2.1
  have h1 : (s.setSlice! i s')[j]? = s'[j - i]? := by
    simp only [Array.getElem?_Nat_eq, Array.setSlice!]
    simp_lists [List.setSlice!_getElem?_middle]
  simpa [Array.getElem?_Nat_eq, Array.getElem_Nat_eq,
    List.getElem?_eq_getElem hj', List.getElem?_eq_getElem hji] using h1

theorem Array.setSlice!_getElem!_suffix {α} {n} [Inhabited α]
  (s : Array α n) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [Array.setSlice!, Array.getElem!_Nat_eq]
  simp_lists

theorem Array.setSlice!_getElem_suffix {α} {n}
  (s : Array α n) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j ∧ j < s.length) :
  (s.setSlice! i s')[j] = s[j] := by
  have hj' : j < (s.setSlice! i s').length := by scalar_tac
  have h1 : (s.setSlice! i s')[j]? = s[j]? := by
    simp only [Array.getElem?_Nat_eq, Array.setSlice!]
    simp_lists [List.setSlice!_getElem?_suffix]
  simpa [Array.getElem?_Nat_eq, Array.getElem_Nat_eq,
    List.getElem?_eq_getElem hj', List.getElem?_eq_getElem h.2] using h1

/- Remark: see the comment for `core.default.DefaultArray` -/
@[rust_fun "core::array::{core::default::Default<[@T; @N]>}::default"]
def core.default.DefaultArray.default {T : Type} (N : Usize) (defaultInst : core.default.Default T) : Result (Array T N) := do
  let x ← defaultInst.default
  .ok (Array.repeat N x)

/- Remark: the `Default` instance actually doesn't exist for *any* const generic `N`. Rather,
   there exists one instance per known length different from 0 (and a different instance for
   the case where the length is equal to 0, because in this case we don't need the type of
   the elements to have a default value). We factor the cases where `N` is ≠ 0 in the Lean model.
 -/
@[reducible, rust_trait_impl "core::default::Default<[@T; @N]>"]
def core.default.DefaultArray {T : Type} (N : Usize)
  (defaultInst : core.default.Default T) : core.default.Default (Array T N) := {
  default := core.default.DefaultArray.default N defaultInst
}

@[rust_fun "core::array::{core::default::Default<[@T; 0]>}::default"]
def core.default.DefaultArrayEmpty.default (T : Type) : Result (Array T (Usize.ofNat 0)) :=
  ok ⟨ [], by scalar_tac ⟩

/- See the comments for `core.default.DefaultArray` -/
@[reducible, rust_trait_impl "core::default::Default<[@T; 0]>"]
def core.default.DefaultArrayEmpty (T : Type) : core.default.Default (Array T (Usize.ofNat 0)) := {
  default := core.default.DefaultArrayEmpty.default T
}

@[reducible, rust_trait_impl "core::marker::Copy<[@T; @N]>"]
def Array.Insts.CoreMarkerCopy {T : Type} (N : Std.Usize)
  (markerCopyInst : core.marker.Copy T) : core.marker.Copy (Array T N) := {
  cloneInst := core.clone.CloneArray N markerCopyInst.cloneInst
}

end Aeneas.Std
