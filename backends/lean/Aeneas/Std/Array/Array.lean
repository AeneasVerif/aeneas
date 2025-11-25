/- Arrays -/
import Aeneas.List
import Aeneas.Progress.Init
import Aeneas.Std.Array.Core
import Aeneas.Std.Core.Default

namespace Aeneas.Std

open Result Error

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

/- Registering some theorems for `scalar_tac` -/
@[scalar_tac_simps]
theorem Array.length_eq {α : Type u} {n : Usize} (a : Array α n) : a.val.length = n.val := by
  cases a; simp[*]

@[simp, scalar_tac_simps, simp_scalar_simps, simp_lists_simps]
abbrev Array.length {α : Type u} {n : Usize} (v : Array α n) : Nat := v.val.length

@[simp, scalar_tac_simps, simp_scalar_simps, simp_lists_simps]
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

@[reducible] instance {α : Type u} {n : Usize} : GetElem (Array α n) Nat α (fun a i => i < a.val.length) where
  getElem a i h := getElem a.val i h

@[reducible] instance {α : Type u} {n : Usize} : GetElem? (Array α n) Nat α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Array.getElem?_Nat_eq {α : Type u} {n : Usize} (v : Array α n) (i : Nat) : v[i]? = v.val[i]? := by rfl

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Array.getElem!_Nat_eq {α : Type u} [Inhabited α] {n : Usize} (v : Array α n) (i : Nat) : v[i]! = v.val[i]! := by
  simp only [instGetElem?ArrayNatLtLengthValListEqVal, List.getElem!_eq_getElem?_getD]; split <;> simp_all
  rfl

@[reducible] instance {α : Type u} {n : Usize} : GetElem (Array α n) Usize α (fun a i => i.val < a.val.length) where
  getElem a i h := getElem a.val i.val h

@[reducible] instance {α : Type u} {n : Usize} : GetElem? (Array α n) Usize α (fun a i => i.val < a.val.length) where
  getElem? a i := getElem? a.val i.val

@[simp, scalar_tac_simps, simp_lists_hyps_simps] theorem Array.getElem?_Usize_eq {α : Type u} {n : Usize} (v : Array α n) (i : Usize) : v[i]? = v.val[i.val]? := by rfl
@[simp, scalar_tac_simps, simp_lists_hyps_simps] theorem Array.getElem!_Usize_eq {α : Type u} [Inhabited α] {n : Usize} (v : Array α n) (i : Usize) : v[i]! = v.val[i.val]! := by
  simp [instGetElem?ArrayUsizeLtNatValLengthValListEq]; split <;> simp_all
  rfl

@[simp, scalar_tac_simps, simp_lists_hyps_simps] abbrev Array.get? {α : Type u} {n : Usize} (v : Array α n) (i : Nat) : Option α := getElem? v i
@[simp, scalar_tac_simps, simp_lists_hyps_simps] abbrev Array.get! {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i : Nat) : α := getElem! v i

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

@[progress]
theorem Array.repeat_spec {α : Type u} (n : Usize) (x : α) :
  ∃ a, Array.repeat n x = a ∧ a.val = List.replicate n.val x := by
  simp [Array.repeat]

/- In the theorems below: we don't always need the `∃ ..`, but we use one
   so that `progress` introduces an opaque variable and an equality. This
   helps control the context.
 -/

@[progress]
theorem Array.index_usize_spec {α : Type u} {n : Usize} [Inhabited α] (v: Array α n) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val[i.val]! := by
  simp only [index_usize]
  simp at *
  split <;> simp_all only [List.Vector.length_val, List.getElem?_eq_getElem, Option.some.injEq,
    Option.getD_some, reduceCtorEq]

def Array.set {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) : Array α n :=
  ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

def Array.set_opt {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: Option α) : Array α n :=
  ⟨ v.val.set_opt i.val x, by have := v.property; simp [*] ⟩

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Array.set_val_eq {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) :
  (v.set i x).val = v.val.set i.val x := by
  simp [set]

@[simp, scalar_tac_simps, simp_lists_hyps_simps]
theorem Array.set_opt_val_eq {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: Option α) :
  (v.set_opt i x).val = v.val.set_opt i.val x := by
  simp [set_opt]

@[scalar_tac_simps]
theorem Array.set_length {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) :
  (v.set i x).length = v.length := by simp

def Array.update {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) : Result (Array α n) :=
  match v[i]? with
  | none => fail .arrayOutOfBounds
  | some _ =>
    ok ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

@[progress]
theorem Array.update_spec {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.update i x = ok nv ∧
  nv = v.set i x
  := by
  simp only [update, set]
  simp at *
  split <;> simp_all

def Array.index_mut_usize {α : Type u} {n : Usize} (v: Array α n) (i: Usize) :
  Result (α × (α -> Array α n)) := do
  let x ← index_usize v i
  ok (x, set v i)

@[progress]
theorem Array.index_mut_usize_spec {α : Type u} {n : Usize} [Inhabited α] (v: Array α n) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_mut_usize i = ok (x, set v i) ∧
  x = v.val[i.val]! := by
  simp only [index_mut_usize, Bind.bind, bind]
  have ⟨ x, h ⟩ := index_usize_spec v i hbound
  simp [h]

@[simp]
theorem Array.set_getElem!_eq α n [Inhabited α] (x : Array α n) (i : Usize) :
  x.set i (x.val[i.val]!) = x := by
  have := @List.set_getElem_self _ x.val i.val
  simp only [Array, Subtype.eq_iff, set_val_eq, List.set_getElem!]

/-- Small helper (this function doesn't model a specific Rust function) -/
def Array.clone {α : Type u} {n : Usize} (clone : α → Result α) (s : Array α n) : Result (Array α n) := do
  let s' ← List.clone clone s.val
  ok ⟨ s', by have:= s'.property; scalar_tac ⟩

theorem Array.clone_length {α : Type u} {n : Usize} (clone : α → Result α) (s s' : Array α n) (h : Array.clone clone s = ok s') :
  s'.length = s.length := by
  simp [Array.clone] at h
  simp [List.clone] at h
  split at h <;> simp_all

@[progress]
theorem Array.clone_spec {α : Type u} {n : Usize} {clone : α → Result α} {s : Array α n} (h : ∀ x ∈ s.val, clone x = ok x) :
  Array.clone clone s = ok s := by
  simp only [Array.clone]
  have ⟨ l', h ⟩ := List.clone_spec h
  simp [h]

@[rust_fun "core::array::{core::clone::Clone<[@T; @N]>}::clone"]
def core.array.CloneArray.clone
  {T : Type} {N : Usize} (cloneInst : core.clone.Clone T) (a : Array T N) : Result (Array T N) :=
  Array.clone cloneInst.clone a

@[progress]
theorem core.array.CloneArray.clone_spec {T : Type} {N : Usize} (cloneInst : core.clone.Clone T) (a : Array T N)
  (h : ∀ x ∈ a.val, cloneInst.clone x = ok x) :
  core.array.CloneArray.clone cloneInst a = ok a := by
  unfold clone
  rw [Array.clone_spec h]

@[rust_fun "core::array::{core::clone::Clone<[@T; @N]>}::clone_from"]
def core.array.CloneArray.clone_from {T : Type} {N : Usize} (cloneInst : core.clone.Clone T)
  (_self source : Array T N) : Result (Array T N) :=
  Array.clone cloneInst.clone source

@[progress]
theorem core.array.CloneArray.clone_from_spec {T : Type} {N : Usize} (cloneInst : core.clone.Clone T)
  (self source : Array T N) (h : ∀ x ∈ source.val, cloneInst.clone x = ok x) :
  core.array.CloneArray.clone_from cloneInst self source = ok source := by
  unfold clone_from
  rw [Array.clone_spec h]

@[reducible, rust_trait_impl "core::clone::Clone<[@T; @N]>"]
def core.clone.CloneArray {T : Type} (N : Usize)
  (cloneCloneInst : core.clone.Clone T) : core.clone.Clone (Array T N) := {
  clone := core.array.CloneArray.clone cloneCloneInst
  clone_from := core.array.CloneArray.clone_from cloneCloneInst
}

def Array.setSlice! {α : Type u} {n} (s : Array α n) (i : ℕ) (s' : List α) : Array α n :=
  ⟨s.val.setSlice! i s', by scalar_tac⟩

@[simp_lists_simps]
theorem Array.setSlice!_getElem!_prefix {α} {n} [Inhabited α]
  (s : Array α n) (s' : List α) (i j : ℕ) (h : j < i) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [Array.setSlice!, Array.getElem!_Nat_eq]
  simp_lists

@[simp_lists_simps]
theorem Array.setSlice!_getElem!_middle {α} {n} [Inhabited α]
  (s : Array α n) (s' : List α) (i j : ℕ) (h : i ≤ j ∧ j - i < s'.length ∧ j < s.length) :
  (s.setSlice! i s')[j]! = s'[j - i]! := by
  simp only [Array.setSlice!, Array.getElem!_Nat_eq]
  simp_lists

theorem Array.setSlice!_getElem!_suffix {α} {n} [Inhabited α]
  (s : Array α n) (s' : List α) (i j : ℕ) (h : i + s'.length ≤ j) :
  (s.setSlice! i s')[j]! = s[j]! := by
  simp only [Array.setSlice!, Array.getElem!_Nat_eq]
  simp_lists

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
def core.default.DefaultArray {T : Type} {N : Usize}
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

end Aeneas.Std
