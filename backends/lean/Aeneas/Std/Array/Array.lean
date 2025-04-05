/- Arrays/Slices -/
import Aeneas.List
import Aeneas.Progress.Init

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

-- TODO: remove
@[scalar_tac a.val]
theorem Array.length_eq' {α : Type u} {n : Usize} (a : Array α n) : a.val.length = n.val ∧ n.val ≤ Usize.max := by
  cases a; simp[*]
  scalar_tac

-- TODO: remove
@[scalar_tac a.val.length]
theorem Array.length_eq'' {α : Type u} {n : Usize} (a : Array α n) : a.val.length = n.val ∧ n.val ≤ Usize.max := by
  cases a; simp[*]
  scalar_tac

@[simp]
abbrev Array.length {α : Type u} {n : Usize} (v : Array α n) : Nat := v.val.length

@[simp]
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

@[simp, scalar_tac_simps] theorem Array.getElem?_Nat_eq {α : Type u} {n : Usize} (v : Array α n) (i : Nat) : v[i]? = v.val[i]? := by rfl
@[simp, scalar_tac_simps] theorem Array.getElem!_Nat_eq {α : Type u} [Inhabited α] {n : Usize} (v : Array α n) (i : Nat) : v[i]! = v.val[i]! := by rfl

@[reducible] instance {α : Type u} {n : Usize} : GetElem (Array α n) Usize α (fun a i => i.val < a.val.length) where
  getElem a i h := getElem a.val i.val h

@[reducible] instance {α : Type u} {n : Usize} : GetElem? (Array α n) Usize α (fun a i => i.val < a.val.length) where
  getElem? a i := getElem? a.val i.val

@[simp, scalar_tac_simps] theorem Array.getElem?_Usize_eq {α : Type u} {n : Usize} (v : Array α n) (i : Usize) : v[i]? = v.val[i.val]? := by rfl
@[simp, scalar_tac_simps] theorem Array.getElem!_Usize_eq {α : Type u} [Inhabited α] {n : Usize} (v : Array α n) (i : Usize) : v[i]! = v.val[i.val]! := by rfl

@[simp, scalar_tac_simps] abbrev Array.get? {α : Type u} {n : Usize} (v : Array α n) (i : Nat) : Option α := getElem? v i
@[simp, scalar_tac_simps] abbrev Array.get! {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i : Nat) : α := getElem! v i

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
  split <;> simp_all

def Array.set {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) : Array α n :=
  ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

def Array.set_opt {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: Option α) : Array α n :=
  ⟨ v.val.set_opt i.val x, by have := v.property; simp [*] ⟩

@[simp]
theorem Array.set_val_eq {α : Type u} {n : Usize} (v: Array α n) (i: Usize) (x: α) :
  (v.set i x).val = v.val.set i.val x := by
  simp [set]

@[simp]
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
  x = v.val.get! i.val := by
  simp only [index_mut_usize, Bind.bind, bind]
  have ⟨ x, h ⟩ := index_usize_spec v i hbound
  simp [h]

@[simp]
theorem Array.set_getElem!_eq α n [Inhabited α] (x : Array α n) (i : Usize) :
  x.set i (x.val[i.val]!) = x := by
  have := @List.set_getElem_self _ x.val i.val
  simp only [Array, Subtype.eq_iff, set_val_eq, List.set_getElem!]

end Aeneas.Std
