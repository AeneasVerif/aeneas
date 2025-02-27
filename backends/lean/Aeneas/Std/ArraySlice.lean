/- Arrays/Slices -/
import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.Linarith
import Aeneas.List
import Aeneas.Std.Scalar
import Aeneas.Std.Range
import Aeneas.Std.Core
import Aeneas.ScalarTac
import Aeneas.Progress.Core

namespace Aeneas

namespace Std

open Result Error core.ops.range

/-!
# Notations for `List`
-/
instance {α : Type u} : GetElem (List α) Usize α (fun l i => i.val < l.length) where
  getElem l i h := getElem l i.val h

instance {α : Type u} : GetElem? (List α) Usize α (fun l i => i < l.length) where
  getElem? l i := getElem? l i.val

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

@[simp, scalar_tac_simp] theorem Array.getElem?_Nat_eq {α : Type u} {n : Usize} (v : Array α n) (i : Nat) : v[i]? = v.val[i]? := by rfl
@[simp, scalar_tac_simp] theorem Array.getElem!_Nat_eq {α : Type u} [Inhabited α] {n : Usize} (v : Array α n) (i : Nat) : v[i]! = v.val[i]! := by rfl

@[reducible] instance {α : Type u} {n : Usize} : GetElem (Array α n) Usize α (fun a i => i.val < a.val.length) where
  getElem a i h := getElem a.val i.val h

@[reducible] instance {α : Type u} {n : Usize} : GetElem? (Array α n) Usize α (fun a i => i.val < a.val.length) where
  getElem? a i := getElem? a.val i.val

@[simp, scalar_tac_simp] theorem Array.getElem?_Usize_eq {α : Type u} {n : Usize} (v : Array α n) (i : Usize) : v[i]? = v.val[i.val]? := by rfl
@[simp, scalar_tac_simp] theorem Array.getElem!_Usize_eq {α : Type u} [Inhabited α] {n : Usize} (v : Array α n) (i : Usize) : v[i]! = v.val[i.val]! := by rfl

@[simp, scalar_tac_simp] abbrev Array.get? {α : Type u} {n : Usize} (v : Array α n) (i : Nat) : Option α := getElem? v i
@[simp, scalar_tac_simp] abbrev Array.get! {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i : Nat) : α := getElem! v i

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

@[scalar_tac_simp]
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

@[scalar_tac s]
theorem Slice.length_ineq {α : Type u} (s : Slice α) : s.val.length ≤ Usize.max := by
  cases s; simp[*]

-- TODO: move/remove?
@[scalar_tac s]
theorem Slice.subtype_property {α : Type u} {p : Slice α → Prop} (s : Subtype p) : p s.val := s.property

@[simp]
abbrev Slice.length {α : Type u} (v : Slice α) : Nat := v.val.length

@[simp]
abbrev Slice.v {α : Type u} (v : Slice α) : List α := v.val

example {a: Type u} (v : Slice a) : v.length ≤ Usize.max := by
  scalar_tac

def Slice.new (α : Type u) : Slice α := ⟨ [], by simp ⟩

-- TODO: very annoying that the α is an explicit parameter
abbrev Slice.len {α : Type u} (v : Slice α) : Usize :=
  Usize.ofNatCore v.val.length (by scalar_tac)

@[simp, scalar_tac_simp]
theorem Slice.len_val {α : Type u} (v : Slice α) : (Slice.len v).val = v.length :=
  by simp

@[reducible] instance {α : Type u} : GetElem (Slice α) Nat α (fun a i => i < a.val.length) where
  getElem a i h := getElem a.val i h

@[reducible] instance {α : Type u} : GetElem? (Slice α) Nat α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i

@[simp, scalar_tac_simp] theorem Slice.getElem?_Nat_eq {α : Type u} (v : Slice α) (i : Nat) : v[i]? = v.val[i]? := by rfl
@[simp, scalar_tac_simp] theorem Slice.getElem!_Nat_eq {α : Type u} [Inhabited α] (v : Slice α) (i : Nat) : v[i]! = v.val[i]! := by rfl

@[reducible] instance {α : Type u} : GetElem (Slice α) Usize α (fun a i => i.val < a.val.length) where
  getElem a i h := getElem a.val i.val h

@[reducible] instance {α : Type u} : GetElem? (Slice α) Usize α (fun a i => i < a.val.length) where
  getElem? a i := getElem? a.val i.val

@[simp, scalar_tac_simp] theorem Slice.getElem?_Usize_eq {α : Type u} (v : Slice α) (i : Usize) : v[i]? = v.val[i.val]? := by rfl
@[simp, scalar_tac_simp] theorem Slice.getElem!_Usize_eq {α : Type u} [Inhabited α] (v : Slice α) (i : Usize) : v[i]! = v.val[i.val]! := by rfl

@[simp, scalar_tac_simp] abbrev Slice.get? {α : Type u} (v : Slice α) (i : Nat) : Option α := getElem? v i
@[simp, scalar_tac_simp] abbrev Slice.get! {α : Type u} [Inhabited α] (v : Slice α) (i : Nat) : α := getElem! v i

def Slice.set {α : Type u} (v: Slice α) (i: Usize) (x: α) : Slice α :=
  ⟨ v.val.set i.val x, by have := v.property; simp [*] ⟩

def Slice.set_opt {α : Type u} (v: Slice α) (i: Usize) (x: Option α) : Slice α :=
  ⟨ v.val.set_opt i.val x, by have := v.property; simp [*] ⟩

def Slice.drop {α} (s : Slice α) (i : Usize) : Slice α :=
  ⟨ s.val.drop i.val, by scalar_tac ⟩

@[simp]
abbrev Slice.slice {α : Type u} [Inhabited α] (s : Slice α) (i j : Nat) : List α :=
  s.val.slice i j

def Slice.index_usize {α : Type u} (v: Slice α) (i: Usize) : Result α :=
  match v[i]? with
  | none => fail .arrayOutOfBounds
  | some x => ok x

/- In the theorems below: we don't always need the `∃ ..`, but we use one
   so that `progress` introduces an opaque variable and an equality. This
   helps control the context.
 -/

@[progress]
theorem Slice.index_usize_spec {α : Type u} [Inhabited α] (v: Slice α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val[i.val]! := by
  simp only [index_usize]
  simp at *
  simp [*]

@[simp]
theorem Slice.set_val_eq {α : Type u} (v: Slice α) (i: Usize) (x: α) :
  (v.set i x) = v.val.set i.val x := by
  simp [set]

@[simp]
theorem Slice.set_opt_val_eq {α : Type u} (v: Slice α) (i: Usize) (x: Option α) :
  (v.set_opt i x) = v.val.set_opt i.val x := by
  simp [set_opt]

@[scalar_tac_simp]
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

/- Array to slice/subslices -/

/- We could make this function not use the `Result` type. By making it monadic, we
   push the user to use the `Array.to_slice_spec` spec theorem below (through the
   `progress` tactic), meaning `Array.to_slice` should be considered as opaque.
   All what the spec theorem reveals is that the "representative" lists are the same. -/
def Array.to_slice {α : Type u} {n : Usize} (v : Array α n) : Result (Slice α) :=
  ok ⟨ v.val, by scalar_tac ⟩

@[progress]
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

@[progress]
theorem Array.to_slice_mut_spec {α : Type u} {n : Usize} (v : Array α n) :
  ∃ s, to_slice_mut v = ok (s, Array.from_slice v) ∧
  v.val = s.val
  := by simp [to_slice_mut, to_slice]

def Array.subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end_.val ∧ r.end_.val ≤ a.val.length then
    ok ⟨ a.val.slice r.start.val r.end_.val,
          by
            have := a.val.slice_length_le r.start.val r.end_.val
            scalar_tac ⟩
  else
    fail panic

@[progress]
theorem Array.subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize)
  (h0 : r.start.val < r.end_.val) (h1 : r.end_.val ≤ a.val.length) :
  ∃ s, subslice a r = ok s ∧
  s.val = a.val.slice r.start.val r.end_.val ∧
  (∀ i, i + r.start.val < r.end_.val → s.val[i]! = a.val[r.start.val + i]!)
  := by
  simp only [subslice, true_and, h0, h1, ↓reduceIte, ok.injEq, exists_eq_left', true_and]
  intro i _
  have := List.getElem!_slice r.start.val r.end_.val i a.val (by scalar_tac) (by scalar_tac)
  simp only [this]

set_option maxHeartbeats 500000

def Array.update_subslice {α : Type u} {n : Usize} (a : Array α n) (r : Range Usize) (s : Slice α) : Result (Array α n) :=
  -- TODO: not completely sure here
  if h: r.start.val < r.end_.val ∧ r.end_.val ≤ a.length ∧ s.val.length = r.end_.val - r.start.val then
    let s_beg := a.val.take r.start.val
    let s_end := a.val.drop r.end_.val
    have : s_beg.length = r.start.val := by
      scalar_tac
    have : s_end.length = a.val.length - r.end_.val := by
      scalar_tac
    let na := s_beg.append (s.val.append s_end)
    have : na.length = a.val.length:= by
      simp [na]; scalar_tac
    ok ⟨ na, by simp_all ⟩
  else
    fail panic

-- TODO: it is annoying to write `.val` everywhere. We could leverage coercions,
-- but: some symbols like `+` are already overloaded to be notations for monadic
-- operations/
-- We should introduce special symbols for the monadic arithmetic operations
-- (the user will never write those symbols directly).
@[progress]
theorem Array.update_subslice_spec {α : Type u} {n : Usize} [Inhabited α] (a : Array α n) (r : Range Usize) (s : Slice α)
  (_ : r.start.val < r.end_.val) (_ : r.end_.val ≤ a.length) (_ : s.length = r.end_.val - r.start.val) :
  ∃ na, update_subslice a r s = ok na ∧
  (∀ i, i < r.start.val → na[i]! = a[i]!) ∧
  (∀ i, r.start.val ≤ i → i < r.end_.val → na[i]! = s[i - r.start.val]!) ∧
  (∀ i, r.end_.val ≤ i → i < n.val → na[i]! = a[i]!) := by
  simp only [update_subslice, length, and_true, true_and, List.append_eq,
    get!, Slice.get!, ↓reduceDIte, ok.injEq, exists_eq_left', *]
  have h := List.replace_slice_getElem! r.start.val r.end_.val a.val s.val
    (by scalar_tac) (by scalar_tac) (by scalar_tac)
  simp [List.replace_slice] at h
  have ⟨ h0, h1, h2 ⟩ := h
  clear h
  split_conjs
  . intro i _
    have := h0 i (by scalar_tac)
    simp_all
  . intro i _ _
    have := h1 i (by scalar_tac) (by scalar_tac)
    simp [*]
  . intro i _ _
    have := h2 i (by scalar_tac) (by scalar_tac)
    simp [*]

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
  simp_all only [subslice, length, and_self, ite_true, ok.injEq, slice, get!, exists_eq_left',
    true_and]
  intro i _
  have := List.getElem!_slice r.start.val r.end_.val i s.val (by scalar_tac) (by scalar_tac)
  apply this

def Slice.update_subslice {α : Type u} (s : Slice α) (r : Range Usize) (ss : Slice α) : Result (Slice α) :=
  -- TODO: not completely sure here
  if h: r.start.val < r.end_.val ∧ r.end_.val ≤ s.length ∧ ss.val.length = r.end_.val - r.start.val then
    let s_beg := s.val.take r.start.val
    let s_end := s.val.drop r.end_.val
    have : s_beg.length = r.start.val := by scalar_tac
    have : s_end.length = s.val.length - r.end_.val := by scalar_tac
    let ns := s_beg.append (ss.val.append s_end)
    have : ns.length = s.val.length := by simp [ns, *]; scalar_tac
    ok ⟨ ns, by simp_all; scalar_tac ⟩
  else
    fail panic

@[progress]
theorem Slice.update_subslice_spec {α : Type u} [Inhabited α] (a : Slice α) (r : Range Usize) (ss : Slice α)
  (_ : r.start.val < r.end_.val) (_ : r.end_.val ≤ a.length) (_ : ss.length = r.end_.val - r.start.val) :
  ∃ na, update_subslice a r ss = ok na ∧
  (∀ i, i < r.start.val → na[i]! = a[i]!) ∧
  (∀ i, r.start.val ≤ i → i < r.end_.val → na[i]! = ss[i - r.start.val]!) ∧
  (∀ i, r.end_.val ≤ i → i < a.length → na[i]! = a[i]!) := by
  simp [update_subslice, *]
  have h := List.replace_slice_getElem! r.start.val r.end_.val a.val ss.val
    (by scalar_tac) (by scalar_tac) (by scalar_tac)
  simp [List.replace_slice, *] at h
  have ⟨ h0, h1, h2 ⟩ := h
  clear h
  split_conjs
  . intro i _
    have := h0 i (by scalar_tac)
    simp [*]
  . intro i _ _
    have := h1 i (by scalar_tac) (by scalar_tac)
    simp [*]
  . intro i _ _
    have := h2 i (by scalar_tac) (by scalar_tac)
    simp [*]

@[simp]
theorem Array.set_getElem!_eq α n [Inhabited α] (x : Array α n) (i : Usize) :
  x.set i (x.val[i.val]!) = x := by
  have := @List.set_getElem_self _ x.val i.val
  simp only [Array, Subtype.eq_iff, set_val_eq, List.set_getElem!]

@[simp]
theorem Slice.update_index_eq α [Inhabited α] (x : Slice α) (i : Usize) :
  x.set i (x.val[i.val]!) = x := by
  simp only [Slice, Subtype.eq_iff, set_val_eq, List.set_getElem!]

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
  (slice : Slice T) (i : I) : Result inst.Output :=
  inst.index i slice

/- [core::slice::index::Range:::get]: forward function -/
def core.slice.index.RangeUsize.get {T : Type} (r : Range Usize) (s : Slice T) :
  Result (Option (Slice T)) :=
  if r.start ≤ r.end_ ∧ r.end_ ≤ s.length then
    ok (some ⟨ s.val.slice r.start r.end_, by scalar_tac⟩)
  else ok none

/- [core::slice::index::Range::get_mut]: forward function -/
def core.slice.index.RangeUsize.get_mut
  {T : Type} (r : Range Usize) (s : Slice T) : Result (Option (Slice T) × (Option (Slice T) → Slice T)) :=
  if r.start ≤ r.end_ ∧ r.end_ ≤ s.length then
    ok (some ⟨ s.val.slice r.start r.end_, by scalar_tac⟩,
        fun s' =>
        match s' with
        | none => s
        | some s' =>
          if h: (List.replace_slice r.start r.end_ s.val s'.val).length ≤ Usize.max then
            ⟨ List.replace_slice r.start r.end_ s.val s'.val, by scalar_tac ⟩
          else s )
  else ok (none, fun _ => s)

/- [core::slice::index::Range::get_unchecked]: forward function -/
def core.slice.index.RangeUsize.get_unchecked
  {T : Type} :
  Range Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr (Slice T)) :=
  -- Don't know what the model should be - for now we always fail
  fun _ _ => fail .undef

/- [core::slice::index::Range::get_unchecked_mut]: forward function -/
def core.slice.index.RangeUsize.get_unchecked_mut
  {T : Type} :
  Range Usize → MutRawPtr (Slice T) → Result (MutRawPtr (Slice T)) :=
  -- Don't know what the model should be - for now we always fail
  fun _ _ => fail .undef

/- [core::slice::index::Range::index]: forward function -/
def core.slice.index.RangeUsize.index {T : Type} (r : Range Usize) (s : Slice T) : Result (Slice T) :=
  if r.start ≤ r.end_ ∧ r.end_ ≤ s.length then
    ok (⟨ s.val.slice r.start r.end_, by scalar_tac⟩)
  else fail .panic

/- [core::slice::index::Range::index_mut]: forward function -/
def core.slice.index.RangeUsize.index_mut {T : Type} (r : Range Usize) (s : Slice T) :
  Result (Slice T × (Slice T → Slice T)) :=
  if r.start ≤ r.end_ ∧ r.end_ ≤ s.length then
    ok (⟨ s.val.slice r.start r.end_, by scalar_tac⟩,
        fun s' =>
        if h: (List.replace_slice r.start r.end_ s.val s'.val).length ≤ Usize.max then
          ⟨ List.replace_slice r.start r.end_ s.val s'.val, by scalar_tac ⟩
        else s )
  else fail .panic

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
@[simp] abbrev core.slice.index.Usize.get
  {T : Type} (i : Usize) (s : Slice T) : Result (Option T) :=
  ok s[i]?

/- [core::slice::index::usize::get_mut]: forward function -/
@[simp] abbrev core.slice.index.Usize.get_mut
  {T : Type} (i : Usize) (s : Slice T) : Result (Option T × (Option T → Slice T)) :=
  ok (s[i]?, s.set_opt i)

/- [core::slice::index::usize::get_unchecked]: forward function -/
def core.slice.index.Usize.get_unchecked
  {T : Type} : Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr T) :=
  -- We don't have a model for now
  fun _ _ => fail .undef

/- [core::slice::index::usize::get_unchecked_mut]: forward function -/
def core.slice.index.Usize.get_unchecked_mut
  {T : Type} : Usize → MutRawPtr (Slice T) → Result (MutRawPtr T) :=
  -- We don't have a model for now
  fun _ _ => fail .undef

/- [core::slice::index::usize::index]: forward function -/
@[simp] abbrev core.slice.index.Usize.index {T : Type} (i : Usize) (s : Slice T) : Result T :=
  Slice.index_usize s i

/- [core::slice::index::usize::index_mut]: forward function -/
@[simp] abbrev core.slice.index.Usize.index_mut {T : Type}
  (i : Usize) (s : Slice T) : Result (T × (T → (Slice T))) :=
  Slice.index_mut_usize s i

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

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>> for core::ops::range::RangeFrom<usize>}::get] -/
def core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice.get {T : Type} (r : core.ops.range.RangeFrom Usize) (s : Slice T) : Result (Option (Slice T)) :=
  if  r.start ≤ s.length then
    ok (some (s.drop r.start))
  else ok none

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>> for core::ops::range::RangeFrom<usize>}::get_mut] -/
def core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice.get_mut
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

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>> for core::ops::range::RangeFrom<usize>}::get_unchecked] -/
def core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice.get_unchecked {T : Type} :
  core.ops.range.RangeFrom Usize → ConstRawPtr (Slice T) → Result (ConstRawPtr (Slice T)) :=
  -- We don't have a model for now
  fun _ _ => fail .undef

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>> for core::ops::range::RangeFrom<usize>}::get_unchecked_mut] -/
def core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice.get_unchecked_mut {T : Type} :
  core.ops.range.RangeFrom Usize → MutRawPtr (Slice T) → Result (MutRawPtr (Slice T)) :=
  -- We don't have a model for now
  fun _ _ => fail .undef

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>> for core::ops::range::RangeFrom<usize>}::index] -/
def core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice.index {T : Type}
  (r : core.ops.range.RangeFrom Usize) (s : Slice T) : Result (Slice T) :=
  if r.start.val ≤ s.length then
    ok (s.drop r.start)
  else fail .undef

/- [core::slice::index::{core::slice::index::SliceIndex<@Slice<T>> for core::ops::range::RangeFrom<usize>}::index_mut] -/
def core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice.index_mut {T : Type}
  (r : core.ops.range.RangeFrom Usize) (s : Slice T) : Result ((Slice T) × (Slice T → Slice T)) :=
  if r.start ≤ s.length then
    ok ( s.drop r.start, fun s' =>
         if h: s'.length + s.length - r.start.val ≤ Usize.max then
            ⟨ s'.val ++ s.val.drop r.start.val, by scalar_tac ⟩
          else s )
  else fail .panic

/- Trait implementation: [core::slice::index::private_slice_index::{core::slice::index::private_slice_index::Sealed for core::ops::range::RangeFrom<usize>}] -/
@[reducible]
def core.slice.index.private_slice_index.SealedcoreopsrangeRangeFromUsize :
  core.slice.index.private_slice_index.Sealed (core.ops.range.RangeFrom Usize)
  := {}

/- Trait implementation: [core::slice::index::{core::slice::index::SliceIndex<[T]> for core::ops::range::RangeFrom<usize>}] -/
@[reducible]
def core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice (T : Type) :
  core.slice.index.SliceIndex (core.ops.range.RangeFrom Usize) (Slice T) := {
  Output := Slice T
  sealedInst :=
    core.slice.index.private_slice_index.SealedcoreopsrangeRangeFromUsize
  get := core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice.get
  get_mut := core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice.get_mut
  get_unchecked :=
    core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice.get_unchecked
  get_unchecked_mut :=
    core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice.get_unchecked_mut
  index := core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice.index
  index_mut :=
    core.slice.index.SliceIndexcoreopsrangeRangeFromUsizeSlice.index_mut
}

end Std

end Aeneas
