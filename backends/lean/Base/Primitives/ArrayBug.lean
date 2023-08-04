/- Arrays/slices -/
import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd
import Mathlib.Tactic.Linarith
import Base.IList
import Base.Primitives.Scalar
import Base.Primitives.Range
import Base.Arith
import Base.Progress.Base

namespace Primitives

open Result Error

abbrev Array (α : Type u) (n : Usize) := { l : List α // l.length = n.val }

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

def Array.mk (α : Type u) (n : Usize) (init : List α) (hl : init.len = n.val := by decide) :
  Array α n := ⟨ init, by simp [← List.len_eq_length]; apply hl ⟩

example : Array Int (Usize.ofInt 2) := Array.mk Int (Usize.ofInt 2) [0, 1]

-- Remark: not used yet, but could be used if explicit calls to Len are used in Rust
-- TODO: very annoying that the α and the n are explicit parameters
def Array.len (α : Type u) (n : Usize) (v : Array α n) : Usize :=
  Usize.ofIntCore v.val.len (by scalar_tac) (by scalar_tac)

@[simp]
theorem Array.len_val {α : Type u} {n : Usize} (v : Array α n) : (Array.len α n v).val = v.length :=
  by rfl

abbrev Array.index {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i : Int) : α :=
  v.val.index i

@[simp]
theorem Array.index_simp {α : Type u} {n : Usize} [Inhabited α]
  (val : List α) (property : (fun l => l.length = n.val) val) (i: Int) :
  Array.index ⟨ val, property ⟩ i = val.index i := by simp

abbrev Array.slice {α : Type u} {n : Usize} [Inhabited α] (v : Array α n) (i j : Int) : List α :=
  v.val.slice i j

@[simp]
theorem Array.slice_simp {α : Type u} {n : Usize} [Inhabited α]
  (val : List α) (property : (fun l => l.length = n.val) val) (i j : Int) :
  Array.slice ⟨ val, property ⟩ i j = val.slice i j := by simp

def Slice (α : Type u) := { l : List α // True }

@[simp]
abbrev Slice.length {α : Type u} (v : Slice α) : Int := v.val.len

@[simp]
abbrev Slice.v {α : Type u} (v : Slice α) : List α := v.val

abbrev Slice.index {α : Type u} [Inhabited α] (v: Slice α) (i: Int) : α :=
  v.val.index i

@[simp]
theorem Slice.index_simp {α : Type u} [Inhabited α]
  (val : List α) (property : (fun l => True) val) (i: Int) :
  Slice.index ⟨ val, property ⟩ i = val.index i := by simp [index]

def Slice.mut_subslice_back (α : Type u) (s : Slice α) (r : Range Usize) (ss : Slice α) : Result (Slice α) :=
  -- TODO: not completely sure here
  if r.start.val < r.end_.val ∧ r.end_.val ≤ s.length ∧ ss.val.len = r.end_.val - r.start.val then
    let s_beg := s.val.itake r.start.val
    let s_end := s.val.idrop r.end_.val
    let ns := s_beg.append (ss.val.append s_end)
    ret ⟨ ns, by trivial ⟩
  else
    fail panic

theorem Slice.mut_subslice_back_spec {α : Type u} [Inhabited α] (a : Slice α) (r : Range Usize) (ss : Slice α)
  (_ : r.start.val < r.end_.val)
  (_ : r.end_.val ≤ a.length)
  (_ : ss.length = r.end_.val - r.start.val)
  :
  ∃ (na : Slice α), mut_subslice_back α a r ss = ret na ∧
  (∀ i, 0 ≤ i → i < r.start.val → na.index i = a.index i)
  := by
  simp [mut_subslice_back]
  simp [*]

end Primitives
