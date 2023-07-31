import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd
import Mathlib.Tactic.Linarith
import Base.IList
import Base.Primitives.Scalar
import Base.Arith
import Base.Progress.Base

namespace Primitives

open Result Error

-------------
-- VECTORS --
-------------

def Vec (α : Type u) := { l : List α // l.length ≤ Usize.max }

-- TODO: do we really need it? It should be with Subtype by default
instance Vec.cast (a : Type u): Coe (Vec a) (List a)  where coe := λ v => v.val

instance (a : Type u) : Arith.HasIntProp (Vec a) where
  prop_ty := λ v => 0 ≤ v.val.len ∧ v.val.len ≤ Scalar.max ScalarTy.Usize
  prop := λ ⟨ _, l ⟩ => by simp[Scalar.max, List.len_eq_length, *]

@[simp]
abbrev Vec.length {α : Type u} (v : Vec α) : Int := v.val.len

@[simp]
abbrev Vec.v {α : Type u} (v : Vec α) : List α := v.val

example {a: Type u} (v : Vec a) : v.length ≤ Scalar.max ScalarTy.Usize := by
  scalar_tac

def Vec.new (α : Type u): Vec α := ⟨ [], by apply Scalar.cMax_suffices .Usize; simp ⟩

-- TODO: very annoying that the α is an explicit parameter
def Vec.len (α : Type u) (v : Vec α) : Usize :=
  Usize.ofIntCore v.val.len (by scalar_tac) (by scalar_tac)

@[simp]
theorem Vec.len_val {α : Type u} (v : Vec α) : (Vec.len α v).val = v.length :=
  by rfl

-- This shouldn't be used
def Vec.push_fwd (α : Type u) (_ : Vec α) (_ : α) : Unit := ()

-- This is actually the backward function
def Vec.push (α : Type u) (v : Vec α) (x : α) : Result (Vec α)
  :=
  let nlen := List.length v.val + 1
  if h : nlen ≤ U32.max || nlen ≤ Usize.max then
    have h : nlen ≤ Usize.max := by
      simp [Usize.max] at *
      have hm := Usize.refined_max.property
      cases h <;> cases hm <;> simp [U32.max, U64.max] at * <;> try linarith
    return ⟨ List.concat v.val x, by simp at *; assumption ⟩
  else
    fail maximumSizeExceeded

-- This shouldn't be used
def Vec.insert_fwd (α : Type u) (v: Vec α) (i: Usize) (_: α) : Result Unit :=
  if i.val < v.length then
    .ret ()
  else
    .fail arrayOutOfBounds

-- This is actually the backward function
def Vec.insert (α : Type u) (v: Vec α) (i: Usize) (x: α) : Result (Vec α) :=
  if i.val < v.length then
    .ret ⟨ v.val.update i.val x, by have := v.property; simp [*] ⟩
  else
    .fail arrayOutOfBounds

@[pspec]
theorem Vec.insert_spec {α : Type u} (v: Vec α) (i: Usize) (x: α)
  (hbound : i.val < v.length) :
  ∃ nv, v.insert α i x = ret nv ∧ nv.val = v.val.update i.val x := by
  simp [insert, *]

def Vec.index (α : Type u) (v: Vec α) (i: Usize) : Result α :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some x => ret x

/- In the theorems below: we don't always need the `∃ ..`, but we use one
   so that `progress` introduces an opaque variable and an equality. This
   helps control the context.
 -/

@[pspec]
theorem Vec.index_spec {α : Type u} [Inhabited α] (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index α i = ret x ∧ x = v.val.index i.val := by
  simp only [index]
  -- TODO: dependent rewrite
  have h := List.indexOpt_eq_index v.val i.val (by scalar_tac) (by simp [*])
  simp [*]

-- This shouldn't be used
def Vec.index_back (α : Type u) (v: Vec α) (i: Usize) (_: α) : Result Unit :=
  if i.val < List.length v.val then
    .ret ()
  else
    .fail arrayOutOfBounds

def Vec.index_mut (α : Type u) (v: Vec α) (i: Usize) : Result α :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some x => ret x

@[pspec]
theorem Vec.index_mut_spec {α : Type u} [Inhabited α] (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_mut α i = ret x ∧ x = v.val.index i.val := by
  simp only [index_mut]
  -- TODO: dependent rewrite
  have h := List.indexOpt_eq_index v.val i.val (by scalar_tac) (by simp [*])
  simp [*]

instance {α : Type u} (p : Vec α → Prop) : Arith.HasIntProp (Subtype p) where
  prop_ty := λ x => p x
  prop := λ x => x.property

def Vec.index_mut_back (α : Type u) (v: Vec α) (i: Usize) (x: α) : Result (Vec α) :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some _ =>
    .ret ⟨ v.val.update i.val x, by have := v.property; simp [*] ⟩

@[pspec]
theorem Vec.index_mut_back_spec {α : Type u} (v: Vec α) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.index_mut_back α i x = ret nv ∧
  nv.val = v.val.update i.val x
  := by
  simp only [index_mut_back]
  have h := List.indexOpt_bounds v.val i.val
  split
  . simp_all [length]; cases h <;> scalar_tac
  . simp_all

end Primitives
