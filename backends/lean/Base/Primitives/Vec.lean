/- Vectors -/
import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd
import Mathlib.Tactic.Linarith
import Base.IList
import Base.Primitives.Scalar
import Base.Primitives.ArraySlice
import Base.Arith
import Base.Progress.Base

namespace Primitives

open Result Error

namespace alloc.vec

def Vec (α : Type u) := { l : List α // l.length ≤ Usize.max }

instance (a : Type u) : Arith.HasIntProp (Vec a) where
  prop_ty := λ v => 0 ≤ v.val.len ∧ v.val.len ≤ Scalar.max ScalarTy.Usize
  prop := λ ⟨ _, l ⟩ => by simp[Scalar.max, List.len_eq_length, *]

instance {α : Type u} (p : Vec α → Prop) : Arith.HasIntProp (Subtype p) where
  prop_ty := λ x => p x
  prop := λ x => x.property

@[simp]
abbrev Vec.length {α : Type u} (v : Vec α) : Int := v.val.len

@[simp]
abbrev Vec.v {α : Type u} (v : Vec α) : List α := v.val

example {a: Type u} (v : Vec a) : v.length ≤ Scalar.max ScalarTy.Usize := by
  scalar_tac

def Vec.new (α : Type u): Vec α := ⟨ [], by apply Scalar.cMax_suffices .Usize; simp; decide ⟩

instance (α : Type u) : Inhabited (Vec α) := by
  constructor
  apply Vec.new

-- TODO: very annoying that the α is an explicit parameter
def Vec.len (α : Type u) (v : Vec α) : Usize :=
  Usize.ofIntCore v.val.len (by constructor <;> scalar_tac)

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

def Vec.index_usize {α : Type u} (v: Vec α) (i: Usize) : Result α :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some x => ret x

/- In the theorems below: we don't always need the `∃ ..`, but we use one
   so that `progress` introduces an opaque variable and an equality. This
   helps control the context.
 -/

@[pspec]
theorem Vec.index_usize_spec {α : Type u} [Inhabited α] (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_usize i = ret x ∧ x = v.val.index i.val := by
  simp only [index_usize]
  -- TODO: dependent rewrite
  have h := List.indexOpt_eq_index v.val i.val (by scalar_tac) (by simp [*])
  simp [*]

def Vec.update_usize {α : Type u} (v: Vec α) (i: Usize) (x: α) : Result (Vec α) :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some _ =>
    .ret ⟨ v.val.update i.val x, by have := v.property; simp [*] ⟩

@[pspec]
theorem Vec.update_usize_spec {α : Type u} (v: Vec α) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.update_usize i x = ret nv ∧
  nv.val = v.val.update i.val x
  := by
  simp only [update_usize]
  have h := List.indexOpt_bounds v.val i.val
  split
  . simp_all [length]; cases h <;> scalar_tac
  . simp_all

def Vec.index_mut_usize {α : Type u} (v: Vec α) (i: Usize) :
  Result (α × (α → Result (Vec α))) :=
  match Vec.index_usize v i with
  | ret x =>
    ret (x, Vec.update_usize v i)
  | fail e => fail e
  | div => div

@[pspec]
theorem Vec.index_mut_usize_spec {α : Type u} [Inhabited α] (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x back, v.index_mut_usize i = ret (x, back) ∧
  x = v.val.index i.val ∧
  -- Backward function
  back = v.update_usize i
  := by
  simp only [index_mut_usize]
  have ⟨ x, h ⟩ := index_usize_spec v i hbound
  simp [h]

/- [alloc::vec::Vec::index]: forward function -/
def Vec.index (T I : Type) (inst : core.slice.index.SliceIndex I (Slice T))
  (self : Vec T) (i : I) : Result inst.Output :=
  sorry -- TODO

/- [alloc::vec::Vec::index_mut]: forward function -/
def Vec.index_mut (T I : Type) (inst : core.slice.index.SliceIndex I (Slice T))
  (self : Vec T) (i : I) :
  Result (inst.Output × (inst.Output → Result (Vec T))) :=
  sorry -- TODO

/- Trait implementation: [alloc::vec::Vec] -/
def Vec.coreopsindexIndexInst (T I : Type)
  (inst : core.slice.index.SliceIndex I (Slice T)) :
  core.ops.index.Index (alloc.vec.Vec T) I := {
  Output := inst.Output
  index := Vec.index T I inst
}

/- Trait implementation: [alloc::vec::Vec] -/
def Vec.coreopsindexIndexMutInst (T I : Type)
  (inst : core.slice.index.SliceIndex I (Slice T)) :
  core.ops.index.IndexMut (alloc.vec.Vec T) I := {
  indexInst := Vec.coreopsindexIndexInst T I inst
  index_mut := Vec.index_mut T I inst
}

@[simp]
theorem Vec.index_slice_index {α : Type} (v : Vec α) (i : Usize) :
  Vec.index α Usize (core.slice.index.SliceIndexUsizeSliceTInst α) v i =
  Vec.index_usize v i :=
  sorry

@[simp]
theorem Vec.index_mut_slice_index {α : Type} (v : Vec α) (i : Usize) :
  Vec.index_mut α Usize (core.slice.index.SliceIndexUsizeSliceTInst α) v i =
  index_mut_usize v i :=
  sorry

end alloc.vec

end Primitives
