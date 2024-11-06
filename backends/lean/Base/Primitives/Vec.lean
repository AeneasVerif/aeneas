/- Vectors -/
import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Base.Primitives.Scalar
import Base.Primitives.ArraySlice
import Base.Arith
import Base.Progress.Base

namespace Primitives

open Result Error

namespace alloc.vec

def Vec (α : Type u) := { l : List α // l.length ≤ Usize.max }

/-- We need this to coerce vectors to lists without marking `Vec` as reducible.
    Also not that we *do not* want to mark `Vec` as reducible: it triggers issues.
-/
instance (α : Type u) : CoeOut (Vec α) (List α) where
  coe := λ v => v.val

instance [BEq α] : BEq (Vec α) := SubtypeBEq _

instance [BEq α] [LawfulBEq α] : LawfulBEq (Vec α) := SubtypeLawfulBEq _

@[scalar_tac v]
theorem Vec.len_ineq {α : Type u} (v : Vec α) : 0 ≤ v.val.length ∧ v.val.length ≤ Scalar.max ScalarTy.Usize := by
  cases v; simp[Scalar.max, *]

-- TODO: move/remove?
@[scalar_tac v]
theorem Vec.subtype_property {α : Type u} {p : Vec α → Prop} (v : Subtype p) : p v.val := v.property

@[simp]
abbrev Vec.length {α : Type u} (v : Vec α) : Nat := v.val.length

@[simp]
abbrev Vec.v {α : Type u} (v : Vec α) : List α := v.val

example {a: Type u} (v : Vec a) : v.length ≤ Scalar.max ScalarTy.Usize := by
  scalar_tac

abbrev Vec.new (α : Type u): Vec α := ⟨ [], by apply Scalar.cMax_suffices .Usize; simp ⟩

instance (α : Type u) : Inhabited (Vec α) := by
  constructor
  apply Vec.new

@[simp]
abbrev Vec.len {α : Type u} (v : Vec α) : Usize :=
  Usize.ofIntCore v.val.length (by constructor <;> scalar_tac)

@[simp]
theorem Vec.len_val {α : Type u} (v : Vec α) : (Vec.len v).val = v.length :=
  by rfl

@[irreducible]
def Vec.push {α : Type u} (v : Vec α) (x : α) : Result (Vec α)
  :=
  let nlen := List.length v.val + 1
  if h : nlen ≤ U32.max || nlen ≤ Usize.max then
    have h : nlen ≤ Usize.max := by
      simp [Usize.max] at *
      have hm := Usize.refined_max.property
      cases h <;> cases hm <;> simp [U32.max, U64.max] at * <;> try omega
    ok ⟨ List.concat v.val x, by simp at *; assumption ⟩
  else
    fail maximumSizeExceeded

@[pspec]
theorem Vec.push_spec {α : Type u} (v : Vec α) (x : α) (h : v.val.length < Usize.max) :
  ∃ v1, v.push x = ok v1 ∧
  v1.val = v.val ++ [x] := by
  rw [push]; simp
  split <;> simp_all
  scalar_tac

def Vec.insert {α : Type u} (v: Vec α) (i: Usize) (x: α) : Result (Vec α) :=
  if i.val < v.length then
    ok ⟨ v.val.update i.toNat x, by have := v.property; simp [*] ⟩
  else
    fail arrayOutOfBounds

@[pspec]
theorem Vec.insert_spec {α : Type u} (v: Vec α) (i: Usize) (x: α)
  (hbound : i.val < v.length) :
  ∃ nv, v.insert i x = ok nv ∧ nv.val = v.val.update i.toNat x := by
  simp [insert, *]

def Vec.index_usize {α : Type u} (v: Vec α) (i: Usize) : Result α :=
  match v.val.indexOpt i.toNat with
  | none => fail .arrayOutOfBounds
  | some x => ok x

@[pspec]
theorem Vec.index_usize_spec {α : Type u} [Inhabited α] (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_usize i = ok x ∧ x = v.val.index i.toNat := by
  simp only [index_usize]
  -- TODO: dependent rewrite
  have h := List.indexOpt_eq_index v.val i.toNat (by scalar_tac)
  simp [*]

def Vec.update_usize {α : Type u} (v: Vec α) (i: Usize) (x: α) : Result (Vec α) :=
  match v.val.indexOpt i.toNat with
  | none => fail .arrayOutOfBounds
  | some _ =>
    ok ⟨ v.val.update i.toNat x, by have := v.property; simp [*] ⟩

@[pspec]
theorem Vec.update_usize_spec {α : Type u} (v: Vec α) (i: Usize) (x : α)
  (hbound : i.val < v.length) :
  ∃ nv, v.update_usize i x = ok nv ∧
  nv.val = v.val.update i.toNat x
  := by
  simp only [update_usize]
  have h := List.indexOpt_bounds v.val i.toNat
  split
  . simp_all [length]; scalar_tac
  . simp_all

def Vec.index_mut_usize {α : Type u} (v: Vec α) (i: Usize) :
  Result (α × (α → Result (Vec α))) :=
  match Vec.index_usize v i with
  | ok x =>
    ok (x, Vec.update_usize v i)
  | fail e => fail e
  | div => div

@[pspec]
theorem Vec.index_mut_usize_spec {α : Type u} [Inhabited α] (v: Vec α) (i: Usize)
  (hbound : i.val < v.length) :
  ∃ x, v.index_mut_usize i = ok (x, v.update_usize i) ∧
  x = v.val.index i.toNat
  := by
  simp only [index_mut_usize]
  have ⟨ x, h ⟩ := index_usize_spec v i hbound
  simp [h]

/- [alloc::vec::Vec::index]: forward function -/
def Vec.index {T I : Type} (inst : core.slice.index.SliceIndex I (Slice T))
  (self : Vec T) (i : I) : Result inst.Output :=
  sorry -- TODO

/- [alloc::vec::Vec::index_mut]: forward function -/
def Vec.index_mut {T I : Type} (inst : core.slice.index.SliceIndex I (Slice T))
  (self : Vec T) (i : I) :
  Result (inst.Output × (inst.Output → Result (Vec T))) :=
  sorry -- TODO

/- Trait implementation: [alloc::vec::Vec] -/
@[reducible]
def Vec.coreopsindexIndexInst {T I : Type}
  (inst : core.slice.index.SliceIndex I (Slice T)) :
  core.ops.index.Index (alloc.vec.Vec T) I := {
  Output := inst.Output
  index := Vec.index inst
}

/- Trait implementation: [alloc::vec::Vec] -/
@[reducible]
def Vec.coreopsindexIndexMutInst {T I : Type}
  (inst : core.slice.index.SliceIndex I (Slice T)) :
  core.ops.index.IndexMut (alloc.vec.Vec T) I := {
  indexInst := Vec.coreopsindexIndexInst inst
  index_mut := Vec.index_mut inst
}

@[simp]
theorem Vec.index_slice_index {α : Type} (v : Vec α) (i : Usize) :
  Vec.index (core.slice.index.SliceIndexUsizeSliceTInst α) v i =
  Vec.index_usize v i :=
  sorry

@[simp]
theorem Vec.index_mut_slice_index {α : Type} (v : Vec α) (i : Usize) :
  Vec.index_mut (core.slice.index.SliceIndexUsizeSliceTInst α) v i =
  index_mut_usize v i :=
  sorry

end alloc.vec

/-- [alloc::slice::{@Slice<T>}::to_vec] -/
def alloc.slice.Slice.to_vec
  {T : Type} (cloneInst : core.clone.Clone T) (s : Slice T) : Result (alloc.vec.Vec T) :=
  -- TODO: we need a monadic map
  sorry

/-- [core::slice::{@Slice<T>}::reverse] -/
def core.slice.Slice.reverse {T : Type} (s : Slice T) : Slice T :=
  ⟨ s.val.reverse, by sorry ⟩

def alloc.vec.Vec.with_capacity {T : Type} (_ : Usize) : alloc.vec.Vec T := Vec.new T

/- [alloc::vec::{(core::ops::deref::Deref for alloc::vec::Vec<T, A>)#9}::deref]:
   Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/vec/mod.rs', lines 2624:4-2624:27
   Name pattern: alloc::vec::{core::ops::deref::Deref<alloc::vec::Vec<@T, @A>>}::deref -/
def alloc.vec.DerefVec.deref {T : Type} (v : Vec T) : Slice T :=
  ⟨ v.val, v.property ⟩

@[reducible]
def core.ops.deref.DerefVec {T : Type} : core.ops.deref.Deref (alloc.vec.Vec T) := {
  Target := Slice T
  deref := fun v => ok (alloc.vec.DerefVec.deref v)
}

/- [alloc::vec::{(core::ops::deref::DerefMut for alloc::vec::Vec<T, A>)#10}::deref_mut]:
   Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/vec/mod.rs', lines 2632:4-2632:39
   Name pattern: alloc::vec::{core::ops::deref::DerefMut<alloc::vec::Vec<@T, @A>>}::deref_mut -/
def alloc.vec.DerefMutVec.deref_mut {T : Type} (v :  alloc.vec.Vec T) :
   Result ((Slice T) × (Slice T → Result (alloc.vec.Vec T))) :=
   ok (⟨ v.val, v.property ⟩, λ s => ok ⟨ s.val, s.property ⟩)

/- Trait implementation: [alloc::vec::{(core::ops::deref::DerefMut for alloc::vec::Vec<T, A>)#10}]
   Source: '/rustc/d59363ad0b6391b7fc5bbb02c9ccf9300eef3753/library/alloc/src/vec/mod.rs', lines 2630:0-2630:49
   Name pattern: core::ops::deref::DerefMut<alloc::vec::Vec<@Self, @>> -/
@[reducible]
def core.ops.deref.DerefMutVec {T : Type} :
  core.ops.deref.DerefMut (alloc.vec.Vec T) := {
  derefInst := core.ops.deref.DerefVec
  deref_mut := alloc.vec.DerefMutVec.deref_mut
}

def alloc.vec.Vec.resize {T : Type} (cloneInst : core.clone.Clone T)
  (v : alloc.vec.Vec T) (new_len : Usize) (value : T) : Result (alloc.vec.Vec T) := do
  if new_len.val < v.length then
    ok ⟨ v.val.resize new_len.toNat value, by scalar_tac ⟩
  else
    let value ← cloneInst.clone value
    ok ⟨ v.val.resize new_len.toNat value, by scalar_tac ⟩

@[pspec]
theorem alloc.vec.Vec.resize_spec {T} (cloneInst : core.clone.Clone T)
  (v : alloc.vec.Vec T) (new_len : Usize) (value : T)
  (hClone : cloneInst.clone value = ok value) :
  ∃ nv, alloc.vec.Vec.resize cloneInst v new_len value = ok nv ∧
    nv.val = v.val.resize new_len.toNat value := by
  rw [resize]
  split
  . simp
  . simp [*]

end Primitives
