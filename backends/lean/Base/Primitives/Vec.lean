import Lean
import Lean.Meta.Tactic.Simp
import Init.Data.List.Basic
import Mathlib.Tactic.RunCmd
import Mathlib.Tactic.Linarith
import Base.IList
import Base.Primitives.Scalar
import Base.Arith

namespace Primitives

open Result Error

-------------
-- VECTORS --
-------------

def Vec (α : Type u) := { l : List α // List.length l ≤ Usize.max }

-- TODO: do we really need it? It should be with Subtype by default
instance Vec.cast (a : Type): Coe (Vec a) (List a)  where coe := λ v => v.val

instance (a : Type) : Arith.HasIntProp (Vec a) where
  prop_ty := λ v => v.val.length ≤ Scalar.max ScalarTy.Usize
  prop := λ ⟨ _, l ⟩ => l

example {a: Type} (v : Vec a) : v.val.length ≤ Scalar.max ScalarTy.Usize := by
  intro_has_int_prop_instances
  simp_all [Scalar.max, Scalar.min]

example {a: Type} (v : Vec a) : v.val.length ≤ Scalar.max ScalarTy.Usize := by
  scalar_tac

def Vec.new (α : Type u): Vec α := ⟨ [], by apply Scalar.cMax_suffices .Usize; simp ⟩

def Vec.len (α : Type u) (v : Vec α) : Usize :=
  let ⟨ v, l ⟩ := v
  Usize.ofIntCore (List.length v) (by simp [Scalar.min, Usize.min]) l

def Vec.length {α : Type u} (v : Vec α) : Int := v.val.len

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
def Vec.insert_fwd (α : Type u) (v: Vec α) (i: Usize) (_: α): Result Unit :=
  if i.val < List.length v.val then
    .ret ()
  else
    .fail arrayOutOfBounds

-- This is actually the backward function
def Vec.insert (α : Type u) (v: Vec α) (i: Usize) (x: α): Result (Vec α) :=
  if i.val < List.length v.val then
    -- TODO: maybe we should redefine a list library which uses integers
    -- (instead of natural numbers)
    .ret ⟨ v.val.update i.val x, by have := v.property; simp [*] ⟩
  else
    .fail arrayOutOfBounds

-- TODO: remove
def Vec.index_to_fin {α : Type u} {v: Vec α} {i: Usize} (h : i.val < List.length v.val) :
  Fin (List.length v.val) :=
  let j := i.val.toNat
  let h: j < List.length v.val := by
    have heq := @Int.toNat_lt (List.length v.val) i.val i.hmin
    apply heq.mpr
    assumption
  ⟨j, h⟩

def Vec.index (α : Type u) (v: Vec α) (i: Usize): Result α :=
  match v.val.indexOpt i.val with
  | none => fail .arrayOutOfBounds
  | some x => ret x

-- This shouldn't be used
def Vec.index_back (α : Type u) (v: Vec α) (i: Usize) (_: α): Result Unit :=
  if i.val < List.length v.val then
    .ret ()
  else
    .fail arrayOutOfBounds

def Vec.index_mut (α : Type u) (v: Vec α) (i: Usize): Result α :=
  if h: i.val < List.length v.val then
    let i := Vec.index_to_fin h
    .ret (List.get v.val i)
  else
    .fail arrayOutOfBounds

def Vec.index_mut_back (α : Type u) (v: Vec α) (i: Usize) (x: α): Result (Vec α) :=
  if h: i.val < List.length v.val then
    let i := Vec.index_to_fin h
    .ret ⟨ List.set v.val i x, by
      have h: List.length v.val ≤ Usize.max := v.property
      simp [*] at *
    ⟩
  else
    .fail arrayOutOfBounds

end Primitives
