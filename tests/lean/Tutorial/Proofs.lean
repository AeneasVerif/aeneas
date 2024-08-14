import Base
open Primitives Result

namespace Primitives

end Primitives

namespace Tutorial

def times4 (x : U32) : Result U32 := do
  let x1 ← x + x
  x1 + x1

def times16 (x : U32) : Result U32 := do
  let x1 ← times4 x
  times4 x1

#check U32.add_spec

-- Without progress
theorem times4_spec (x : U32) (h : 4 * x.val ≤ U32.max) :
  times4 x = ok (4 * x)#u32 := by
  rw [times4]
  have ⟨ x1, hEq1, hPost1 ⟩ := @U32.add_spec x x (by scalar_tac)
  simp [hEq1]
  have ⟨ x2, hEq2, hPost2 ⟩ := @U32.add_spec x1 x1 (by scalar_tac)
  simp [hEq2]
  scalar_tac

-- With progress
@[pspec]
theorem times4_spec1 (x : U32) (h : 4 * x.val ≤ U32.max) :
  times4 x = ok (4 * x)#u32 := by
  rw [times4]
  progress
  progress
  scalar_tac

theorem times16_spec (x : U32) (h : 16 * x.val ≤ U32.max) :
  times16 x = ok (16 * x)#u32 := by
  rw [times16]
  progress
  progress
  scalar_tac

/- [demo::incr]:
   Source: 'tests/src/demo.rs', lines 23:0-23:31 -/
def incr (x : U32) : Result U32 :=
  x + 1#u32

/- [demo::use_incr]:
   Source: 'tests/src/demo.rs', lines 27:0-27:17 -/
def use_incr : Result Unit :=
  do
  let x ← incr 0#u32
  let x1 ← incr x
  let _ ← incr x1
  Result.ok ()

divergent def i32_id (n : I32) : Result I32 :=
  if n = 0#i32 then ok 0#i32
  else do
    let n1 ← n - 1#i32
    let n2 ← i32_id n1
    n2 + 1#i32

theorem i32_id_spec (n : I32) (h : 0 ≤ n.val) :
  i32_id n = ok n := by
  rw [i32_id]
  split
  . simp [*]
  . progress as ⟨ n1 ⟩
    progress
    progress as ⟨ n2 ⟩
    scalar_tac
termination_by n.toNat
decreasing_by simp_wf; scalar_tac

mutual

divergent def even (n : U32) : Result Bool :=
  if n = 0#u32 then ok true
  else do
    let n ← n - 1#u32
    odd n

divergent def odd (n : U32) : Result Bool :=
  if n = 0#u32 then ok false
  else do
    let n ← n - 1#u32
    even n

end

mutual

theorem even_spec (n : U32) :
  ∃ b, even n = ok b ∧ (b ↔ Even n.val) := by
  rw [even]
  split
  . simp [*]
  . progress as ⟨ n' ⟩
    progress as ⟨ b ⟩
    simp [*]
    simp [Int.even_sub]
termination_by n.toNat
decreasing_by simp_wf; scalar_tac

theorem odd_spec (n : U32) :
  ∃ b, odd n = ok b ∧ (b ↔ Odd n.val) := by
  rw [odd]
  split
  . simp [*]
  . progress as ⟨ n' ⟩
    progress as ⟨ b ⟩
    simp [*]
    simp [Int.even_sub]
termination_by n.toNat
decreasing_by simp_wf; scalar_tac

end

/- [demo::CList]
   Source: 'tests/src/demo.rs', lines 36:0-36:17 -/
inductive CList (T : Type) :=
| CCons : T → CList T → CList T
| CNil : CList T

/- [demo::list_nth]:
   Source: 'tests/src/demo.rs', lines 41:0-41:56 -/
divergent def list_nth (T : Type) (l : CList T) (i : U32) : Result T :=
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then Result.ok x
    else do
         let i1 ← i - 1#u32
         list_nth T tl i1
  | CList.CNil => Result.fail .panic

-- TODO: list_nth1 (with a loop)

/- [demo::list_tail]:
   Source: 'tests/src/demo.rs', lines 90:0-90:64 -/
divergent def list_tail
  (T : Type) (l : CList T) :
  Result ((CList T) × (CList T → Result (CList T)))
  :=
  match l with
  | CList.CCons t tl =>
    do
    let (c, list_tail_back) ← list_tail T tl
    let back :=
      fun ret =>
        do
        let tl1 ← list_tail_back ret
        Result.ok (CList.CCons t tl1)
    Result.ok (c, back)
  | CList.CNil => Result.ok (CList.CNil, Result.ok)

open CList

@[simp] def CList.to_list {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.to_list

theorem list_nth_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
  (h : i.val < l.to_list.length) :
  ∃ x, list_nth T l i = ok x ∧
  x = l.to_list.index ↑i
  := by
  rw [list_nth]
  match l with
  | CNil =>
    simp_all; scalar_tac
  | CCons hd tl =>
    simp_all
    if hi: i = 0#u32 then
      simp_all
    else
      simp_all
      progress as ⟨ i1 ⟩
      progress as ⟨ x ⟩
      simp_all

theorem list_tail_spec {T : Type} [Inhabited T] (l : CList T) :
  ∃ back, list_tail T l = ok (CList.CNil, back) ∧
  ∀ tl', ∃ l', back tl' = ok l' ∧ l'.to_list = l.to_list ++ tl'.to_list := by
  rw [list_tail]
  match l with
  | CNil =>
    simp_all
  | CCons hd tl =>
    simp_all
    progress as ⟨ back ⟩
    simp
    -- Proving the backward function
    intro tl'
    progress
    simp_all

/- Trait declaration: [demo::Counter]
   Source: 'tests/src/demo.rs', lines 99:0-99:17 -/
structure Counter (Self : Type) where
  incr : Self → Result (Usize × Self)

/- [demo::{demo::Counter for usize}::incr]:
   Source: 'tests/src/demo.rs', lines 104:4-104:31 -/
def CounterUsize.incr (self : Usize) : Result (Usize × Usize) :=
  do
  let self1 ← self + 1#usize
  Result.ok (self, self1)

/- Trait implementation: [demo::{demo::Counter for usize}]
   Source: 'tests/src/demo.rs', lines 103:0-103:22 -/
def CounterUsize : Counter Usize := {
  incr := CounterUsize.incr
}

/- [demo::use_counter]:
   Source: 'tests/src/demo.rs', lines 111:0-111:59 -/
def use_counter
  (T : Type) (CounterInst : Counter T) (cnt : T) : Result (Usize × T) :=
  CounterInst.incr cnt

end Tutorial
