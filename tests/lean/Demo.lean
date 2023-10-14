import Base

open Primitives
open Result

namespace Demo

def mul2_add1 (x : U32) : Result U32 := do
  let x1 ← x + x
  let x2 ← x1 + 1#u32
  ret x2

#check U32.add_spec

@[pspec] -- registers the theorem
theorem mul2_add1_spec (x : U32) (h : 2 * ↑x + 1 ≤ U32.max)
  : ∃ y, mul2_add1 x = ret y ∧
  ↑y = 2 * ↑x + (1 : Int)
  := by
  rw [mul2_add1]
  progress as ⟨ x1 ⟩
  progress as ⟨ x2 ⟩
  scalar_tac

def use_mul2_add1 (x : U32) (y : U32) : Result U32 := do
  let x1 ← mul2_add1 x
  x1 + y

@[pspec]
theorem use_mul2_add1_spec (x : U32) (y : U32) (h : 2 * ↑x + 1 + ↑y ≤ U32.max) :
  ∃ z, use_mul2_add1 x y = ret z ∧
  ↑z = 2 * ↑x + (1 : Int) + ↑y := by
  rw [use_mul2_add1]
  progress as ⟨ x1 ⟩
  progress as ⟨ z ⟩
  scalar_tac

/-#===========================================================================#
  #
  #     Recursion
  #
  #===========================================================================#-/

/- We can have a look at more complex examples, for example recursive functions. -/

/- A custom list type.

   Original Rust code:
   ```
   pub enum CList<T> {
    CCons(T, Box<CList<T>>),
    CNil,
   }
   ```
-/
inductive CList (T : Type) :=
| CCons : T → CList T → CList T
| CNil : CList T

-- Open the [CList] namespace, so that we can write [CCons] instead of [CList.CCons]
open CList

/- A function accessing the ith element of a list.

   Original Rust code:
   ```
   pub fn list_nth<'a, T>(l: &'a CList<T>, i: u32) -> &'a T {
      match l {
          List::CCons(x, tl) => {
              if i == 0 {
                  return x;
              } else {
                  return list_nth(tl, i - 1);
              }
          }
          List::CNil => {
              panic!()
          }
      }
   }
   ```
 -/
divergent def list_nth (T : Type) (l : CList T) (i : U32) : Result T :=
  match l with
  | CCons x tl =>
    if i = 0#u32
    then ret x
    else do
      let i1 ← i - 1#u32
      list_nth T tl i1
  | CNil => fail Error.panic

@[simp] def CList.to_list {α : Type} (x : CList α) : List α :=
  match x with
  | CNil => []
  | CCons hd tl => hd :: tl.to_list

theorem list_nth_spec {T : Type} [Inhabited T] (l : CList T) (i : U32)
  -- Precondition: the index is in bounds
  (h : ↑i < l.to_list.len)
  -- Postcondition
  : ∃ x, list_nth T l i = ret x ∧
  -- [x] is the ith element of [l] after conversion to [List]
  x = l.to_list.index ↑i
  := by
  rw [list_nth]
  match l with
  | CNil =>
    scalar_tac
  | CCons hd tl =>
    simp only []
    if hi: i = 0#u32 then
      simp [hi]
    else
      simp [hi]
      progress as ⟨ i1 ⟩
      progress as ⟨ l1 ⟩
      have : i.val ≠ 0 := by scalar_tac
      simp_all

divergent def i32_id (x : I32) : Result I32 :=
  if x = 0#i32 then ret 0#i32
  else do
    let x1 ← x - 1#i32
    let x2 ← i32_id x1
    x2 + 1#i32

theorem i32_id_spec (x : I32) (h : 0 ≤ x.val) :
  ∃ y, i32_id x = ret y ∧ x.val = y.val := by
  rw [i32_id]
  if hx : x = 0#i32 then
    simp_all
  else
    simp [hx]
    -- x - 1
    progress as ⟨ x1 ⟩
    -- Recursive call
    progress as ⟨ x2 ⟩
    -- x2 + 1
    progress
    -- Postcondition
    simp; scalar_tac
termination_by i32_id_spec x _ => x.val.toNat
decreasing_by
  simp_wf
  have : 1 ≤ x.val := by scalar_tac
  simp [Int.toNat_sub_of_le, *]

end Demo
