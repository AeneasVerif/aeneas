import Hashmap.Funs

open Primitives
open Result

namespace List

theorem index_ne
  {α : Type u} [Inhabited α] (l: List α) (i: ℤ) (j: ℤ) (x: α) :
   0 ≤ i → i < l.len → 0 ≤ j → j < l.len → j ≠ i →
    (l.update i x).index j = l.index j
  :=
  λ _ _ _ _ _ => match l with
  | [] => by simp at *
  | hd :: tl =>
    if h: i = 0 then
      have : j ≠ 0 := by scalar_tac
      by simp [*]
    else if h : j = 0 then
      have : i ≠ 0 := by scalar_tac
      by simp [*]
    else
      by
        simp [*]
        simp at *
        apply index_ne <;> scalar_tac

theorem index_eq
  {α : Type u} [Inhabited α] (l: List α) (i: ℤ) (x: α) :
   0 ≤ i → i < l.len →
    (l.update i x).index i = x
  :=
  fun _ _ => match l with
  | [] => by simp at *; exfalso; scalar_tac -- TODO: exfalso needed. Son FIXME
  | hd :: tl =>
    if h: i = 0 then
      by
        simp [*]
    else
      by
        simp [*]
        simp at *
        apply index_eq <;> scalar_tac

def allP {α : Type u} (l : List α) (p: α → Prop) : Prop :=
  foldr (fun a r => p a ∧ r) True l

@[simp]
theorem allP_nil {α : Type u} (p: α → Prop) : allP [] p :=
  by simp [allP, foldr]

@[simp]
theorem allP_cons {α : Type u} (hd: α) (tl : List α) (p: α → Prop) :
  allP (hd :: tl) p ↔ p hd ∧ allP tl p
  := by simp [allP, foldr]

def pairwise_rel 
  {α : Type u} (rel : α → α → Prop) (l: List α) : Prop
  := match l with
  | [] => True
  | hd :: tl => allP tl (rel hd) ∧ pairwise_rel rel tl

@[simp]
theorem pairwise_rel_nil {α : Type u} (rel : α → α → Prop) :
  pairwise_rel rel []
  := by simp [pairwise_rel]

@[simp]
theorem pairwise_rel_cons {α : Type u} (rel : α → α → Prop) (hd: α) (tl: List α) :
  pairwise_rel rel (hd :: tl) ↔ allP tl (rel hd) ∧ pairwise_rel rel tl
  := by simp [pairwise_rel]

end List

namespace hashmap

namespace List

def v {α : Type} (ls: List α) : _root_.List (Usize × α) :=
  match ls with
  | Nil => []
  | Cons k x tl => (k, x) :: v tl

def lookup {α : Type} (ls: _root_.List (Usize × α)) (key: Usize) : Option α :=
  match ls with
  | [] => none
  | (k, x) :: tl => if k = key then some x else lookup tl key

end List

namespace HashMap

@[pspec]
theorem insert_in_list_spec {α : Type} (key: Usize) (value: α) (ls: List α) :
  ∃ b,
    insert_in_list α key value ls = ret b ∧
    (b ↔ List.lookup ls.v key = none)
  := match ls with
  | .Nil => by simp [insert_in_list, insert_in_list_loop, List.lookup]
  | .Cons k v tl =>
    if h: k = key then -- TODO: The order of k/key matters
      by
        simp [insert_in_list, List.lookup]
        rw [insert_in_list_loop]
        simp [h]
    else
      by
        have ⟨ b, hi ⟩ := insert_in_list_spec key value tl
        exists b
        simp [insert_in_list, List.lookup]
        rw [insert_in_list_loop] -- TODO: Using it in simp leads to infinite recursion
        simp [h]
        simp [insert_in_list] at hi
        exact hi
   
/--
@[pspec]
theorem insert_in_list_spec2 {α : Type} (key: Usize) (value: α) (ls: List α) :
  ∃ b,
    insert_in_list α key value ls = ret b ∧
    (b = (List.lookup ls.v key = none))
  := by
  induction ls
  case Nil => simp [insert_in_list, insert_in_list_loop, List.lookup]
  case Cons k v tl ih =>
    simp only [insert_in_list, List.lookup]
    rw [insert_in_list_loop]
    simp only
    if h: k = key then
     simp [h]
    else
     conv =>
       rhs; ext; arg 1; simp [h] -- TODO: Simplify
     simp [insert_in_list] at ih;
     progress -- TODO: Does not work
--/
    
@[pspec]
theorem insert_in_list_back_spec {α : Type} (key: Usize) (value: α) (l0: List α) :
  ∃ l1,
    insert_in_list_back α key value l0 = ret l1 ∧
    List.lookup l1.v key = value ∧
    (∀ k, k ≠ key → List.lookup l1.v k = List.lookup l0.v k)
  := match l0 with
  | .Nil => by simp [insert_in_list_back, insert_in_list_loop_back, List.lookup]; tauto
  | .Cons k v tl =>
     if h: k = key then
       by
         simp [insert_in_list_back, List.lookup]
         rw [insert_in_list_loop_back]
         simp [h, List.lookup]
         intro k1 h1
         have h2 : ¬(key = k1) := by tauto -- TODO: Why is the order of args in eq swapped
         simp [h2]
     else
       by
         simp [insert_in_list_back, List.lookup]
         rw [insert_in_list_loop_back]
         simp [h, List.lookup]
         have ⟨tl0 , _, _ ⟩ := insert_in_list_back_spec key value tl -- TODO: Use progress
         simp [insert_in_list_back] at *
         simp [*]
         have : ¬ (key = k) := by tauto
         simp [List.lookup, *]
         simp (config := {contextual := true}) [*]
        
end HashMap
-- def distinct_keys {α : Type u}

end hashmap
