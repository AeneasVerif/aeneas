import Hashmap.Funs

open Primitives
open Result

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
      have ⟨ b, hi ⟩ := insert_in_list_spec key value tl
      by
        exists b
        simp [insert_in_list, List.lookup]
        rw [insert_in_list_loop] -- TODO: Using simp leads to infinite recursion
        simp [h]
        simp [insert_in_list] at hi
        exact hi

-- Variation: use progress
@[pspec]
theorem insert_in_list_spec1 {α : Type} (key: Usize) (value: α) (ls: List α) :
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
        simp only [insert_in_list]
        rw [insert_in_list_loop]
        conv => rhs; ext; simp [*]
        progress keep as heq as ⟨ b hi ⟩
        simp only [insert_in_list] at heq
        exists b
        simp only [heq, hi]
        simp [*, List.lookup]

-- Variation: use tactics from the beginning
@[pspec]
theorem insert_in_list_spec2 {α : Type} (key: Usize) (value: α) (ls: List α) :
  ∃ b,
    insert_in_list α key value ls = ret b ∧
    (b ↔ (List.lookup ls.v key = none))
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
     conv => rhs; ext; left; simp [h] -- TODO: Simplify
     simp only [insert_in_list] at ih;
     -- TODO: give the possibility of using underscores
     progress as ⟨ b h ⟩
     simp [*]

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
         simp [*]
     else
       by
         simp [insert_in_list_back, List.lookup]
         rw [insert_in_list_loop_back]
         simp [h, List.lookup]
         have ⟨tl0 , _, _ ⟩ := insert_in_list_back_spec key value tl -- TODO: Use progress
         simp [insert_in_list_back] at *
         simp [List.lookup, *]
         simp (config := {contextual := true}) [*]
        
end HashMap

end hashmap
