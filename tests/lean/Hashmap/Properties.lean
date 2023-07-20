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

abbrev Core.List := _root_.List

theorem insert_in_list_spec0 {α : Type} (key: Usize) (value: α) (ls: List α) :
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
      have ⟨ b, hi ⟩ := insert_in_list_spec0 key value tl
      by
        exists b
        simp [insert_in_list, List.lookup]
        rw [insert_in_list_loop] -- TODO: Using simp leads to infinite recursion
        simp [h]
        simp [insert_in_list] at hi
        exact hi

-- Variation: use progress
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

theorem insert_in_list_back_spec {α : Type} (key: Usize) (value: α) (l0: List α) :
  ∃ l1,
    insert_in_list_back α key value l0 = ret l1 ∧
    -- We update the binding
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
         progress keep as heq as ⟨ tl hp1 hp2 ⟩
         simp [insert_in_list_back] at heq
         simp (config := {contextual := true}) [*, List.lookup]

def distinct_keys (ls : Core.List (Usize × α)) := ls.pairwise_rel (λ x y => x.fst ≠ y.fst)

def hash_mod_key (k : Usize) (l : Int) : Int :=
  match hash_key k with
  | .ret k => k.val % l
  | _ => 0

def slot_s_inv_hash (l i : Int) (ls : Core.List (Usize × α)) : Prop :=
  ls.allP (λ (k, _) => hash_mod_key k l = i)

@[simp]
def slot_s_inv (l i : Int) (ls : Core.List (Usize × α)) : Prop :=
  distinct_keys ls ∧
  slot_s_inv_hash l i ls

def slot_t_inv (l i : Int) (s : List α) : Prop := slot_s_inv l i s.v

@[pspec]
theorem insert_in_list_back_spec1 {α : Type} (l : Int) (key: Usize) (value: α) (l0: List α)
  (hinv : slot_s_inv_hash l (hash_mod_key key l) l0.v) :
  ∃ l1,
    insert_in_list_back α key value l0 = ret l1 ∧
    -- We update the binding
    List.lookup l1.v key = value ∧
    (∀ k, k ≠ key → List.lookup l1.v k = List.lookup l0.v k) ∧
    -- We preserve part of the key invariant
    slot_s_inv_hash l (hash_mod_key key l) l1.v
  := match l0 with
  | .Nil => by
    simp [insert_in_list_back, insert_in_list_loop_back, List.lookup, List.v, slot_s_inv_hash]
    tauto
  | .Cons k v tl0 =>
     if h: k = key then
       by
         simp [insert_in_list_back, List.lookup]
         rw [insert_in_list_loop_back]
         simp [h, List.lookup]
         constructor
         . intros; simp [*]
         . simp [List.v, slot_s_inv_hash] at *
           simp [*]
     else
       by
         simp [insert_in_list_back, List.lookup]
         rw [insert_in_list_loop_back]
         simp [h, List.lookup]
         have : slot_s_inv_hash l (hash_mod_key key l) (List.v tl0) := by
           simp_all [List.v, slot_s_inv_hash]
         progress keep as heq as ⟨ tl1 hp1 hp2 hp3 ⟩
         simp only [insert_in_list_back] at heq
         have : slot_s_inv_hash l (hash_mod_key key l) (List.v (List.Cons k v tl1)) := by
           simp [List.v, slot_s_inv_hash] at *
           simp [*]
         simp (config := {contextual := true}) [*, List.lookup]


end HashMap

end hashmap
