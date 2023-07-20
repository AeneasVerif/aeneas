import Hashmap.Funs

open Primitives
open Result

namespace List

-- TODO: we don't want to use the original List.lookup because it uses BEq
-- TODO: rewrite rule: match x == y with ... -> if x = y then ... else ... ?
@[simp]
def lookup' {α : Type} (ls: _root_.List (Usize × α)) (key: Usize) : Option α :=
  match ls with
  | [] => none
  | (k, x) :: tl => if k = key then some x else lookup' tl key

end List

namespace hashmap

namespace List

def v {α : Type} (ls: List α) : _root_.List (Usize × α) :=
  match ls with
  | Nil => []
  | Cons k x tl => (k, x) :: v tl

@[simp] theorem v_nil (α : Type) : (Nil : List α).v = [] := by rfl
@[simp] theorem v_cons {α : Type} k x (tl: List α) : (Cons k x tl).v = (k, x) :: v tl := by rfl

@[simp]
abbrev lookup {α : Type} (ls: List α) (key: Usize) : Option α :=
  ls.v.lookup' key

@[simp]
abbrev len {α : Type} (ls : List α) : Int := ls.v.len

end List

namespace HashMap

abbrev Core.List := _root_.List

namespace List

end List

-- TODO: move
@[simp] theorem neq_imp_nbeq [BEq α] [LawfulBEq α] (x y : α) (heq : ¬ x = y) : ¬ x == y := by simp [*]
@[simp] theorem neq_imp_nbeq_rev [BEq α] [LawfulBEq α] (x y : α) (heq : ¬ x = y) : ¬ y == x := by simp [*]

-- TODO: move
theorem match_lawful_beq [BEq α] [LawfulBEq α] [DecidableEq α] (x y : α) :
  (x == y) = (if x = y then true else false) := by
  split <;> simp_all

theorem insert_in_list_spec0 {α : Type} (key: Usize) (value: α) (ls: List α) :
  ∃ b,
    insert_in_list α key value ls = ret b ∧
    (b ↔ ls.lookup key = none)
  := match ls with
  | .Nil => by simp [insert_in_list, insert_in_list_loop]
  | .Cons k v tl =>
    if h: k = key then -- TODO: The order of k/key matters
      by
        simp [insert_in_list]
        rw [insert_in_list_loop]
        simp [h]
    else
      have ⟨ b, hi ⟩ := insert_in_list_spec0 key value tl
      by
        exists b
        simp [insert_in_list]
        rw [insert_in_list_loop] -- TODO: Using simp leads to infinite recursion
        simp only [insert_in_list] at hi
        simp [*]

-- Variation: use progress
theorem insert_in_list_spec1 {α : Type} (key: Usize) (value: α) (ls: List α) :
  ∃ b,
    insert_in_list α key value ls = ret b ∧
    (b ↔ ls.lookup key = none)
  := match ls with
  | .Nil => by simp [insert_in_list, insert_in_list_loop]
  | .Cons k v tl =>
    if h: k = key then -- TODO: The order of k/key matters
      by
        simp [insert_in_list]
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

-- Variation: use tactics from the beginning
theorem insert_in_list_spec2 {α : Type} (key: Usize) (value: α) (ls: List α) :
  ∃ b,
    insert_in_list α key value ls = ret b ∧
    (b ↔ (ls.lookup key = none))
  := by
  induction ls
  case Nil => simp [insert_in_list, insert_in_list_loop]
  case Cons k v tl ih =>
    simp only [insert_in_list]
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
    l1.lookup key = value ∧
    (∀ k, k ≠ key → l1.lookup k = l0.lookup k)
  := match l0 with
  | .Nil => by
    simp (config := {contextual := true}) [insert_in_list_back, insert_in_list_loop_back]
  | .Cons k v tl =>
     if h: k = key then
       by
         simp [insert_in_list_back]
         rw [insert_in_list_loop_back]
         simp [h]
         intro k1 h1
         simp [*]
     else
       by
         simp [insert_in_list_back]
         rw [insert_in_list_loop_back]
         simp [h]
         progress keep as heq as ⟨ tl hp1 hp2 ⟩
         simp [insert_in_list_back] at heq
         simp (config := {contextual := true}) [*]

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

theorem insert_in_list_back_spec_aux {α : Type} (l : Int) (key: Usize) (value: α) (l0: List α)
  (hinv : slot_s_inv_hash l (hash_mod_key key l) l0.v) :
  ∃ l1,
    insert_in_list_back α key value l0 = ret l1 ∧
    -- We update the binding
    l1.lookup key = value ∧
    (∀ k, k ≠ key → l1.lookup k = l0.lookup k) ∧
    -- We preserve part of the key invariant
    slot_s_inv_hash l (hash_mod_key key l) l1.v ∧
    -- Reasoning about the length
    match l0.lookup key with
    | none => l1.len = l0.len + 1
    | some _ => l1.len = l0.len
  := match l0 with
  | .Nil => by
    simp (config := {contextual := true}) [insert_in_list_back, insert_in_list_loop_back, List.v, slot_s_inv_hash]
  | .Cons k v tl0 =>
     if h: k = key then
       by
         simp [insert_in_list_back]
         rw [insert_in_list_loop_back]
         simp [h]
         constructor
         . intros; simp [*]
         . simp [List.v, slot_s_inv_hash] at *
           simp [*]
     else
       by
         simp [insert_in_list_back]
         rw [insert_in_list_loop_back]
         simp [h]
         have : slot_s_inv_hash l (hash_mod_key key l) (List.v tl0) := by
           simp_all [List.v, slot_s_inv_hash]
         progress keep as heq as ⟨ tl1 hp1 hp2 hp3 hp4 ⟩
         simp only [insert_in_list_back] at heq
         have : slot_s_inv_hash l (hash_mod_key key l) (List.v (List.Cons k v tl1)) := by
           simp [List.v, slot_s_inv_hash] at *
           simp [*]
         -- TODO: canonize addition by default?
         simp_all [Int.add_assoc, Int.add_comm, Int.add_left_comm]

theorem insert_in_list_back_spec_aux1 {α : Type} (l : Int) (key: Usize) (value: α) (l0: List α)
  (hinv : slot_s_inv_hash l (hash_mod_key key l) l0.v)
  (hdk : distinct_keys l0.v) :
  ∃ l1,
    insert_in_list_back α key value l0 = ret l1 ∧
    -- We update the binding
    l1.lookup key = value ∧
    (∀ k, k ≠ key → l1.lookup k = l0.lookup k) ∧
    -- We preserve part of the key invariant
    slot_s_inv_hash l (hash_mod_key key l) l1.v ∧
    -- Reasoning about the length
    (match l0.lookup key with
     | none => l1.len = l0.len + 1
     | some _ => l1.len = l0.len) ∧
    -- The keys are distinct
    distinct_keys l1.v ∧
    -- We need this auxiliary property to prove that the keys distinct properties is preserved
    (∀ k, k ≠ key → l0.v.allP (λ (k1, _) => k ≠ k1) → l1.v.allP (λ (k1, _) => k ≠ k1))
  := match l0 with
  | .Nil => by
    simp (config := {contextual := true})
      [insert_in_list_back, insert_in_list_loop_back,
       List.v, slot_s_inv_hash, distinct_keys, List.pairwise_rel]
  | .Cons k v tl0 =>
     if h: k = key then
       by
         simp [insert_in_list_back]
         rw [insert_in_list_loop_back]
         simp [h]
         split_target_conjs
         . intros; simp [*]
         . simp [List.v, slot_s_inv_hash] at *
           simp [*]
         . simp [*, distinct_keys] at *
           apply hdk
         . tauto
     else
       by
         simp [insert_in_list_back]
         rw [insert_in_list_loop_back]
         simp [h]
         have : slot_s_inv_hash l (hash_mod_key key l) (List.v tl0) := by
           simp_all [List.v, slot_s_inv_hash]
         have : distinct_keys (List.v tl0) := by
           simp [distinct_keys] at hdk
           simp [hdk, distinct_keys]
         progress keep as heq as ⟨ tl1 hp1 hp2 hp3 hp4 hp5 hp6 ⟩ -- TODO: naming is weird
         simp only [insert_in_list_back] at heq
         have : slot_s_inv_hash l (hash_mod_key key l) (List.v (List.Cons k v tl1)) := by
           simp [List.v, slot_s_inv_hash] at *
           simp [*]
         have : distinct_keys ((k, v) :: List.v tl1) := by
           simp [distinct_keys] at *
           simp [*]
         -- TODO: canonize addition by default?
         simp_all [Int.add_assoc, Int.add_comm, Int.add_left_comm]

end HashMap

end hashmap
