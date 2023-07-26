import Hashmap.Funs

open Primitives
open Result

namespace List

-- TODO: we don't want to use the original List.lookup because it uses BEq
-- TODO: rewrite rule: match x == y with ... -> if x = y then ... else ... ? (actually doesn't work because of sugar)
-- TODO: move?
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
-- TODO: this doesn't work because of sugar
theorem match_lawful_beq [BEq α] [LawfulBEq α] [DecidableEq α] (x y : α) :
  (x == y) = (if x = y then true else false) := by
  split <;> simp_all

@[pspec]
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
        progress keep heq as ⟨ b, hi ⟩
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
     progress as ⟨ b, h ⟩
     simp [*]

def distinct_keys (ls : Core.List (Usize × α)) := ls.pairwise_rel (λ x y => x.fst ≠ y.fst)

def hash_mod_key (k : Usize) (l : Int) : Int :=
  match hash_key k with
  | .ret k => k.val % l
  | _ => 0

@[simp]
theorem hash_mod_key_eq : hash_mod_key k l = k.val % l := by
  simp [hash_mod_key, hash_key]

def slot_s_inv_hash (l i : Int) (ls : Core.List (Usize × α)) : Prop :=
  ls.allP (λ (k, _) => hash_mod_key k l = i)

@[simp]
def slot_s_inv (l i : Int) (ls : Core.List (Usize × α)) : Prop :=
  distinct_keys ls ∧
  slot_s_inv_hash l i ls

def slot_t_inv (l i : Int) (s : List α) : Prop := slot_s_inv l i s.v

-- Interpret the hashmap as a list of lists
def v (hm : HashMap α) : Core.List (Core.List (Usize × α)) :=
  hm.slots.val.map List.v

-- Interpret the hashmap as an associative list
def al_v (hm : HashMap α) : Core.List (Usize × α) :=
  hm.v.flatten

-- TODO: automatic derivation
instance : Inhabited (List α) where
  default := .Nil

@[simp]
def slots_s_inv (s : Core.List (List α)) : Prop :=
  ∀ (i : Int), 0 ≤ i → i < s.len → slot_t_inv s.len i (s.index i)

def slots_t_inv (s : Vec (List α)) : Prop :=
  slots_s_inv s.v

@[simp]
def base_inv (hm : HashMap α) : Prop :=
  -- [num_entries] correctly tracks the number of entries
  hm.num_entries.val = hm.al_v.len ∧
  -- Slots invariant
  slots_t_inv hm.slots ∧
  -- The capacity must be > 0 (otherwise we can't resize)
  0 < hm.slots.length
  -- TODO: load computation

def inv (hm : HashMap α) : Prop :=
  -- Base invariant
  base_inv hm
  -- TODO: either the hashmap is not overloaded, or we can't resize it

theorem insert_in_list_back_spec_aux {α : Type} (l : Int) (key: Usize) (value: α) (l0: List α)
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
  | .Nil => by checkpoint
    simp (config := {contextual := true})
      [insert_in_list_back, insert_in_list_loop_back,
       List.v, slot_s_inv_hash, distinct_keys, List.pairwise_rel]
  | .Cons k v tl0 =>
     if h: k = key then by checkpoint
       simp [insert_in_list_back]
       rw [insert_in_list_loop_back]
       simp [h]
       split_conjs
       . intros; simp [*]
       . simp [List.v, slot_s_inv_hash] at *
         simp [*]
       . simp [*, distinct_keys] at *
         apply hdk
       . tauto
     else by checkpoint
       simp [insert_in_list_back]
       rw [insert_in_list_loop_back]
       simp [h]
       have : slot_s_inv_hash l (hash_mod_key key l) (List.v tl0) := by checkpoint
         simp_all [List.v, slot_s_inv_hash]
       have : distinct_keys (List.v tl0) := by checkpoint
         simp [distinct_keys] at hdk
         simp [hdk, distinct_keys]
       progress keep heq as ⟨ tl1 .. ⟩
       simp only [insert_in_list_back] at heq
       have : slot_s_inv_hash l (hash_mod_key key l) (List.v (List.Cons k v tl1)) := by checkpoint
         simp [List.v, slot_s_inv_hash] at *
         simp [*]
       have : distinct_keys ((k, v) :: List.v tl1) := by checkpoint
         simp [distinct_keys] at *
         simp [*]
       -- TODO: canonize addition by default?
       simp_all [Int.add_assoc, Int.add_comm, Int.add_left_comm]

@[pspec]
theorem insert_in_list_back_spec {α : Type} (l : Int) (key: Usize) (value: α) (l0: List α)
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
    distinct_keys l1.v
  := by
  progress with insert_in_list_back_spec_aux as ⟨ l1 .. ⟩
  exists l1

@[simp]
def slots_t_lookup (s : Core.List (List α)) (k : Usize) : Option α :=
  let i := hash_mod_key k s.len
  let slot := s.index i
  slot.lookup k

def lookup (hm : HashMap α) (k : Usize) : Option α :=
  slots_t_lookup hm.slots.val k

@[simp]
abbrev len_s (hm : HashMap α) : Int := hm.al_v.len

-- Remark: α and β must live in the same universe, otherwise the
-- bind doesn't work
theorem if_update_eq
  {α β : Type u} (b : Bool) (y : α) (e : Result α) (f : α → Result β) :
  (if b then Bind.bind e f else f y) = Bind.bind (if b then e else pure y) f
  := by
  split <;> simp [Pure.pure]

-- Small helper
-- TODO: move, and introduce a better solution with nice syntax
def mk_opaque {α : Sort u} (x : α) : { y : α // y = x}  :=
  ⟨ x, by simp ⟩

theorem insert_no_resize_spec {α : Type} (hm : HashMap α) (key : Usize) (value : α)
  (hinv : hm.inv) (hnsat : hm.lookup key = none → hm.len_s < Usize.max) :
  ∃ nhm, hm.insert_no_resize α key value = ret nhm  ∧
  -- We preserve the invariant
  nhm.inv ∧
  -- We updated the binding for key
  nhm.lookup key = some value ∧
  -- We left the other bindings unchanged
  (∀ k, ¬ k = key → nhm.lookup k = hm.lookup k) ∧
  -- Reasoning about the length
  (match hm.lookup key with
   | none => nhm.len_s = hm.len_s + 1
   | some _ => nhm.len_s = hm.len_s) := by
  rw [insert_no_resize]
  simp only [hash_key, bind_tc_ret] -- TODO: annoying
  have _ : (Vec.len (List α) hm.slots).val ≠ 0 := by checkpoint
   intro
   simp_all [inv]
  progress keep _ as ⟨ hash_mod, hhm ⟩
  have _ : 0 ≤ hash_mod.val := by checkpoint scalar_tac
  have _ : hash_mod.val < Vec.length hm.slots := by
    have : 0 < hm.slots.val.len := by
      simp [inv] at hinv
      simp [hinv]
    -- TODO: we want to automate that
    simp [*, Int.emod_lt_of_pos]
  -- TODO: change the spec of Vec.index_mut to introduce a let-binding.
  -- or: make progress introduce the let-binding by itself (this is clearer)
  progress as ⟨ l, h_leq ⟩
  -- TODO: make progress use the names written in the goal
  progress as ⟨ inserted ⟩
  rw [if_update_eq] -- TODO: necessary because we don't have a join
  -- TODO: progress to ...
  have hipost :
    ∃ i0, (if inserted = true then hm.num_entries + Usize.ofInt 1 else pure hm.num_entries) = ret i0 ∧
    i0.val = if inserted then hm.num_entries.val + 1 else hm.num_entries.val
    := by
    if inserted then
      simp [*]
      have hbounds : hm.num_entries.val + (Usize.ofInt 1).val ≤ Usize.max := by
        simp [lookup] at hnsat
        simp_all
        simp [inv] at hinv
        int_tac
      -- TODO: progress fails in command line mode with "index out of bounds"
      -- and I have no idea how to fix this. The error happens after progress
      -- introduced the new goals. It must be when we exit the "withApp", etc.
      -- helpers.
      have ⟨ z, hp ⟩ := Usize.add_spec hbounds
      simp [hp]
    else
      simp [*, Pure.pure]
  progress as ⟨ i0 ⟩
  have h_slot : slot_s_inv_hash hm.slots.length (hash_mod_key key hm.slots.length) l.v
    := by
    simp [inv] at hinv
    have h := (hinv.right.left hash_mod.val (by assumption) (by assumption)).right
    simp [slot_t_inv, hhm] at h
    simp [h, hhm, h_leq]
  have hd : distinct_keys l.v := by checkpoint
    simp [inv, slots_t_inv, slot_t_inv] at hinv
    have h := hinv.right.left hash_mod.val (by assumption) (by assumption)
    simp [h, h_leq]
  -- TODO: hide the variables and only keep the props
  -- TODO: allow providing terms to progress to instantiate the meta variables
  -- which are not propositions
  progress as ⟨ l0, _, _, _, hlen .. ⟩
  progress keep hv as ⟨ v, h_veq ⟩
  -- TODO: update progress to automate that
  -- TODO: later I don't want to inline nhm - we need to control simp: deactivate
  -- zeta reduction? For now I have to do this peculiar manipulation
  have ⟨ nhm, nhm_eq ⟩ := @mk_opaque (HashMap α) { num_entries := i0, max_load_factor := hm.max_load_factor, max_load := hm.max_load, slots := v }
  exists nhm
  have hupdt : lookup nhm key = some value := by checkpoint
    simp [lookup, List.lookup] at *
    simp_all
  have hlkp : ∀ k, ¬ k = key → nhm.lookup k = hm.lookup k := by
    simp [lookup, List.lookup] at *
    intro k hk
    -- We have to make a case disjunction: either the hashes are different,
    -- in which case we don't even lookup the same slots, or the hashes
    -- are the same, in which case we have to reason about what happens
    -- in one slot
    let k_hash_mod := k.val % v.val.len
    have : 0 < hm.slots.val.len := by simp_all [inv]
    have hvpos : 0 < v.val.len := by simp_all
    have hvnz: v.val.len ≠ 0 := by
      simp_all
    have _ : 0 ≤ k_hash_mod := by
      -- TODO: we want to automate this
      simp
      apply Int.emod_nonneg k.val hvnz
    have _ : k_hash_mod < Vec.length hm.slots := by
      -- TODO: we want to automate this
      simp
      have h := Int.emod_lt_of_pos k.val hvpos
      simp_all
    if h_hm : k_hash_mod = hash_mod.val then
      simp_all
    else
      simp_all
  have _ :
    match hm.lookup key with
    | none => nhm.len_s = hm.len_s + 1
    | some _ => nhm.len_s = hm.len_s := by checkpoint
    simp only [lookup, List.lookup, len_s, al_v, HashMap.v, slots_t_lookup] at *
    -- We have to do a case disjunction
    simp_all
    simp [_root_.List.update_map_eq]
    -- TODO: dependent rewrites
    have _ : key.val % hm.slots.val.len < (List.map List.v hm.slots.val).len := by
      simp [*]
    simp [_root_.List.len_flatten_update_eq, *]
    split <;>
    rename_i heq <;>
    simp [heq] at hlen <;>
    -- TODO: canonize addition by default? We need a tactic to simplify arithmetic equalities
    -- with addition and substractions ((ℤ, +) is a group or something - there should exist a tactic
    -- somewhere in mathlib?)
    simp [Int.add_assoc, Int.add_comm, Int.add_left_comm] <;>
    int_tac
  have hinv : inv nhm := by
    simp [inv] at *
    split_conjs
    . match h: lookup hm key with
      | none =>
        simp [h, lookup] at *
        simp_all
      | some _ =>
        simp_all [lookup]
    . simp [slots_t_inv, slot_t_inv] at *
      intro i hipos _
      have _ := hinv.right.left i hipos (by simp_all)
      simp [hhm, h_veq, nhm_eq] at * -- TODO: annoying, we do that because simp_all fails below
      -- We need a case disjunction
      if h_ieq : i = key.val % _root_.List.len hm.slots.val then
        -- TODO: simp_all fails: "(deterministic) timeout at 'whnf'"
        -- Also, it is annoying to do this kind
        -- of rewritings by hand. We could have a different simp
        -- which safely substitutes variables when we have an
        -- equality `x = ...` and `x` doesn't appear in the rhs
        simp [h_ieq] at *
        simp [*]
      else
        simp [*]
    . -- TODO: simp[*] fails: "(deterministic) timeout at 'whnf'"
      simp [hinv, h_veq, nhm_eq]
  simp_all

end HashMap

end hashmap
