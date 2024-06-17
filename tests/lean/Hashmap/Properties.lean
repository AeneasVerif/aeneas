import Hashmap.Funs

open Primitives
open Result

namespace List

-- TODO: we don't want to use the original List.lookup because it uses BEq
-- TODO: rewrite rule: match x == y with ... -> if x = y then ... else ... ? (actually doesn't work because of sugar)
-- TODO: move?
@[simp]
def lookup' {α : Type} (ls: List (Usize × α)) (key: Usize) : Option α :=
  match ls with
  | [] => none
  | (k, x) :: tl => if k = key then some x else lookup' tl key

end List

namespace hashmap

namespace AList

def v {α : Type} (ls: AList α) : List (Usize × α) :=
  match ls with
  | Nil => []
  | Cons k x tl => (k, x) :: v tl

@[simp] theorem v_nil (α : Type) : (Nil : AList α).v = [] := by rfl
@[simp] theorem v_cons {α : Type} k x (tl: AList α) : (Cons k x tl).v = (k, x) :: v tl := by rfl

@[simp]
abbrev lookup {α : Type} (ls: AList α) (key: Usize) : Option α :=
  ls.v.lookup' key

@[simp]
abbrev len {α : Type} (ls : AList α) : Int := ls.v.len

end AList

namespace HashMap

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

def distinct_keys (ls : List (Usize × α)) := ls.pairwise_rel (λ x y => x.fst ≠ y.fst)

def hash_mod_key (k : Usize) (l : Int) : Int :=
  match hash_key k with
  | .ok k => k.val % l
  | _ => 0

@[simp]
theorem hash_mod_key_eq : hash_mod_key k l = k.val % l := by
  simp [hash_mod_key, hash_key]

def slot_s_inv_hash (l i : Int) (ls : List (Usize × α)) : Prop :=
  ls.allP (λ (k, _) => hash_mod_key k l = i)

def slot_s_inv (l i : Int) (ls : List (Usize × α)) : Prop :=
  distinct_keys ls ∧
  slot_s_inv_hash l i ls

def slot_t_inv (l i : Int) (s : AList α) : Prop := slot_s_inv l i s.v

@[simp] theorem distinct_keys_nil : @distinct_keys α [] := by simp [distinct_keys]
@[simp] theorem slot_s_inv_hash_nil : @slot_s_inv_hash l i α [] := by simp [slot_s_inv_hash]
@[simp] theorem slot_s_inv_nil : @slot_s_inv α l i [] := by simp [slot_s_inv]

@[simp] theorem distinct_keys_cons (kv : Usize × α) (tl : List (Usize × α)) :
  distinct_keys (kv :: tl) ↔ ((tl.allP fun (k', _) => ¬↑kv.1 = ↑k') ∧ distinct_keys tl) := by simp [distinct_keys]

@[simp] theorem slot_s_inv_hash_cons (kv : Usize × α) (tl : List (Usize × α)) :
  slot_s_inv_hash l i (kv :: tl) ↔
    (hash_mod_key kv.1 l = i ∧ tl.allP (λ (k, _) => hash_mod_key k l = i) ∧ slot_s_inv_hash l i tl) :=
  by simp [slot_s_inv_hash]

@[simp] theorem slot_s_inv_cons (kv : Usize × α) (tl : List (Usize × α)) :
  slot_s_inv l i (kv :: tl) ↔
    ((tl.allP fun (k', _) => ¬↑kv.1 = ↑k') ∧ distinct_keys tl ∧
     hash_mod_key kv.1 l = i ∧ tl.allP (λ (k, _) => hash_mod_key k l = i) ∧ slot_s_inv l i tl) := by
    simp [slot_s_inv]; tauto

-- Interpret the hashmap as a list of lists
def v (hm : HashMap α) : List (List (Usize × α)) :=
  hm.slots.val.map AList.v

-- Interpret the hashmap as an associative list
def al_v (hm : HashMap α) : List (Usize × α) :=
  hm.v.flatten

-- TODO: automatic derivation
instance : Inhabited (AList α) where
  default := .Nil

@[simp]
def slots_s_inv (s : List (AList α)) : Prop :=
  ∀ (i : Int), 0 ≤ i → i < s.len → slot_t_inv s.len i (s.index i)

def slots_t_inv (s : alloc.vec.Vec (AList α)) : Prop :=
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

@[simp]
def slots_s_lookup (s : List (AList α)) (k : Usize) : Option α :=
  let i := hash_mod_key k s.len
  let slot := s.index i
  slot.lookup k

abbrev Slots α := alloc.vec.Vec (AList α)

abbrev Slots.lookup (s : Slots α) (k : Usize) := slots_s_lookup s.val k

abbrev Slots.al_v (s : Slots α) := (s.val.map AList.v).flatten

def lookup (hm : HashMap α) (k : Usize) : Option α :=
  slots_s_lookup hm.slots.val k

@[simp]
abbrev len_s (hm : HashMap α) : Int := hm.al_v.len

instance : Membership Usize (HashMap α) where
  mem k hm := hm.lookup k ≠ none

/- Activate the ↑ notation -/
attribute [coe] HashMap.v

-- This rewriting lemma is problematic below
attribute [-simp] Bool.exists_bool

-- The proof below is a bit expensive, so we need to increase the maximum number
-- of heart beats
set_option maxHeartbeats 1000000

theorem insert_in_list_spec_aux {α : Type} (l : Int) (key: Usize) (value: α) (l0: AList α)
  (hinv : slot_s_inv_hash l (hash_mod_key key l) l0.v)
  (hdk : distinct_keys l0.v) :
  ∃ b l1,
    insert_in_list α key value l0 = ok (b, l1) ∧
    -- The boolean is true ↔ we inserted a new binding
    (b ↔ (l0.lookup key = none)) ∧
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
  := by
  cases l0 with
  | Nil =>
    exists true -- TODO: why do we need to do this?
    simp [insert_in_list]
    rw [insert_in_list_loop]
    simp (config := {contextual := true}) [AList.v]
  | Cons k v tl0 =>
     if h: k = key then
       rw [insert_in_list]
       rw [insert_in_list_loop]
       simp [h]
       exists false; simp only [true_and, exists_eq_left', List.lookup', ↓reduceIte, AList.v_cons] -- TODO: why do we need to do this?
       split_conjs
       . intros; simp [*]
       . simp_all [slot_s_inv_hash]
       . simp at hinv; tauto
       . simp_all [slot_s_inv_hash]
       . simp_all
     else
       rw [insert_in_list]
       rw [insert_in_list_loop]
       simp [h]
       have : slot_s_inv_hash l (hash_mod_key key l) (AList.v tl0) := by
         simp_all [AList.v, slot_s_inv_hash]
       have : distinct_keys (AList.v tl0) := by
         simp [distinct_keys] at hdk
         simp [hdk, distinct_keys]
       progress as ⟨ b, tl1 .. ⟩
       have : slot_s_inv_hash l (hash_mod_key key l) (AList.v (AList.Cons k v tl1)) := by
         simp [AList.v, slot_s_inv_hash] at *
         simp [*]
       have : distinct_keys ((k, v) :: AList.v tl1) := by
         simp [distinct_keys] at *
         simp [*]
       -- TODO: canonize addition by default?
       exists b
       simp_all [Int.add_assoc, Int.add_comm, Int.add_left_comm]

@[pspec]
theorem insert_in_list_spec {α : Type} (l : Int) (key: Usize) (value: α) (l0: AList α)
  (hinv : slot_s_inv_hash l (hash_mod_key key l) l0.v)
  (hdk : distinct_keys l0.v) :
  ∃ b l1,
    insert_in_list α key value l0 = ok (b, l1) ∧
    (b ↔ (l0.lookup key = none)) ∧
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
  progress with insert_in_list_spec_aux as ⟨ b, l1 .. ⟩
  exists b
  exists l1

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

--set_option profiler true
--set_option profiler.threshold 10
--set_option trace.profiler true

-- For pretty printing (useful when copy-pasting goals)
set_option pp.coercions false -- do not print coercions with ↑ (this doesn't parse)

-- The proof below is a bit expensive, so we need to increase the maximum number
-- of heart beats
set_option maxHeartbeats 2000000

@[pspec]
theorem insert_no_resize_spec {α : Type} (hm : HashMap α) (key : Usize) (value : α)
  (hinv : hm.inv) (hnsat : hm.lookup key = none → hm.len_s < Usize.max) :
  ∃ nhm, hm.insert_no_resize α key value = ok nhm  ∧
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
  -- Simplify. Note that this also simplifies some function calls, like array index
  simp [hash_key, bind_tc_ok]
  have _ : (alloc.vec.Vec.len (AList α) hm.slots).val ≠ 0 := by
   intro
   simp_all [inv]
  progress as ⟨ hash_mod, hhm ⟩
  have _ : 0 ≤ hash_mod.val := by scalar_tac
  have _ : hash_mod.val < alloc.vec.Vec.length hm.slots := by
    have : 0 < hm.slots.val.len := by
      simp [inv] at hinv
      simp [hinv]
    -- TODO: we want to automate that
    simp [*, Int.emod_lt_of_pos]
  progress as ⟨ l, index_mut_back, h_leq, h_index_mut_back ⟩
  simp [h_index_mut_back] at *; clear h_index_mut_back index_mut_back
  have h_slot :
    slot_s_inv_hash hm.slots.length (hash_mod_key key hm.slots.length) l.v := by
    simp [inv] at hinv
    have h := (hinv.right.left hash_mod.val (by assumption) (by assumption)).right
    simp [slot_t_inv, hhm] at h
    simp [h, hhm, h_leq]
  have hd : distinct_keys l.v := by
    simp [inv, slots_t_inv, slot_t_inv, slot_s_inv] at hinv
    have h := hinv.right.left hash_mod.val (by assumption) (by assumption)
    simp [h, h_leq]
  progress as ⟨ inserted, l0, _, _, _, _, hlen .. ⟩
  rw [if_update_eq] -- TODO: necessary because we don't have a join
  -- TODO: progress to ...
  have hipost :
    ∃ i0, (if inserted = true then hm.num_entries + Usize.ofInt 1 else pure hm.num_entries) = ok i0 ∧
    i0.val = if inserted then hm.num_entries.val + 1 else hm.num_entries.val
    := by
    if inserted then
      simp [*]
      have hbounds : hm.num_entries.val + (Usize.ofInt 1).val ≤ Usize.max := by
        simp [lookup] at hnsat
        simp_all
        simp [inv] at hinv
        int_tac
      progress as ⟨ z, hp ⟩
      simp [hp]
    else
      simp [*, Pure.pure]
  progress as ⟨ i0 ⟩
  -- TODO: hide the variables and only keep the props
  -- TODO: allow providing terms to progress to instantiate the meta variables
  -- which are not propositions
  progress keep hv as ⟨ v, h_veq ⟩
  -- TODO: update progress to automate that
  -- TODO: later I don't want to inline nhm - we need to control simp: deactivate
  -- zeta reduction? For now I have to do this peculiar manipulation
  have ⟨ nhm, nhm_eq ⟩ := @mk_opaque (HashMap α) { num_entries := i0, max_load_factor := hm.max_load_factor, max_load := hm.max_load, slots := v }
  exists nhm
  have hupdt : lookup nhm key = some value := by
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
      simp only [k_hash_mod]
      apply Int.emod_nonneg k.val hvnz
    have _ : k_hash_mod < alloc.vec.Vec.length hm.slots := by
      -- TODO: we want to automate this
      simp only [k_hash_mod]
      have h := Int.emod_lt_of_pos k.val hvpos
      simp_all only [ok.injEq, exists_eq_left', List.len_update, gt_iff_lt,
                     List.index_update_eq, ne_eq, not_false_eq_true, neq_imp]
    if h_hm : k_hash_mod = hash_mod.val then
      simp_all only [k_hash_mod, List.len_update, gt_iff_lt, List.index_update_eq,
                     ne_eq, not_false_eq_true, neq_imp, alloc.vec.Vec.length]
    else
      simp_all only [k_hash_mod, List.len_update, gt_iff_lt, List.index_update_eq,
                     ne_eq, not_false_eq_true, neq_imp, ge_iff_le,
                     alloc.vec.Vec.length, List.index_update_ne]
  have _ :
    match hm.lookup key with
    | none => nhm.len_s = hm.len_s + 1
    | some _ => nhm.len_s = hm.len_s := by
    simp only [lookup, List.lookup, len_s, al_v, HashMap.v, slots_s_lookup] at *
    -- We have to do a case disjunction
    simp_all
    simp [List.update_map_eq]
    -- TODO: dependent rewrites
    have _ : key.val % hm.slots.val.len < (List.map AList.v hm.slots.val).len := by
      simp [*]
    simp [List.len_flatten_update_eq, *]
    split <;>
    rename_i heq <;>
    simp [heq] at hlen <;>
    -- TODO: canonize addition by default? We need a tactic to simplify arithmetic equalities
    -- with addition and substractions ((ℤ, +) is a group or something - there should exist a tactic
    -- somewhere in mathlib?)
    (try simp [Int.add_assoc, Int.add_comm, Int.add_left_comm]) <;>
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
      -- We need a case disjunction
      cases h_ieq : i == key.val % List.len hm.slots.val <;> simp_all [slot_s_inv]
    . simp [hinv, h_veq, nhm_eq]
  simp_all

theorem slot_allP_not_key_lookup (slot : AList T) (h : slot.v.allP fun (k', _) => ¬k = k') :
  slot.lookup k = none := by
  induction slot <;> simp_all

@[pspec]
theorem move_elements_from_list_spec
  {T : Type} (ntable : HashMap T) (slot : AList T)
  (hinv : ntable.inv)
  {l i : Int} (hSlotInv : slot_t_inv l i slot)
  (hDisjoint1 : ∀ key, ntable.lookup key ≠ none → slot.lookup key = none)
  (hDisjoint2 : ∀ key, slot.lookup key ≠ none → ntable.lookup key = none)
  (hLen : ntable.al_v.len + slot.v.len ≤ Usize.max)
  :
  ∃ ntable1, ntable.move_elements_from_list T slot = ok ntable1 ∧
  ntable1.inv ∧
  (∀ key, ntable1.lookup key ≠ none ↔
    (ntable.lookup key ≠ none ∨ slot.lookup key ≠ none)) ∧
  (∀ key, ntable1.lookup key = ntable.lookup key ∨
          ntable1.lookup key = slot.lookup key)
  := by
  rw [move_elements_from_list]; rw [move_elements_from_list_loop]
  cases slot with
  | Nil =>
    simp [hinv]
  | Cons key value slot1 =>
    simp
    have hLookupKey : ntable.lookup key = none := by simp_all
    have : ntable.lookup key = none → ntable.len_s < Usize.max := by simp_all; scalar_tac
    progress as ⟨ ntable1, _, _, hLookup12, hLength1 ⟩
    simp [hLookupKey] at hLength1
    have : ∀ (key : Usize), ntable1.lookup key ≠ none → slot1.lookup key = none := by
      intro key' hLookup
      if h: key = key' then
        simp_all [slot_t_inv]
        apply slot_allP_not_key_lookup
        simp_all
      else
        simp_all
        have := hDisjoint1 key' hLookup
        simp_all
    have : ∀ (key : Usize), slot1.lookup key ≠ none → ntable1.lookup key = none := by
      intro key' hLookup
      if h: key = key' then simp_all
      else
        simp [*] -- TODO: simplification (simp_all)
    have : ntable1.al_v.len + slot1.v.len ≤ Usize.max := by simp_all; scalar_tac
    have : slot_t_inv l i slot1 := by
      simp [slot_t_inv] at hSlotInv
      simp [slot_t_inv, hSlotInv]
    -- TODO: progress leads to: slot_t_inv i i slot1
    -- progress as ⟨ ntable2 ⟩
    have  ⟨ ntable2, hEq, hInv2, hLookup21, hLookup22 ⟩ := move_elements_from_list_spec ntable1 slot1 (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption)
    simp [hEq]; clear hEq
    split_conjs
    . simp [*]
    . intro key'
      if h: key = key' then simp_all
      else simp_all
    . intro key'
      have hLookup3 := hLookup22 key'
      if h: key = key' then
        simp_all
      else
        cases hLookup3 with
        | inl =>
          left
          have := hLookup12 key' (by simp [*])
          simp_all
        | inr =>
          simp_all

theorem slots_forall_nil_imp_lookup_none (slots : Slots T) (hLen : slots.val.len ≠ 0)
  (hEmpty : ∀ j, 0 ≤ j → j < slots.val.len → slots.val.index j = AList.Nil) :
  ∀ key, slots.lookup key = none := by
  intro key
  simp [Slots.lookup]
  have : 0 ≤ key.val % slots.val.len := by
    exact Int.emod_nonneg key.val hLen -- TODO: automate that
  have : key.val % slots.val.len < slots.val.len := by
    apply Int.emod_lt_of_pos
    scalar_tac
  have := hEmpty (key.val % slots.val.len) (by assumption) (by assumption)
  simp [*]

/- If we successfully lookup a key from a slot, the hash of the key modulo the number of slots must
   be equal to the slot index.
 -/
theorem slots_inv_lookup_imp_eq (slots : Slots α) (hInv : slots_t_inv slots)
  (i : Int) (h0 : 0 ≤ i) (h1 : i < slots.val.len) (key : Usize) :
  (slots.val.index i).lookup key ≠ none → i = key.val % slots.val.len := by
  suffices hSlot : ∀ (slot : List (Usize × α)),
           slot_s_inv slots.val.len i slot →
           slot.lookup' key ≠ none →
           i = key.val % slots.val.len
  from by
    rw [slots_t_inv, slots_s_inv] at hInv
    replace hInv := hInv i h0 h1
    simp [slot_t_inv] at hInv
    exact hSlot _ hInv
  intro slot
  induction slot <;> simp_all
  intros; simp_all
  split at * <;> simp_all

theorem slots_update_lookup_equiv (slots : Slots α) (hInv : slots_t_inv slots)
  (i : Int) (h0 : 0 ≤ i) (h1 : i < slots.val.len) (key : Usize) :
  let slot := slots.val.index i
  slot.lookup key ≠ none ∨ slots_s_lookup (slots.val.update i .Nil) key ≠ none ↔
  slots.lookup key ≠ none := by
  -- We need the following lemma to derive a contradiction
  have := slots_inv_lookup_imp_eq slots hInv i h0 h1 key
  cases hi : (key.val % slots.val.len) == i <;>
  simp_all [Slots.lookup]

theorem move_one_slot_lookup_equiv {α : Type} (ntable ntable1 ntable2 : HashMap α)
  (slot : AList α)
  (slots slots1 : Slots α)
  (i : Int) (h0 : 0 ≤ i) (h1 : i < ntable.slots.len)
  (hSlotEq : slot = slots.val.index i)
  (hSlots1Eq : slots1.val = slots.val.update i .Nil)
  (hLen1 : ntable1.slots.len = ntable.slots.len)
  (hLen2 : ntable2.slots.len = ntable1.slots.len)
  (hLookup1 : ntable1.lookup key = ntable.lookup key ∨ ntable1.lookup key = slot.lookup key)
  (hLookup2 : ntable2.lookup key = ntable1.lookup key ∨ ntable2.lookup key = Slots.lookup slots1 key)
  (key : Usize) :
  ntable2.lookup key = ntable.lookup key ∨ ntable2.lookup key = slots.lookup key := by
  if heq : key.val % slots.val.len = i then
    right
    sorry
  else
    left
    sorry

theorem move_elements_loop_spec
  {α : Type} (ntable : HashMap α) (slots : Slots α)
  (i : Usize) (hi : i ≤ alloc.vec.Vec.len (AList α) slots)
  (hinv : ntable.inv)
  (hSlotsNonZero : slots.val.len ≠ 0)
  (hSlotsInv : slots_t_inv slots)
  (hEmpty : ∀ j, 0 ≤ j → j < i.val → slots.val.index j = AList.Nil)
  (hDisjoint1 : ∀ key, ntable.lookup key ≠ none → slots.lookup key = none)
  (hDisjoint2 : ∀ key, slots.lookup key ≠ none → ntable.lookup key = none)
  (hLen : ntable.al_v.len + slots.al_v.len ≤ Usize.max)
  :
  ∃ ntable1 slots1, ntable.move_elements_loop α slots i = ok (ntable1, slots1) ∧
  ntable1.inv ∧
  slots1.len = slots.len ∧
  (∀ key, ntable1.lookup key ≠ none ↔
    (ntable.lookup key ≠ none ∨ slots.lookup key ≠ none)) ∧
  (∀ key v, slots.lookup key = some v → ntable1.lookup key = some v) ∧
  (∀ key v, ntable.lookup key = some v → ntable1.lookup key = some v) ∧
  (∀ (j : Int), 0 ≤ j → j < slots1.len → slots1.val.index j = AList.Nil)
  := by
    rw [move_elements_loop]
    simp
  --if hi: i < alloc.vec.Vec.len (AList T) slots then
    have hi: i < alloc.vec.Vec.len (AList α) slots := by sorry
    simp [hi]
    progress as ⟨ slot, index_back, hSlotEq, hIndexBack ⟩
    rw [hIndexBack]; clear hIndexBack
    have hInvSlot : slot_t_inv slots.val.len i.val slot := by
      simp [slots_t_inv] at hSlotsInv
      simp [hSlotEq]
      apply hSlotsInv <;> scalar_tac
    have : ∀ (key : Usize), ntable.lookup key ≠ none → slot.lookup key = none := by sorry
    have : ∀ (key : Usize), slot.lookup key ≠ none → ntable.lookup key = none := by sorry
    have : ntable.al_v.len + slot.v.len ≤ Usize.max := by sorry
    progress as ⟨ ntable1, _, _, hLookup1 ⟩ -- TODO: decompose post-condition by default
    progress as ⟨ i' .. ⟩
    progress as ⟨ slots1 .. ⟩
    have : i' ≤ alloc.vec.Vec.len (AList α) slots1 := by sorry
    have : slots_t_inv slots1 := by sorry
    have : ∀ (key : Usize), ntable1.lookup key ≠ none → Slots.lookup slots1 key = none := by sorry
    have : ∀ (key : Usize), ntable1.lookup key ≠ none → Slots.lookup slots1 key = none := by sorry
    have : ∀ (j : ℤ), OfNat.ofNat 0 ≤ j → j < i'.val → slots1.val.index j = AList.Nil := by sorry
    have : ∀ (key : Usize), Slots.lookup slots1 key ≠ none → ntable1.lookup key = none := by sorry
    have : ntable1.al_v.len + (Slots.al_v slots1).len ≤ Usize.max := by sorry
    progress as ⟨ ntable2, slots2, _, _, _, _, hLookup2, hIndexNil ⟩
    simp [and_assoc]
    have : ∀ (j : ℤ), OfNat.ofNat 0 ≤ j → j < slots2.val.len → slots2.val.index j = AList.Nil := by
      intro j h0 h1
      apply hIndexNil j h0 h1
    have : ∀ (key : Usize),
       ntable.lookup key ≠ none ∨ slot.lookup key ≠ none ∨ Slots.lookup slots1 key ≠ none ↔
       ntable.lookup key ≠ none ∨ slots.lookup key ≠ none := by
       intro key
       have := slots_update_lookup_equiv slots hSlotsInv i.val (by scalar_tac) (by scalar_tac) key
       simp_all [Slots.lookup]
    have : ∀ (key : Usize), ntable2.lookup key = ntable.lookup key ∨
                            ntable2.lookup key = slots.lookup key := by
      intro key
      replace hLookup1 := hLookup1 key
      replace hLookup2 := hLookup2 key
      have : Slots.lookup slots1 key = ntable.lookup key ∨ Slots.lookup slots1 key = slots.lookup key := by
        sorry
      cases hLookup2 <;> simp [*]
      cases hLookup1 <;> simp [*]

    stop
    simp_all [alloc.vec.Vec.len, or_assoc]
  /-else
    stop
    simp [hi, and_assoc, *]
    simp_all
    have hi : i = alloc.vec.Vec.len (AList T) slots := by scalar_tac
    have hEmpty : ∀ j, 0 ≤ j → j < slots.val.len → slots.val.index j = AList.Nil := by
      simp [hi] at hEmpty
      exact hEmpty
    have hLenNonZero : slots.val.len ≠ 0 := by simp [*]
    have hLookupEmpty := slots_forall_nil_imp_lookup_none slots hLenNonZero hEmpty
    simp [hLookupEmpty]
    apply hEmpty-/
--termination_by (slots.val.len - i.val).toNat
--decreasing_by scalar_decr_tac


end HashMap

end hashmap
