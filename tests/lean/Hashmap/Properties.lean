import Hashmap.Funs

open Aeneas.Std
open Result

#setup_aeneas_simps

namespace hashmap

namespace AList

@[simp, scalar_tac_simps, grind]
def v {α : Type} (ls: AList α) : List (Usize × α) :=
  match ls with
  | Nil => []
  | Cons k x tl => (k, x) :: v tl

@[simp]
abbrev lookup {α : Type} (ls: AList α) (key: Usize) : Option α :=
  ls.v.lookup key

@[simp, scalar_tac_simps, grind]
abbrev length {α : Type} (ls : AList α) : Nat := ls.v.length

end AList

namespace HashMap

def distinct_keys (ls : List (Usize × α)) := ls.pairwise_rel (λ x y => x.fst ≠ y.fst)

def hash_mod_key (k : Usize) (l : Nat) : Nat :=
  match hash_key k with
  | .ok k => k.val % l
  | _ => 0

@[simp]
theorem hash_mod_key_eq : hash_mod_key k l = k.val % l := by
  fsimp [hash_mod_key, hash_key]

def slot_s_inv_hash (l i : Nat) (ls : List (Usize × α)) : Prop :=
  ls.allP (λ (k, _) => hash_mod_key k l = i)

def slot_s_inv (l i : Nat) (ls : List (Usize × α)) : Prop :=
  distinct_keys ls ∧
  slot_s_inv_hash l i ls

def slot_t_inv (l i : Nat) (s : AList α) : Prop := slot_s_inv l i s.v

@[simp] theorem distinct_keys_nil : @distinct_keys α [] := by fsimp [distinct_keys]
@[simp] theorem slot_s_inv_hash_nil : @slot_s_inv_hash l i α [] := by fsimp [slot_s_inv_hash]
@[simp] theorem slot_s_inv_nil : @slot_s_inv α l i [] := by fsimp [slot_s_inv]
@[simp] theorem slot_t_inv_nil : @slot_t_inv α l i .Nil := by fsimp [slot_t_inv]

@[simp] theorem distinct_keys_cons (kv : Usize × α) (tl : List (Usize × α)) :
  distinct_keys (kv :: tl) ↔ ((tl.allP fun (k', _) => ¬↑kv.1 = ↑k') ∧ distinct_keys tl) := by fsimp [distinct_keys]

@[simp] theorem slot_s_inv_hash_cons (kv : Usize × α) (tl : List (Usize × α)) :
  slot_s_inv_hash l i (kv :: tl) ↔
    (hash_mod_key kv.1 l = i ∧ tl.allP (λ (k, _) => hash_mod_key k l = i) ∧ slot_s_inv_hash l i tl) :=
  by fsimp [slot_s_inv_hash]

@[simp] theorem slot_s_inv_cons (kv : Usize × α) (tl : List (Usize × α)) :
  slot_s_inv l i (kv :: tl) ↔
    ((tl.allP fun (k', _) => ¬↑kv.1 = ↑k') ∧ distinct_keys tl ∧
     hash_mod_key kv.1 l = i ∧ tl.allP (λ (k, _) => hash_mod_key k l = i) ∧ slot_s_inv l i tl) := by
    fsimp [slot_s_inv]; tauto

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
  ∀ (i : Nat), i < s.length → slot_t_inv s.length i s[i]!

def slots_t_inv (s : alloc.vec.Vec (AList α)) : Prop :=
  slots_s_inv s.v

@[simp]
def slots_s_lookup (s : List (AList α)) (k : Usize) : Option α :=
  let i := hash_mod_key k s.length
  let slot := s[i]!
  slot.lookup k

abbrev Slots α := alloc.vec.Vec (AList α)

abbrev Slots.lookup (s : Slots α) (k : Usize) := slots_s_lookup s.val k

abbrev Slots.al_v (s : Slots α) := (s.val.map AList.v).flatten

def lookup (hm : HashMap α) (k : Usize) : Option α :=
  slots_s_lookup hm.slots.val k

@[simp, scalar_tac_simps, grind]
abbrev len_s (hm : HashMap α) : Nat := hm.al_v.length

instance : Membership Usize (HashMap α) where
  mem (hm : HashMap α) k := hm.lookup k ≠ none

/- Activate the ↑ notation -/
attribute [coe] HashMap.v

abbrev inv_load (hm : HashMap α) : Prop :=
  let capacity : Int := hm.slots.val.length
  let dividend := hm.max_load_factor.dividend.val
  let divisor := hm.max_load_factor.divisor.val
  0 < dividend ∧ dividend < divisor ∧
  capacity * dividend >= divisor ∧
  hm.max_load = (capacity * dividend) / divisor

@[simp]
def inv_base (hm : HashMap α) : Prop :=
  -- [num_entries] correctly tracks the number of entries
  hm.num_entries.val = hm.al_v.length ∧
  -- Slots invariant
  slots_t_inv hm.slots ∧
  -- The capacity must be > 0 (otherwise we can't resize)
  0 < hm.slots.length ∧
  -- Load computation
  inv_load hm

def inv (hm : HashMap α) : Prop :=
  -- Base invariant
  inv_base hm
  -- TODO: either the hashmap is not overloaded, or we can't resize it

def frame_load (hm nhm : HashMap α) : Prop :=
  nhm.max_load_factor = hm.max_load_factor ∧
  nhm.max_load = hm.max_load ∧
  nhm.saturated = hm.saturated

-- These fsimp lemmas were introduced by upstream changes and are problematic
attribute [-simp] List.length_flatten List.flatten_eq_nil_iff List.lookup_eq_none_iff

attribute [local simp] List.lookup

/- Adding some theorems for `scalar_tac` -/
@[local scalar_tac h]
theorem inv_imp_eqs_ineqs {hm : HashMap α} (h : hm.inv) :
  0 < hm.slots.length ∧ hm.num_entries.val = hm.al_v.length := by
  simp_all [inv]

-- The proofs below are a bit expensive, so we deactivate the heart bits limit
set_option maxHeartbeats 0

open AList

@[progress]
theorem allocate_slots_spec {α : Type} (slots : alloc.vec.Vec (AList α)) (n : Usize)
  (Hslots : ∀ (i : Nat), i < slots.length → slots[i]! = Nil)
  (Hlen : slots.len + n.val ≤ Usize.max) :
  ∃ slots1, allocate_slots slots n = ok slots1 ∧
  (∀ (i : Nat), i < slots1.length → slots1[i]! = Nil) ∧
  slots1.len = slots.len + n.val := by
  unfold allocate_slots allocate_slots_loop
  fsimp at *
  if h: 0 < n.val then
    fsimp [h]
    progress as ⟨ slots1 ⟩
    progress as ⟨ n1 ⟩
    have Hslots1Nil :
      ∀ (i : Nat), i < slots1.length → slots1[i]! = Nil := by
      intro i h0
      by_cases hi: i < slots.length <;> simp_lists [*]
    have Hslots1Len : alloc.vec.Vec.len slots1 + n1.val ≤ Usize.max := by
      scalar_tac
    progress as ⟨ slots2 ⟩
    split_conjs
    . intro i h0
      fsimp_all
    . simp_all
  else
    fsimp [h]
    fsimp_all
termination_by n.val
decreasing_by scalar_decr_tac

theorem forall_nil_imp_flatten_len_zero (slots : List (List α))
  (Hnil : ∀ i, i < slots.length → slots[i]! = []) :
  slots.flatten = [] := by
  induction slots <;> fsimp_all
  have Hhead := Hnil 0 (by simp)
  fsimp at Hhead
  fsimp_all
  rename _ → _ => Hind
  apply Hind
  intros i h0
  have := Hnil (i + 1) (by scalar_tac)
  have : 0 < i + 1 := by scalar_tac
  -- TODO: fsimp_all eliminates Hnil
  fsimp at *; fsimp_all

@[progress]
theorem new_with_capacity_spec
  (capacity : Usize) (max_load_factor : Fraction)
  (Hcapa : 0 < capacity.val)
  (Hfactor : 0 < max_load_factor.dividend.val ∧
             max_load_factor.dividend.val < max_load_factor.divisor.val ∧
             capacity.val * max_load_factor.dividend.val ≤ Usize.max ∧
             capacity.val * max_load_factor.dividend.val ≥ max_load_factor.divisor)
  (Hdivid : 0 < max_load_factor.divisor.val) :
  ∃ hm, new_with_capacity α capacity max_load_factor = ok hm ∧
  hm.inv ∧ hm.len_s = 0 ∧ hm.v.length = capacity.val ∧ hm.max_load_factor = max_load_factor ∧
  ∀ k, hm.lookup k = none := by
  unfold new_with_capacity
  progress as ⟨ slots, Hnil ⟩
  progress as ⟨ i1 ⟩
  progress as ⟨ i2 ⟩
  fsimp [inv, inv_load]
  have : (Slots.al_v slots).length = 0 := by
    have := forall_nil_imp_flatten_len_zero (slots.val.map AList.v)
      (by intro i h0
          -- TODO: fsimp_all eliminates Hnil !?
          fsimp at *
          fsimp_all)
    fsimp_all
  have : 0 < slots.val.length := by scalar_tac
  have : slots_t_inv slots := by
    fsimp [slots_t_inv, slot_t_inv]
    intro i h0
    fsimp_all
  split_conjs
  . fsimp_all [al_v, Slots.al_v, v]
  . assumption
  . scalar_tac
  . fsimp_all [alloc.vec.Vec.len, alloc.vec.Vec.new]
  . fsimp_all
  . scalar_tac
  . fsimp_all [alloc.vec.Vec.len, alloc.vec.Vec.new]
  . fsimp_all [al_v, Slots.al_v, v]
  . simp_all [HashMap.v]
  . fsimp [lookup]
    intro k
    simp_lists [Hnil]
    simp

@[progress]
theorem new_spec (α : Type) :
  ∃ hm, new α = ok hm ∧
  hm.inv ∧ hm.len_s = 0 ∧ ∀ k, hm.lookup k = none := by
  unfold new
  progress as ⟨ hm ⟩
  fsimp_all

example (key : Usize) : key == key := by fsimp [beq_iff_eq]

theorem insert_in_list_spec_aux {α : Type} (l : Nat) (key: Usize) (value: α) (l0: AList α)
  (hinv : slot_s_inv_hash l (hash_mod_key key l) l0.v)
  (hdk : distinct_keys l0.v) :
  ∃ b l1,
    insert_in_list key value l0 = ok (b, l1) ∧
    -- The boolean is true ↔ we inserted a new binding
    (b ↔ (l0.lookup key = none)) ∧
    -- We update the binding
    l1.lookup key = value ∧
    (∀ k, k ≠ key → l1.lookup k = l0.lookup k) ∧
    -- We preserve part of the key invariant
    slot_s_inv_hash l (hash_mod_key key l) l1.v ∧
    -- Reasoning about the length
    (match l0.lookup key with
     | none => l1.length = l0.length + 1
     | some _ => l1.length = l0.length) ∧
    -- The keys are distinct
    distinct_keys l1.v ∧
    -- We need this auxiliary property to prove that the keys distinct properties is preserved
    (∀ k, k ≠ key → l0.v.allP (λ (k1, _) => k ≠ k1) → l1.v.allP (λ (k1, _) => k ≠ k1))
  := by
  cases l0; swap
  . fsimp [insert_in_list]
    unfold insert_in_list_loop
    fsimp (config := {contextual := true}) [AList.v]
    intros; split <;> fsimp_all
  . rename_i k v tl0
    if h: k = key then
      unfold insert_in_list insert_in_list_loop
      fsimp [h]
      split_conjs <;> fsimp_all [slot_s_inv_hash]
      intros; split <;> fsimp_all
    else
      unfold insert_in_list insert_in_list_loop
      fsimp [h]
      have : slot_s_inv_hash l (hash_mod_key key l) (AList.v tl0) := by
        fsimp_all [AList.v, slot_s_inv_hash]
      have : distinct_keys (AList.v tl0) := by
        fsimp [distinct_keys] at hdk
        fsimp [hdk, distinct_keys]
      progress as ⟨ b, tl1 ⟩
      have : slot_s_inv_hash l (hash_mod_key key l) (AList.v (AList.Cons k v tl1)) := by
        fsimp [AList.v, slot_s_inv_hash] at *
        fsimp [*]
      have : distinct_keys ((k, v) :: AList.v tl1) := by
        fsimp [distinct_keys] at *
        fsimp [*]
      -- TODO: canonize addition by default?
      simp_all only [hash_mod_key_eq, AList.v, slot_s_inv_hash_cons, distinct_keys_cons,
        UScalar.neq_to_neq_val, and_true, AList.lookup, ne_eq, length, true_and, not_false_eq_true,
        and_self, exists_and_left, exists_eq_left', List.lookup, implies_true, List.length_cons,
        Nat.add_right_cancel_iff, List.allP_cons]
      split <;> fsimp_all

@[progress]
theorem insert_in_list_spec {α : Type} (l : Nat) (key: Usize) (value: α) (l0: AList α)
  (hinv : slot_s_inv_hash l (hash_mod_key key l) l0.v)
  (hdk : distinct_keys l0.v) :
  ∃ b l1,
    insert_in_list key value l0 = ok (b, l1) ∧
    (b ↔ (l0.lookup key = none)) ∧
    -- We update the binding
    l1.lookup key = value ∧
    (∀ k, k ≠ key → l1.lookup k = l0.lookup k) ∧
    -- We preserve part of the key invariant
    slot_s_inv_hash l (hash_mod_key key l) l1.v ∧
    -- Reasoning about the length
    (match l0.lookup key with
     | none => l1.length = l0.length + 1
     | some _ => l1.length = l0.length) ∧
    -- The keys are distinct
    distinct_keys l1.v
  := by
  progress with insert_in_list_spec_aux as ⟨ b, l1 ⟩
  exists b
  exists l1

-- Remark: α and β must live in the same universe, otherwise the
-- bind doesn't work
theorem if_update_eq
  {α β : Type u} (b : Bool) (y : α) (e : Result α) (f : α → Result β) :
  (if b then Bind.bind e f else f y) = Bind.bind (if b then e else pure y) f
  := by
  split <;> fsimp [Pure.pure]

def frame_slots_params (hm1 hm2 : HashMap α) :=
  -- The max load factor is the same
  hm2.max_load_factor = hm1.max_load_factor ∧
  -- The number of slots is the same
  hm2.slots.val.length = hm1.slots.val.length

@[progress]
theorem insert_no_resize_spec {α : Type} (hm : HashMap α) (key : Usize) (value : α)
  (hinv : hm.inv) (hnsat : hm.lookup key = none → hm.len_s < Usize.max) :
  ∃ nhm, hm.insert_no_resize key value = ok nhm  ∧
  -- We preserve the invariant
  nhm.inv ∧
  -- Frame information
  frame_slots_params hm nhm ∧
  -- We updated the binding for key
  nhm.lookup key = some value ∧
  -- We left the other bindings unchanged
  (∀ k, ¬ k = key → nhm.lookup k = hm.lookup k) ∧
  -- Reasoning about the length
  (match hm.lookup key with
   | none => nhm.len_s = hm.len_s + 1
   | some _ => nhm.len_s = hm.len_s) := by
  unfold insert_no_resize
  -- Simplify. Note that this also simplifies some function calls, like array index
  fsimp [hash_key, bind_tc_ok]
  progress as ⟨ hash_mod, hhm ⟩
  fsimp at hhm
  have _ : hash_mod.val < alloc.vec.Vec.length hm.slots := by
    scalar_tac
  progress as ⟨ l, h_leq ⟩
  have h_slot :
    slot_s_inv_hash hm.slots.length (hash_mod_key key hm.slots.length) l.v := by
    fsimp [inv, slots_t_inv] at hinv
    have h := (hinv.right.left hash_mod.val (by scalar_tac)).right
    fsimp [slot_t_inv, hhm] at h
    fsimp_all
  progress as ⟨ inserted, l0, _, _, _, _, hlen ⟩
  . fsimp [inv, slots_t_inv, slot_t_inv, slot_s_inv] at hinv
    have h := hinv.right.left hash_mod.val (by scalar_tac)
    fsimp [h, h_leq]
  rw [if_update_eq] -- TODO: necessary because we don't have a join
  -- TODO: progress to ...
  have hipost :
    ∃ i0, (if inserted = true then hm.num_entries + Usize.ofNat 1 else pure hm.num_entries) = ok i0 ∧
    i0.val = if inserted then hm.num_entries.val + 1 else hm.num_entries.val
    := by
    if inserted then
      fsimp [*]
      have hbounds : hm.num_entries.val + (Usize.ofNat 1).val ≤ Usize.max := by
        fsimp [lookup] at hnsat
        fsimp_all []
        scalar_tac
      progress as ⟨ z, hp ⟩
      fsimp [hp]
    else
      fsimp [*, Pure.pure]
  progress as ⟨ i0 ⟩
  -- TODO: hide the variables and only keep the props
  -- TODO: allow providing terms to progress to instantiate the meta variables
  -- which are not propositions

  -- The postcondition
  let nhm : HashMap α := {
      num_entries := i0,
      max_load_factor := hm.max_load_factor,
      max_load := hm.max_load,
      saturated := hm.saturated,
      slots := hm.slots.set hash_mod l0 }

  have _ :
    match hm.lookup key with
    | none => nhm.len_s = hm.len_s + 1
    | some _ => nhm.len_s = hm.len_s := by
    fsimp only [lookup, len_s, al_v, HashMap.v, slots_s_lookup] at *
    -- We have to do a case disjunction
    fsimp_all
    -- TODO: dependent rewrites
    have _ : key.val % hm.slots.val.length < (List.map AList.v hm.slots.val).length := by
      fsimp [*]
    split <;>
    rename_i heq <;>
    fsimp [heq] at hlen <;>
    -- TODO: canonize addition by default? We need a tactic to simplify arithmetic equalities
    -- with addition and substractions ((ℤ, +) is a group or something - there should exist a tactic
    -- somewhere in mathlib?)
    fsimp [List.length_flatten_set_as_int_eq, nhm, *]
    scalar_tac

  split_conjs
  . fsimp [inv] at *
    split_conjs
    . match h: lookup hm key with
      | none =>
        fsimp [h, lookup, nhm] at *
        fsimp_all
      | some _ =>
        fsimp_all [lookup, nhm]
    . fsimp [slots_t_inv, slot_t_inv] at *
      intro i _
      have _ := hinv.right.left i (by fsimp_all)
      -- We need a case disjunction
      cases h_ieq : key.val % List.length hm.slots.val == i <;> simp_all [slot_s_inv]
    . fsimp [hinv]
    . fsimp_all [frame_load, inv_base, inv_load]
  . simp_all [frame_slots_params]
  . fsimp [lookup] at *
    simp_all
  . fsimp [lookup] at *
    intro k hk
    -- We have to make a case disjunction: either the hashes are different,
    -- in which case we don't even lookup the same slots, or the hashes
    -- are the same, in which case we have to reason about what happens
    -- in one slot
    let k_hash_mod := k.val % hm.slots.length
    have _ : k_hash_mod < alloc.vec.Vec.length hm.slots := by scalar_tac
    cases h_hm: k_hash_mod == hash_mod.val <;> simp_all (config := {zetaDelta := true})

  fsimp_all [nhm]

private theorem slot_allP_not_key_lookup (slot : AList α) (h : slot.v.allP fun (k', _) => ¬k = k') :
  slot.lookup k = none := by
  induction slot <;> fsimp_all
  split <;> fsimp_all

@[progress]
theorem move_elements_from_list_spec
  {T : Type} (ntable : HashMap T) (slot : AList T)
  (hinv : ntable.inv)
  {l i : Nat} (hSlotInv : slot_t_inv l i slot)
  (hDisjoint1 : ∀ key v, ntable.lookup key = some v → slot.lookup key = none)
  (hDisjoint2 : ∀ key v, slot.lookup key = some v → ntable.lookup key = none)
  (hLen : ntable.al_v.length + slot.v.length ≤ Usize.max)
  :
  ∃ ntable1, ntable.move_elements_from_list slot = ok ntable1 ∧
  ntable1.inv ∧
  frame_slots_params ntable ntable1 ∧
  (∀ key v, ntable1.lookup key = some v → ntable.lookup key = some v ∨ slot.lookup key = some v) ∧
  (∀ key v, ntable.lookup key = some v → ntable1.lookup key = some v) ∧
  (∀ key v, slot.lookup key = some v → ntable1.lookup key = some v) ∧
  ntable1.al_v.length = ntable.al_v.length + slot.v.length
  := by
  unfold move_elements_from_list move_elements_from_list_loop
  cases slot; swap
  . fsimp [hinv, frame_slots_params]
  . rename_i key value slot1
    simp
    have hLookupKey : ntable.lookup key = none := by
      by_contra
      cases h: ntable.lookup key <;> fsimp_all
    have : ntable.lookup key = none → ntable.len_s < Usize.max := by fsimp_all; scalar_tac
    progress as ⟨ ntable1, _, _, hLookup11, hLookup12, hLength1 ⟩
    fsimp [hLookupKey] at hLength1
    have hTable1LookupImp : ∀ (key : Usize) (v : T), ntable1.lookup key = some v → slot1.lookup key = none := by
      intro key' v hLookup
      if h: key = key' then
        fsimp_all [slot_t_inv]
        apply slot_allP_not_key_lookup
        fsimp_all
      else
        fsimp_all
        cases h: ntable.lookup key' <;> simp_all [Aeneas.Simp.neq_imp]
        have := hDisjoint1 _ _ h
        split at this <;> simp_all
    have hSlot1LookupImp : ∀ (key : Usize) (v : T), slot1.lookup key = some v → ntable1.lookup key = none := by
      intro key' v hLookup
      if h: key' = key then
        by_contra
        rename _ => hNtable1NotNone
        cases h: ntable1.lookup key' <;> fsimp [h] at hNtable1NotNone
        have := hTable1LookupImp _ _ h
        fsimp_all
      else
        have := hLookup12 key' h
        have := hDisjoint2 key' v
        simp at this; split at this <;> fsimp_all
    have : slot_t_inv l i slot1 := by
      fsimp [slot_t_inv] at hSlotInv
      fsimp [slot_t_inv, hSlotInv]
    progress as ⟨ ntable2, hInv2, _, hLookup21, hLookup22, hLookup23, hLen1 ⟩ -- TODO: allow progress to receive instantiation hints

    -- The conclusion
    -- TODO: use aesop here
    split_conjs
    . fsimp [*]
    . simp_all [frame_slots_params]
    . intro key' v hLookup
      have := hLookup21 key' v
      if h: key = key' then
        have := hLookup22 key' v
        have := hLookup23 key' v
        have := hDisjoint1 key' v
        have := hDisjoint2 key' v
        have := hTable1LookupImp key' v
        have := hSlot1LookupImp key' v
        fsimp_all [Slots.lookup]
      else
        have := hLookup12 key'
        split <;>
        simp_all [Aeneas.Simp.neq_imp]
    . intro key' v hLookup1
      if h: key' = key then
        simp_all
      else
        have := hLookup12 key' h
        have := hLookup22 key' v
        simp_all
    . intro key' v hLookup1
      if h: key' = key then
        have := hLookup22 key' v
        fsimp_all
      else
        have := hLookup23 key' v
        split at hLookup1 <;>
        fsimp_all
    . scalar_tac

private theorem slots_forall_nil_imp_lookup_none (slots : Slots T) (hLen : slots.val.length ≠ 0)
  (hEmpty : ∀ (j : Nat), j < slots.val.length → slots[j]! = AList.Nil) :
  ∀ key, slots.lookup key = none := by
  intro key
  fsimp [Slots.lookup]
  -- TODO: simplify
  have : key.val % slots.val.length < slots.val.length := by scalar_tac
  have := hEmpty (key.val % slots.val.length) (by fsimp [*])
  fsimp at *
  fsimp [*]

private theorem slots_index_len_le_flatten_len
  (slots : List (AList α)) (i : Nat) (h : i < slots.length) :
  (slots[i]!).length ≤ (List.map AList.v slots).flatten.length := by
  match slots with
  | [] =>
    fsimp at *
  | slot :: slots' =>
    fsimp at *
    if hi : i = 0 then
      fsimp_all
    else
      have := slots_index_len_le_flatten_len slots' (i - 1) (by scalar_tac)
      fsimp [*]
      scalar_tac

/- If we successfully lookup a key from a slot, the hash of the key modulo the number of slots must
   be equal to the slot index.
   TODO: remove?
 -/
private theorem slots_inv_lookup_imp_eq (slots : Slots α) (hInv : slots_t_inv slots)
  (i : Nat) (hi : i < slots.val.length) (key : Usize) :
  (slots[i]!).lookup key ≠ none → i = key.val % slots.val.length := by
  suffices hSlot : ∀ (slot : List (Usize × α)),
           slot_s_inv slots.val.length i slot →
           slot.lookup key ≠ none →
           i = key.val % slots.val.length
  from by
    rw [slots_t_inv, slots_s_inv] at hInv
    replace hInv := hInv i hi
    fsimp [slot_t_inv] at hInv
    have := hSlot _ hInv
    apply this
  intro slot
  induction slot <;> fsimp_all
  intros; fsimp_all
  split at * <;> fsimp_all

private theorem move_slots_updated_table_lookup_imp
  (i : Nat)
  (ntable ntable1 ntable2 : HashMap α) (slots slots1 : Slots α) (slot : AList α)
  (hi : i < slots.val.length)
  (hSlotsInv : slots_t_inv slots)
  (hSlotEq : slot = slots[i]!)
  (hSlotsEq : slots1.val = slots.val.set i .Nil)
  (hTableLookup : ∀ (key : Usize) (v : α), ntable1.lookup key = some v →
                    ntable.lookup key = some v ∨ slot.lookup key = some v)
  (hTable1Lookup : ∀ (key : Usize) (v : α), ntable2.lookup key = some v →
                    ntable1.lookup key = some v ∨ Slots.lookup slots1 key = some v)
  :
  ∀ key v, ntable2.lookup key = some v → ntable.lookup key = some v ∨ slots.lookup key = some v := by
  intro key v hLookup
  replace hTableLookup := hTableLookup key v
  replace hTable1Lookup := hTable1Lookup key v hLookup
  cases hTable1Lookup with
  | inl hTable1Lookup =>
    replace hTableLookup := hTableLookup hTable1Lookup
    cases hTableLookup <;> try fsimp [*]
    right
    have := slots_inv_lookup_imp_eq slots hSlotsInv i hi key (by fsimp_all)
    fsimp_all [Slots.lookup]
  | inr hTable1Lookup =>
    right
    -- The key can't be for the slot we replaced
    cases heq : key.val % slots.val.length == i <;> fsimp_all [Slots.lookup]

private theorem move_one_slot_lookup_equiv {α : Type} (ntable ntable1 ntable2 : HashMap α)
  (slot : AList α)
  (slots slots1 : Slots α)
  (i : Nat)
  (hSlotEq : slot = slots[i]!)
  (hSlots1Eq : slots1.val = slots.val.set i .Nil)
  (hLookup1 : ∀ (key : Usize) (v : α), ntable.lookup key = some v → ntable1.lookup key = some v)
  (hLookup2 : ∀ (key : Usize) (v : α), slot.lookup key = some v → ntable1.lookup key = some v)
  (hLookup3 : ∀ (key : Usize) (v : α), ntable1.lookup key = some v → ntable2.lookup key = some v)
  (hLookup4 : ∀ (key : Usize) (v : α), slots1.lookup key = some v → ntable2.lookup key = some v) :
  (∀ key v, slots.lookup key = some v → ntable2.lookup key = some v) ∧
  (∀ key v, ntable.lookup key = some v → ntable2.lookup key = some v) := by
  constructor <;> intro key v hLookup
  . if hi: key.val % slots.val.length = i then
      -- We lookup in slot
      have := hLookup2 key v
      fsimp_all [Slots.lookup]
      have := hLookup3 key v
      simp_all

    else
      -- We lookup in slots
      have := hLookup4 key v
      simp_all [Slots.lookup]
  . have := hLookup1 key v
    have := hLookup3 key v
    simp_all

private theorem slots_lookup_none_imp_slot_lookup_none
  (slots : Slots α) (hInv : slots_t_inv slots) (i : Nat) (hi : i < slots.val.length) :
  ∀ (key : Usize), slots.lookup key = none → (slots[i]!).lookup key = none := by
  intro key hLookup
  if heq : key.val % slots.val.length = i then
    fsimp_all [Slots.lookup]
  else
    have := slots_inv_lookup_imp_eq slots hInv i (by scalar_tac) key
    by_contra
    fsimp_all

private theorem slot_lookup_not_none_imp_slots_lookup_not_none
  (slots : Slots α) (hInv : slots_t_inv slots) (i : Nat) (hi : i < slots.val.length) :
  ∀ (key : Usize), (slots[i]!).lookup key ≠ none → slots.lookup key ≠ none := by
  intro key hLookup hNone
  have := slots_lookup_none_imp_slot_lookup_none slots hInv i hi key hNone
  apply hLookup this

private theorem slots_forall_nil_imp_al_v_nil
  (slots : Slots α)
  (hEmpty : ∀ (i : Nat), i < slots.val.length → slots[i]! = AList.Nil) :
  slots.al_v = [] := by
  suffices h :
    ∀ (slots : List (AList α)),
      (∀ (i : Nat), i < slots.length → slots[i]! = Nil) →
      (slots.map AList.v).flatten = [] from by
      replace h := h slots.val (by intro i h0; exact hEmpty i h0)
      fsimp_all
  clear slots hEmpty
  intro slots hEmpty
  induction slots <;> fsimp_all
  have hHead := hEmpty 0 (by scalar_tac)
  fsimp at hHead
  fsimp [hHead]
  rename (_ → _) => ih
  apply ih; intro i h0
  replace hEmpty := hEmpty (i + 1) (by omega)
  -- TODO: fsimp at hEmpty
  have : 0 < i + 1 := by omega
  fsimp_all

theorem move_elements_loop_spec
  {α : Type} (ntable : HashMap α) (slots : Slots α)
  (i : Usize)
  (hi : i ≤ alloc.vec.Vec.len slots)
  (hinv : ntable.inv)
  (hSlotsNonZero : slots.val.length ≠ 0)
  (hSlotsInv : slots_t_inv slots)
  (hEmpty : ∀ j, j < i.val → slots[j]! = AList.Nil)
  (hDisjoint1 : ∀ key v, ntable.lookup key = some v → slots.lookup key = none)
  (hLen : ntable.al_v.length + slots.al_v.length ≤ Usize.max)
  :
  ∃ ntable1 slots1, ntable.move_elements_loop slots i = ok (ntable1, slots1) ∧
  ntable1.inv ∧
  frame_slots_params ntable ntable1 ∧
  ntable1.al_v.length = ntable.al_v.length + slots.al_v.length ∧
  (∀ key v, ntable1.lookup key = some v → ntable.lookup key = some v ∨ slots.lookup key = some v) ∧
  (∀ key v, slots.lookup key = some v → ntable1.lookup key = some v) ∧
  (∀ key v, ntable.lookup key = some v → ntable1.lookup key = some v) ∧
  (∀ (j : Nat), j < slots1.length → slots1[j]! = AList.Nil)
  := by
  unfold move_elements_loop
  simp
  dcases hi: i.val < slots.val.length
  . -- Continue the proof
    have hIneq : i.val < slots.val.length := by scalar_tac
    fsimp [hi]
    progress as ⟨ slot, hSlotEq ⟩
    have hInvSlot : slot_t_inv slots.val.length i.val slot := by
      fsimp [slots_t_inv] at hSlotsInv
      fsimp [*]

    have ntableLookupImpSlot :
      ∀ (key : Usize) (v : α), ntable.lookup key = some v → slot.lookup key = none := by
      intro key v hLookup
      by_contra
      have : i.val = key.val % slots.val.length := by
        have := slots_inv_lookup_imp_eq slots hSlotsInv i.val (by scalar_tac) key
        fsimp_all
      cases h: slot.lookup key <;> fsimp_all

    have : ntable.al_v.length + slot.v.length ≤ Usize.max := by
      have := slots_index_len_le_flatten_len slots.val i.val (by scalar_tac)
      fsimp_all [Slots.al_v]; scalar_tac
    progress as ⟨ ntable1, _, _, hDisjointNtable1, hLookup11, hLookup12, hLen1 ⟩
    . intro key v hLookup
      by_contra
      cases h : ntable.lookup key <;> fsimp_all

    progress as ⟨ i' ⟩
    have : i' ≤ alloc.vec.Vec.len (alloc.vec.Vec.set slots i Nil) := by
      fsimp_all [alloc.vec.Vec.len]; scalar_tac
    have : slots_t_inv (alloc.vec.Vec.set slots i Nil) := by
      fsimp [slots_t_inv] at *
      intro j h0
      cases h: j == i.val <;> simp_all

    have ntable1LookupImpSlots1 :
      ∀ (key : Usize) (v : α), ntable1.lookup key = some v →
      Slots.lookup (alloc.vec.Vec.set slots i Nil) key = none := by
      intro key v hLookup
      cases hDisjointNtable1 _ _ hLookup with
      | inl h =>
        have := ntableLookupImpSlot _ _ h
        have := hDisjoint1 _ _ h
        cases heq : i.val == key.val % slots.val.length <;> fsimp_all [Slots.lookup]
      | inr h =>
        have heq : i = key.val % slots.val.length := by
          have := slots_inv_lookup_imp_eq slots hSlotsInv i.val (by scalar_tac) key (by fsimp_all [Slots.lookup])
          scalar_tac
        simp_all [Slots.lookup]

    progress as ⟨ ntable2, slots2, _, _, _, hLookup2Rev, hLookup21, hLookup22, hIndexNil ⟩
    . intro j h0
      if h : j = i.val then
        simp_all
      else
        have := hEmpty j (by scalar_tac)
        fsimp_all
    . have : i.val < (List.map AList.v slots.val).length := by simp; scalar_tac
      simp_all [Slots.al_v, List.length_flatten_set_as_int_eq]
      scalar_tac

    simp
    have hLookupPreserve :
      (∀ key v, slots.lookup key = some v → ntable2.lookup key = some v) ∧
      (∀ key v, ntable.lookup key = some v → ntable2.lookup key = some v) := by
      exact move_one_slot_lookup_equiv ntable ntable1 ntable2 slot slots
        (alloc.vec.Vec.set slots i Nil) i.val
        (by assumption) (by simp)
        (by assumption) (by assumption) (by assumption) (by assumption)

    split_conjs
    . fsimp [*]
    . fsimp_all [frame_slots_params]
    . fsimp_all [Slots.al_v]
      -- TODO
      scalar_tac_preprocess
      have : i.val < slots.length := by scalar_tac
      simp_all [List.length_flatten_set_as_int_eq]
      scalar_tac
    . intro key v hLookup
      apply move_slots_updated_table_lookup_imp i.val ntable ntable1 ntable2 slots (alloc.vec.Vec.set slots i Nil) slot (by scalar_tac) <;>
      first | assumption | simp
    . apply hLookupPreserve.left
    . apply hLookupPreserve.right
    . intro j h0
      apply hIndexNil j h0
  . fsimp [hi, *]
    -- TODO: fsimp_all removes hEmpty!!
    have hi : i = alloc.vec.Vec.len slots := by scalar_tac
    have hEmpty : ∀ (j : Nat), j < slots.val.length → slots[j]! = AList.Nil := by
      fsimp [hi] at hEmpty
      exact hEmpty
    have hNil : slots.al_v = [] := slots_forall_nil_imp_al_v_nil slots hEmpty
    have hLenNonZero : slots.val.length ≠ 0 := by fsimp [*]
    have hLookupEmpty := slots_forall_nil_imp_lookup_none slots hLenNonZero hEmpty
    fsimp [hNil, hLookupEmpty, frame_slots_params]
    split_conjs
    . intros
      fsimp [*]
    . intros
      simp_all
    . apply hEmpty
termination_by slots.val.length - i.val
decreasing_by scalar_decr_tac

@[progress]
theorem move_elements_spec
  {α : Type} (ntable : HashMap α) (slots : Slots α)
  (hinv : ntable.inv)
  (hslotsNempty : 0 < slots.val.length)
  (hSlotsInv : slots_t_inv slots)
  -- The initial table is empty
  (hEmpty : ∀ key, ntable.lookup key = none)
  (hTableLen : ntable.al_v.length = 0)
  (hSlotsLen : slots.al_v.length ≤ Usize.max)
  :
  ∃ ntable1 slots1, ntable.move_elements slots = ok (ntable1, slots1) ∧
  ntable1.inv ∧
  frame_slots_params ntable ntable1 ∧
  ntable1.al_v.length = ntable.al_v.length + slots.al_v.length ∧
  (∀ key v, ntable1.lookup key = some v ↔ slots.lookup key = some v)
  := by
  unfold move_elements
  progress with move_elements_loop_spec as ⟨ ntable1, slots1, _, _, _, ntable1Lookup, slotsLookup ⟩
  fsimp
  have : frame_slots_params ntable ntable1 := by
    simp_all [frame_slots_params]
  split_conjs <;> try assumption
  --
  intro key v
  have := ntable1Lookup key v
  have := slotsLookup key v
  constructor <;> fsimp_all

@[progress]
theorem try_resize_spec {α : Type} (hm : HashMap α) (hInv : hm.inv):
  ∃ hm', hm.try_resize = ok hm' ∧
  hm'.inv ∧
  (∀ key, hm'.lookup key = hm.lookup key) ∧
  hm'.al_v.length = hm.al_v.length := by
  unfold try_resize
  simp
  progress as ⟨ n1 ⟩ -- TODO: simplify (Usize.ofInt (OfNat.ofNat 2) try_resize.proof_1).val
  have : hm.2.1.val ≠ 0 := by
    fsimp [inv, inv_load] at hInv
    -- TODO: why does hm.max_load_factor appears as hm.2??
    -- Can we deactivate field notations?
    omega
  progress as ⟨ n2 ⟩
  if hSmaller : hm.slots.val.length ≤ n2.val then
    fsimp [hSmaller]
    have : (alloc.vec.Vec.len hm.slots).val * 2 ≤ Usize.max := by
          fsimp [alloc.vec.Vec.len, inv, inv_load] at *
          -- TODO: this should be automated
          have hIneq1 : n1.val ≤ Usize.max / 2 := by fsimp [*]
          fsimp [Int.le_ediv_iff_mul_le] at hIneq1
          -- TODO: this should be automated
          have hIneq2 : n2.val ≤ n1.val / hm.2.1.val := by fsimp [*]
          rw [Nat.le_div_iff_mul_le] at hIneq2 <;> try fsimp [*]
          have : n2.val * 1 ≤ n2.val * hm.max_load_factor.1.val := by
            apply Nat.mul_le_mul <;> scalar_tac
          scalar_tac
    progress as ⟨ newLength ⟩
    have : 0 < newLength.val := by
      fsimp_all [inv, inv_load]
    progress as ⟨ ntable1 ⟩ -- TODO: introduce nice notation to take care of preconditions
    . -- Pre 1
      fsimp_all [inv, inv_load]
      split_conjs at hInv
      --
      apply Nat.mul_le_of_le_div at hSmaller; try fsimp [*]
      apply Nat.mul_le_of_le_div at hSmaller; try simp
      --
      have : (hm.slots.val.length * hm.2.1.val) * 1 ≤ (hm.slots.val.length * hm.2.1.val) * 2 := by
        apply Nat.mul_le_mul <;> (try fsimp [*])
      --
      ring_nf at *
      scalar_tac
    . -- Pre 2
      fsimp_all [inv, inv_load]
      unfold max_load_factor at * -- TODO: this is really annoying
      omega
    . -- End of the proof
      have : slots_t_inv hm.slots := by fsimp_all [inv] -- TODO
      have : (Slots.al_v hm.slots).length ≤ Usize.max := by fsimp_all [inv, al_v, v, Slots.al_v]; scalar_tac
      progress as ⟨ ntable2, slots1, _, _, _, hLookup ⟩ -- TODO: assumption is not powerful enough
      fsimp_all [lookup, al_v, v, alloc.vec.Vec.len]
      split_conjs
      . fsimp_all [inv, al_v, HashMap.v]
        -- load invariant
        simp_all [inv_load, frame_slots_params]
      . intro key
        replace hLookup := hLookup key
        cases h1: (ntable2.slots.val[key.val % ntable2.slots.val.length]!).v.lookup key <;>
        cases h2: (hm.slots.val[key.val % hm.slots.val.length]!).v.lookup key <;>
        fsimp_all [Slots.lookup]
  else
    fsimp [hSmaller]
    tauto

@[progress]
theorem insert_spec {α} (hm : HashMap α) (key : Usize) (value : α)
  (hInv : hm.inv)
  (hNotSat : hm.lookup key = none → hm.len_s < Usize.max) :
  ∃ hm1, insert hm key value = ok hm1 ∧
  hm1.inv ∧
  --
  hm1.lookup key = value ∧
  (∀ key', key' ≠ key → hm1.lookup key' = hm.lookup key') ∧
  --
  match hm.lookup key with
  | none => hm1.len_s = hm.len_s + 1
  | some _ => hm1.len_s = hm.len_s
  := by
  unfold insert
  progress as ⟨ hm1 ⟩
  fsimp [len]
  split
  . split
    . fsimp_all
    . progress as ⟨ hm2 ⟩
      fsimp_all
  . fsimp_all

@[progress]
theorem get_in_list_spec {α} (key : Usize) (slot : AList α) :
  ∃ opt_v, get_in_list key slot = ok opt_v ∧ slot.lookup key = opt_v := by
  induction slot <;>
  unfold get_in_list get_in_list_loop <;>
  fsimp_all
  split <;> fsimp_all
  split <;> fsimp_all

@[progress]
theorem get_spec {α} (hm : HashMap α) (key : Usize) (hInv : hm.inv) :
  ∃ opt_v, get hm key = ok opt_v ∧ hm.lookup key = opt_v := by
  unfold get
  fsimp [hash_key, alloc.vec.Vec.len]
  progress as ⟨ hash_mod ⟩ -- TODO: decompose post by default
  fsimp at *
  have : hash_mod.val < hm.slots.length := by scalar_tac
  progress as ⟨ slot ⟩
  progress as ⟨ v ⟩
  fsimp_all [lookup]

@[progress]
theorem get_mut_in_list_spec {α} (key : Usize) (slot : AList α)
  {l i : Nat}
  (hInv : slot_t_inv l i slot) :
  ∃ opt_v back, get_mut_in_list slot key = ok (opt_v, back) ∧
  slot.lookup key = opt_v ∧
  -- Backward function
  -- case: none
  (opt_v = none → back none = slot) ∧
  -- case: some
  (∀ v v',
   opt_v = some v →
   let slot' := back (some v')
   slot_t_inv l i slot' ∧
   slot'.lookup key = v' ∧
   (∀ key', key' ≠ key → slot'.lookup key' = slot.lookup key') ∧
   -- We need this strong post-condition for the recursive case
   (∀ key', slot.v.allP (fun x => key' ≠ x.1) → slot'.v.allP (fun x => key' ≠ x.1)))
   := by
  induction slot <;>
  unfold get_mut_in_list get_mut_in_list_loop
  split
  . -- Non-recursive case
    fsimp_all [slot_t_inv]
    intros
    split <;> fsimp_all
  . -- Recursive case
    -- TODO: progress by
    progress as ⟨ opt_v, back, _, hbackNone, hBackSome ⟩
    . fsimp_all [slot_t_inv]
    . simp [*]
      -- Proving the post-condition about back
      -- Case disjunction on v
      split_conjs
      . split <;> fsimp_all
      . grind
      . intro v v' heq
        have h := hBackSome v v'
        split_conjs
        . fsimp_all [slot_t_inv, slot_s_inv, slot_s_inv_hash]
        . split <;> fsimp_all
        . fsimp_all
        . fsimp_all
  . fsimp_all

@[progress]
theorem get_mut_spec {α} (hm : HashMap α) (key : Usize) (hInv : hm.inv) :
  ∃ opt_v back, get_mut hm key = ok (opt_v, back) ∧
  hm.lookup key = opt_v ∧
  -- Backward function
  -- case none:
  (opt_v = none → back none = hm) ∧
  -- case some:
  (∀ v v',
    opt_v = some v →
    let hm' := back (some v')
    hm'.lookup key = some v' ∧
    ∀ key', key' ≠ key → hm'.lookup key' = hm.lookup key')
   := by
  unfold get_mut
  fsimp [hash_key, alloc.vec.Vec.len]
  progress as ⟨ hash_mod ⟩
  fsimp at *
  have : hash_mod.val < hm.slots.val.length ∧ hash_mod.val < hm.slots.val.length := by scalar_tac
  progress as ⟨ slot, index_back ⟩
  have : slot_t_inv hm.slots.val.length hash_mod slot := by
    fsimp_all [inv, slots_t_inv]
  progress as ⟨ opt_v, back, _, hBackNone, hBackSome ⟩
  fsimp [lookup, *]
  constructor
  . fsimp_all [lookup]
  . -- Backward function
    split_conjs
    . -- case: none
      intro hEq
      simp_all
      -- TODO: tactic to automate this
      have hSlotsEq :
        hm.slots.set hash_mod ((hm.slots.val)[(key.val % (hm.slots.val).length)]!) = hm.slots := by
        simp_all [alloc.vec.Vec.set]
      fsimp [hSlotsEq]
    . -- case: some
      grind

@[progress]
theorem remove_from_list_spec {α} (key : Usize) (slot : AList α) {l i} (hInv : slot_t_inv l i slot) :
  ∃ v slot', remove_from_list key slot = ok (v, slot') ∧
  slot.lookup key = v ∧
  slot'.lookup key = none ∧
  (∀ key', key' ≠ key → slot'.lookup key' = slot.lookup key') ∧
  match v with
  | none => slot'.v.length = slot.v.length
  | some _ => slot'.v.length + 1 = slot.v.length := by
  unfold remove_from_list remove_from_list_loop
  match hEq : slot with
  | .Nil =>
    simp
  | .Cons k v0 tl =>
    simp
    if hKey : k = key then
      fsimp [hKey]
      fsimp_all [slot_t_inv, slot_s_inv]
      split_conjs
      . apply slot_allP_not_key_lookup
        fsimp [*]
      . intros; split <;> fsimp_all
    else
      fsimp [hKey]
      have hInv' : slot_t_inv l i tl := by fsimp_all [slot_t_inv]
      progress as ⟨ v1, tl1, _, _, hLookupTl1, _ ⟩
      simp [*]
      split <;> fsimp_all

private theorem lookup_not_none_imp_len_s_pos (hm : HashMap α) (key : Usize) (hLookup : hm.lookup key ≠ none)
  (hNotEmpty : 0 < hm.slots.val.length) :
  0 < hm.len_s := by
  -- TODO: simplify
  have : key.val % hm.slots.val.length < hm.slots.val.length := by scalar_tac
  have := List.length_getElem!_le_length_flatten hm.v (key.val % hm.slots.val.length)
  have := List.lookup_not_none_imp_length_pos (hm.slots.val[key.val % hm.slots.val.length]!).v key
  simp_all [lookup, len_s, al_v, v]
  scalar_tac

@[progress]
theorem remove_spec {α} (hm : HashMap α) (key : Usize) (hInv : hm.inv) :
  ∃ v hm', remove hm key = ok (v, hm') ∧
  hm.lookup key = v ∧
  hm'.lookup key = none ∧
  (∀ key', key' ≠ key → hm'.lookup key' = hm.lookup key') ∧
  match v with
  | none => hm'.len_s = hm.len_s
  | some _ => hm'.len_s = hm.len_s - 1 := by
  unfold remove
  fsimp [hash_key, alloc.vec.Vec.len]
  progress as ⟨ hash_mod ⟩ -- TODO: decompose post by default
  fsimp at *
  -- TODO: simplify
  have : hash_mod.val < hm.slots.val.length := by scalar_tac
  progress as ⟨ slot, index_back ⟩
  have : slot_t_inv hm.slots.val.length hash_mod slot := by
    fsimp_all [inv, slots_t_inv]
  progress as ⟨ vOpt, slot' ⟩
  cases hOpt : vOpt
  . fsimp [*]
    fsimp [lookup, *]
    simp_all [al_v, v]
    split_conjs
    . intro key' hNotEq
      -- We need to make a case disjunction
      have : key' % hm.slots.val.length < hm.slots.val.length := by scalar_tac
      cases h: key.val % hm.slots.val.length == key'.val % hm.slots.val.length <;>
      fsimp_all
    . -- TODO
      scalar_tac_preprocess
      fsimp_all
      omega
  . rename_i v
    fsimp [*]
    have : 0 < hm.num_entries.val := by
      have := lookup_not_none_imp_len_s_pos hm key (by fsimp_all [lookup]) (by fsimp_all [inv])
      fsimp_all [inv]
    progress as ⟨ newSize ⟩
    simp_all [lookup, al_v, HashMap.v]
    constructor
    . intro key' hNotEq
      have : key' % hm.slots.val.length < hm.slots.val.length := by scalar_tac
      cases h: key.val % hm.slots.val.length == key'.val % hm.slots.val.length <;>
      fsimp_all
    . simp_all [List.length_flatten_set_as_int_eq]
      scalar_tac

end HashMap

end hashmap
