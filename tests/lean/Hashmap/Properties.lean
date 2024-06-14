import Hashmap.Funs
import Mathlib.Tactic.Ring.RingNF

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

@[simp]
def v {α : Type} (ls: AList α) : _root_.List (Usize × α) :=
  match ls with
  | Nil => []
  | Cons k x tl => (k, x) :: v tl

--@[simp] theorem v_nil (α : Type) : (Nil : AList α).v = [] := by rfl
--@[simp] theorem v_cons {α : Type} k x (tl: AList α) : (Cons k x tl).v = (k, x) :: v tl := by rfl

@[simp]
abbrev lookup {α : Type} (ls: AList α) (key: Usize) : Option α :=
  ls.v.lookup' key

@[simp]
abbrev len {α : Type} (ls : AList α) : Int := ls.v.len

instance : Inhabited (AList α) where
  default := .Nil

end AList

-- TODO: move
-- TODO: remove?
@[simp] theorem neq_imp_nbeq [BEq α] [LawfulBEq α] (x y : α) (heq : ¬ x = y) : ¬ x == y := by simp [*]
@[simp] theorem neq_imp_nbeq_rev [BEq α] [LawfulBEq α] (x y : α) (heq : ¬ x = y) : ¬ y == x := by simp [*]

def distinct_keys (ls : List (Usize × α)) := ls.pairwise_rel (λ x y => x.fst ≠ y.fst)

@[simp]
theorem distinct_keys_nil : @distinct_keys α [] := by simp [distinct_keys]

@[simp]
theorem distinct_keys_cons {k : Usize} (v : α) :
  distinct_keys ((k, v) :: tl) ↔ (distinct_keys tl ∧ tl.allP (fun (k', _) => k ≠ k')) := by
  simp [distinct_keys, List.pairwise_rel]
  tauto

def hash_mod_key (k : Usize) (l : Int) : Int :=
  match hash_key k with
  | .ok k => k.val % l
  | _ => 0

@[simp]
theorem hash_mod_key_eq : hash_mod_key k l = k.val % l := by
  simp [hash_mod_key, hash_key]

def slot_s_inv (l i : Int) (ls : List (Usize × α)) : Prop :=
  ls.allP (λ (k, _) => hash_mod_key k l = i)

@[simp]
def slot_s_inv (l i : Int) (ls : List (Usize × α)) : Prop :=
  distinct_keys ls ∧
  slot_s_inv l i ls

def slots_s_inv (s : List (List (Usize × α))) : Prop :=
  ∀ (i : Int), 0 ≤ i → i < s.len → slot_s_inv s.len i (s.index i)

--def slot_t_inv (l i : Int) (s : AList α) : Prop := slot_s_inv l i s.v

abbrev Slots α := alloc.vec.Vec (AList α)
abbrev Spec.Slots α := List (List (Usize × α))

@[simp] -- TODO: redcible doesn't work
def Slots.v (s : Slots α) := s.val.map AList.v

@[simp]
def Spec.Slots.lookup (s : Spec.Slots α) (k : Usize) : Option α :=
  let i := hash_mod_key k s.len
  let slot := s.index i
  slot.lookup k

structure Spec.HashMap (T : Type) where
  slots : List (List (Usize × T))
  num_entries : Int

abbrev HashMap.v {α : Type} (hm : HashMap α) : Spec.HashMap α :=
  { slots := Slots.v hm.slots,
    num_entries := hm.num_entries.val }

def Spec.HashMap.lookup (hm : Spec.HashMap α) (k : Usize) : Option α :=
  Spec.Slots.lookup hm.slots k

--instance Membership 

/-instance : Coe (Slots α) (Spec.Slots α) where
  coe := λ v => v.v -/

instance : Coe (HashMap α) (Spec.HashMap α) where
  coe := λ v => v.v

instance : Membership Usize (Spec.HashMap α) where
  mem k hm := hm.lookup k ≠ none

instance : Membership Usize (HashMap α) where
  mem k hm := k ∈ hm.v

/- Activate the ↑ notation -/
attribute [coe] HashMap.v

def Spec.HashMap.inv (hm : Spec.HashMap α) : Prop :=
  -- [num_entries] correctly tracks the number of entries
  hm.num_entries = hm.slots.flatten.len ∧
  -- Slots invariant
  slots_s_inv hm.slots ∧
  -- The capacity must be > 0 (otherwise we can't resize)
  0 < hm.slots.len
  -- TODO: load computation

def HashMap.inv (hm : HashMap α) : Prop :=
  hm.v.inv

@[simp]
theorem HashMap.v_slots_v_eq (hm : HashMap α) : hm.v.slots = Slots.v hm.slots := by
  cases hm; simp

-- This rewriting lemma is problematic below
attribute [-simp] Bool.exists_bool

-- The proofs below are a bit expensive, so we need to increase the maximum number
-- of heart beats
set_option maxHeartbeats 1000000

def Spec.HashMap.insert_in_list
  {T : Type} (key : Usize) (value : T) (ls : List (Usize × T)) :
  Bool × (List (Usize × T))
  :=
  match ls with
  | (ckey, cvalue) :: tl =>
    if ckey = key
    then (false, (ckey, value) :: tl)
    else
      let (b, tl1) := insert_in_list key value tl
      (b, (ckey, cvalue) :: tl1)
  | [] => (true, [(key, value)])

@[pspec]
theorem HashMap.insert_in_list_spec {α : Type} (key: Usize) (value: α) (l0: AList α) :
  ∃ b l1,
    HashMap.insert_in_list α key value l0 = ok (b, l1) ∧
    (b, l1.v) = Spec.HashMap.insert_in_list key value l0.v
  := by
  simp [insert_in_list]
  rw [insert_in_list_loop]    
  cases l0 with
  | Nil =>
    exists true -- TODO: why do we need to do this?
    simp (config := {contextual := true})
      [AList.v, slot_s_inv, distinct_keys, List.pairwise_rel, Spec.HashMap.insert_in_list]
  | Cons k v tl0 =>
     cases h: k == key with
     | true =>
       simp at h; simp [h]
       exists false; simp -- TODO: why do we need to do this?
       simp [Spec.HashMap.insert_in_list]
     | false =>
       simp at h; simp [h]
       progress keep heq as ⟨ b, tl1, hpost ⟩
       simp only [insert_in_list] at heq
       simp [heq]
       exists b
       simp [Spec.HashMap.insert_in_list, *]
       rw [← hpost]
       simp

/-
theorem Spec.insert_in_list_spec_aux {α : Type} (l : Int) (key: Usize) (value: α)
  (l0: List (Usize × α))
  (hinv : slot_s_inv l (hash_mod_key key l) l0)
  (hdk : distinct_keys l0) :
  let (b, l1) := insert_in_list key value l0
  -- The boolean is true ↔ we inserted a new binding
  (b ↔ (l0.lookup key = none)) ∧
  -- We update the binding
  l1.lookup key = value ∧
  (∀ k, k ≠ key → l1.lookup k = l0.lookup k) ∧
  -- We preserve part of the key invariant
  slot_s_inv l (hash_mod_key key l) l1 ∧
  -- Reasoning about the length
  (match l0.lookup key with
   | none => l1.len = l0.len + 1
   | some _ => l1.len = l0.len) ∧
  -- The keys are distinct
  distinct_keys l1 ∧
  -- We need this auxiliary property to prove that the keys distinct properties is preserved
  (∀ k, k ≠ key → l0.allP (λ (k1, _) => k ≠ k1) → l1.allP (λ (k1, _) => k ≠ k1))
  := by
  cases l0 with
  | nil =>
    simp (config := {contextual := true})
      [insert_in_list, slot_s_inv, distinct_keys, List.pairwise_rel, List.lookup]
  | cons kv tl0 =>
    cases kv with
    | mk k v =>
      simp [insert_in_list]
      cases h: k == key with
      | true =>
        simp at h; simp [h]
        split_conjs
        . intros; simp [List.lookup, *]
        . simp [AList.v, slot_s_inv] at *
          simp [*]
        . simp [*, distinct_keys] at *
          apply hdk
        . tauto
      | false =>
        simp at h; simp [h]
        have : slot_s_inv l (hash_mod_key key l) tl0 := by simp_all [AList.v, slot_s_inv]
        have : distinct_keys tl0 := by
          simp [distinct_keys] at hdk
          simp [hdk, distinct_keys]
        have ⟨ hInd0, hInd1, hInd2, hInd3, hInd4, hInd5, hInd6 ⟩ :=
          insert_in_list_spec_aux l key value tl0 (by assumption) (by assumption)
        simp at hInd6
        have : slot_s_inv l (↑key % l) ((k, v) :: (insert_in_list key value tl0).2) := by
          simp [hash_mod_key, hash_key, slot_s_inv] at *
          simp [*]
        have : distinct_keys ((k, v) :: (insert_in_list key value tl0).2) := by
          simp [distinct_keys] at *
          simp [*]
        split_conjs
        . simp [List.lookup, *]
        . simp [List.lookup, *]
        . simp (config := {contextual := true}) [List.lookup, *]
        . assumption
        . -- TODO: canonize addition by default?
          simp_all [List.lookup, Int.add_assoc, Int.add_comm, Int.add_left_comm]
        . assumption
        . tauto
-/

/- The boolean is true ↔ we inserted a new binding -/
theorem Spec.HashMap.insert_in_list_inserted {α : Type}
  (key: Usize) (value: α) (l0: List (Usize × α)) :
  let (b, _) := insert_in_list key value l0
  (b ↔ (l0.lookup key = none))
  := by
  induction l0 using insert_in_list.induct key value <;>
  simp_all [insert_in_list, List.lookup]

/- We updated the binding -/
theorem Spec.HashMap.insert_in_list_lookup {α : Type}
  (key: Usize) (value: α) (l0: List (Usize × α)) :
  let (_, l1) := insert_in_list key value l0
  l1.lookup key = value ∧
  (∀ k, k ≠ key → l1.lookup k = l0.lookup k)
  := by
  induction l0 using insert_in_list.induct key value <;>
  simp_all [insert_in_list, List.lookup]

/- The slots invariant is preserved -/
theorem Spec.HashMap.insert_in_list_slot_s_inv {α : Type}
  (key: Usize) (value: α) (l0: List (Usize × α))
  (len : Int)
  (hinv : slot_s_inv len (hash_mod_key key len) l0) :
  let (_, l1) := insert_in_list key value l0
  slot_s_inv len (hash_mod_key key len) l1
  := by
  induction l0 using insert_in_list.induct key value <;>
  simp_all [insert_in_list, slot_s_inv]

/- The keys remain distinct -/
theorem Spec.HashMap.insert_in_list_distinct_keys {α : Type}
  (key: Usize) (value: α) (l0: List (Usize × α))
  (h : distinct_keys l0) :
  let (_, l1) := insert_in_list key value l0
  distinct_keys l1
  := by
  suffices h :
    let (_, l1) := insert_in_list key value l0
    distinct_keys l1 ∧
    -- We need this auxiliary property to prove that the keys distinct properties is preserved
    (∀ k, k ≠ key → l0.allP (λ (k1, _) => k ≠ k1) → l1.allP (λ (k1, _) => k ≠ k1))
  by simp_all
  -- By induction
  induction l0 using insert_in_list.induct key value <;>
  simp_all [insert_in_list]

/- Reasoning about the length -/
theorem Spec.HashMap.insert_in_list_length {α : Type}
  (key: Usize) (value: α) (l0: List (Usize × α)) :
  let (_, l1) := insert_in_list key value l0
  match l0.lookup key with
  | none => l1.len = l0.len + 1
  | some _ => l1.len = l0.len
  := by
  -- By induction
  induction l0 using insert_in_list.induct key value <;>
  simp_all [insert_in_list, List.lookup]
  split <;> simp_all
  omega

def Spec.HashMap.insert_no_resize
  {T : Type} (self : Spec.HashMap T) (key : Usize) (value : T) :
  Spec.HashMap T
  :=
  let hash := key
  let i := self.slots.len
  let hash_mod := hash % i
  let slot := List.index self.slots hash_mod
  let (b, slot1) := insert_in_list key value slot
  if b then
    let num_entries := self.num_entries + 1
    let slots := List.update self.slots hash_mod slot1
    { self with slots, num_entries }
  else
    { self with slots := List.update self.slots hash_mod slot1}

-- TODO: move
@[simp]
theorem List.map_index [Inhabited α] [Inhabited β] (l : List α) (f : α → β) (i : Int) :
  (l.map f).index i = f (l.index i) := by sorry

@[simp]
theorem List.map_update (l : List α) (f : α → β) (i : Int) :
  (l.update i x).map f = (l.map f).update i (f x) := by sorry

#check Int.emod_lt_of_pos
@[pspec]
theorem HashMap.insert_no_resize_spec {α : Type} [Inhabited α]
  (hm : HashMap α) (key : Usize) (value : α)
  (hmSat : key ∉ hm → hm.v.num_entries < Usize.max)
  (hmNotEmpty : hm.slots.val.len ≠ 0) :
  ∃ nhm, hm.insert_no_resize α key value = ok nhm  ∧
  ↑nhm = hm.v.insert_no_resize key value := by
  rw [insert_no_resize]
  simp [hash_key]
  have : (alloc.vec.Vec.len (AList α) hm.slots).val ≠ 0 := by simp [*]
  progress as ⟨ hash_mod, hHashModEq ⟩
  have : hash_mod.val < hm.slots.length := by
    -- TODO: automate that
    rw [hHashModEq]
    apply Int.emod_lt_of_pos
    simp_all; scalar_tac
  progress as ⟨ slot0, index_back, hSlot0Eq, hInsertBack ⟩
  rw [hInsertBack]
  progress as ⟨ inserted, slot1, hInsPost ⟩
  replace hInsPost := Eq.symm hInsPost
  cases hInserted : inserted == true with
  | true =>
    simp at hInserted; simp [hInserted]
    have : ↑hm.num_entries + 1 ≤ Usize.max := by
      have hNotIn : key ∉ hm := by
        have := Spec.HashMap.insert_in_list_inserted key value slot0.v
        simp_all [Membership.mem, Spec.HashMap.lookup]
      replace hmSat := hmSat hNotIn
      scalar_tac
    progress as ⟨ num_entries1 ⟩
    progress as ⟨ slots1, hSlots1Eq ⟩
    simp [Spec.HashMap.insert_no_resize]
    simp_all
  | false =>
    simp at hInserted; simp [hInserted]
    progress as ⟨ slots1, hSlots1Eq ⟩
    simp [Spec.HashMap.insert_no_resize]
    simp_all

/-
-- TODO: make that better
instance (hm : Spec.HashMap α) : Arith.PropHasImp hm.inv where
  concl := 0 < hm.slots.len
  prop := by simp [Spec.HashMap.inv]

TODO: add the others
-/

theorem Spec.HashMap.inv_ineqs {α : Type} (hm : HashMap α) (key : Usize)
  (hinv : hm.inv) :
  0 < hm.slots.len ∧
  0 ≤ key.val % hm.slots.len ∧
  key.val % hm.slots.len < hm.slots.len := by
  have : 0 < hm.slots.len := by simp [inv] at hinv; simp [hinv] -- TODO: automate that
  have : 0 ≤ key.val % hm.slots.len := by -- TODO: automate that
    apply Int.emod_nonneg
    omega
  have : key.val % hm.slots.len < hm.slots.len := by -- TODO: automate that
    apply Int.emod_lt_of_pos
    simp_all [Spec.HashMap.inv]
  tauto

/- The invariant is preserved -/
theorem Spec.HashMap.insert_no_resize_inv {α : Type} (hm : HashMap α)
  (key : Usize) (value : α)
  (hinv : hm.inv) :
  let nhm := hm.insert_no_resize key value
  nhm.inv
  := by
  rw [insert_no_resize]
  let hash := key
  let i := hm.slots.len
  let hash_mod := ↑hash % i
  let slot := hm.slots.index hash_mod
  have hInsert := insert_in_list_inserted key value slot
  have hLength := insert_in_list_length key value slot
  have ⟨ _, _, _ ⟩ := inv_ineqs hm key hinv
  have hSlotIInv : slot_s_inv i (hash_mod_key key i) slot := by
    simp [inv, slots_s_inv] at hinv
    simp [hash_mod_key, hash_key]
    have h := hinv.right.left (↑key % i) (by assumption) (by assumption)
    exact h
  have hSlotInv := insert_in_list_slot_s_inv key value slot i hSlotIInv
  simp at *
  split <;> simp_all (config := {zetaDelta := true, arith := true}) [Spec.HashMap.inv, List.len_flatten_update_eq]
  . ring_nf
    simp [slots_s_inv]
    intro i h0 h1
    cases heq : i == (↑key % hm.slots.len) <;> simp at heq <;> simp [*]
    simp [slots_s_inv] at hinv; tauto
  . split_conjs
    . cases h: (List.lookup key (hm.slots.index (↑key % hm.slots.len))) <;> simp_all
    . simp [slots_s_inv]
      intro i h0 h1
      cases heq : i == (↑key % hm.slots.len) <;> simp at heq <;> simp [*]
      simp [slots_s_inv] at hinv; tauto  

/- The bindings are updated -/
theorem Spec.HashMap.insert_no_resize_lookup {α : Type} (hm : HashMap α)
  (key : Usize) (value : α)
  (hinv : hm.inv) :
  let nhm := hm.insert_no_resize key value
  -- We updated the binding for key
  nhm.lookup key = some value ∧
  -- We left the other bindings unchanged
  (∀ k, ¬ k = key → nhm.lookup k = hm.lookup k) := by
  simp (config := {zetaDelta := true}) [insert_no_resize, insert_in_list]
  let hash := key
  let i := hm.slots.len
  let hash_mod := ↑hash % i
  let slot := hm.slots.index hash_mod
  have ⟨ _, _, _ ⟩ := inv_ineqs hm key hinv
  have ⟨ hLookupKey, hLookupNotKey ⟩ := insert_in_list_lookup key value slot
  split <;> simp_all [lookup] <;> try tauto
  all_goals (intro key' hneq) <;>
  cases h : (key'.val % hm.slots.len == key.val % hm.slots.len) <;> simp at h <;> simp_all

/- Reasoning about the length -/
theorem Spec.HashMap.insert_no_resize_length {α : Type} (hm : HashMap α)
  (key : Usize) (value : α)
  (hinv : hm.inv) :
  let nhm := hm.insert_no_resize key value
  (match hm.lookup key with
   | none => nhm.num_entries = hm.num_entries + 1
   | some _ => nhm.num_entries = hm.num_entries) := by
  rw [insert_no_resize]
  let hash := key
  let i := hm.slots.len
  let hash_mod := ↑hash % i
  let slot := hm.slots.index hash_mod
  have hLength := insert_in_list_length key value slot
  have hInserted := insert_in_list_inserted key value slot
  split <;> simp_all (config := {zetaDelta := true, arith := true}) [Spec.HashMap.inv] <;>
  split <;> simp_all [List.len_flatten_update_eq, lookup]

def Spec.HashMap.move_elements_from_list (ntable : HashMap α) (ls : List (Usize × α)) : HashMap α :=
  match ls with
  | [] => ntable
  | (k, v) :: tl =>
    let ntable1 := insert_no_resize ntable k v
    move_elements_from_list ntable1 tl

def Spec.HashMap.move_elements (ntable : HashMap α) (slots : Spec.Slots α) (i : Int) : HashMap α × Slots α :=
  let len := slots.len
  if i < len
  then
    let slot := slots.index i
    let ntable1 := move_elements_from_list ntable slot
    let i' := i + 1
    let slots1 := slots.update i []
    move_elements ntable1 slots1 i'
  else (ntable, slots)
termination_by (slots.len - i).toNat
decreasing_by scalar_decr_tac

theorem HashMap.move_elements_from_list_spec [Inhabited α] (ntable : HashMap α) (ls : AList α) :
  ∃ ntable1, move_elements_from_list α ntable ls = .ok ntable1 ∧
  ntable1.v = ntable.v.move_elements_from_list ls.v := by
  rw [move_elements_from_list]
  rw [move_elements_from_list_loop]
  cases ls with
  | Nil =>
    simp [Spec.HashMap.move_elements_from_list]
  | Cons k v tl =>
    simp [Spec.HashMap.move_elements_from_list]
    have : k ∉ ntable → ntable.v.num_entries < Usize.max := by sorry
    have : (ntable.slots).v.len ≠ 0 := by sorry
    progress as ⟨ ntable1 ⟩
    progress keep heq as ⟨ ntable2 ⟩
    rw [move_elements_from_list] at heq; simp [heq]
    simp [*]

theorem HashMap.move_elements_spec [Inhabited α] (ntable : HashMap α) (slots : Slots α) (i : Usize) :
  ∃ ntable1 slots1, move_elements α ntable slots i = .ok (ntable1, slots1) ∧
  (ntable1.v, Slots.v slots1) = ntable.v.move_elements slots.v i.val
  := by
  rw [move_elements]
  rw [move_elements_loop]
  let len := slots.len
  if hi : i.val < len.val then sorry
  else sorry
  

/-
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
   simp [_root_.List.len_flatten_update_eq, *]
-/
/-
#exit

theorem Spec.insert_in_list_spec {α : Type} (l : Int) (key: Usize) (value: α)
  (l0: List (Usize × α))
  (hinv : slot_s_inv_hash l (hash_mod_key key l) l0)
  (hdk : distinct_keys l0) :
  let (b, l1) := insert_in_list key value l0
  -- The boolean is true ↔ we inserted a new binding
  (b ↔ (l0.lookup key = none)) ∧
  -- We update the binding
  l1.lookup key = value ∧
  (∀ k, k ≠ key → l1.lookup k = l0.lookup k) ∧
  -- We preserve part of the key invariant
  slot_s_inv_hash l (hash_mod_key key l) l1 ∧
  -- Reasoning about the length
  (match l0.lookup key with
   | none => l1.len = l0.len + 1
   | some _ => l1.len = l0.len) ∧
  -- The keys are distinct
  distinct_keys l1 ∧
  -- We need this auxiliary property to prove that the keys distinct properties is preserved
  (∀ k, k ≠ key → l0.allP (λ (k1, _) => k ≠ k1) → l1.allP (λ (k1, _) => k ≠ k1))
  := by
  match l0 with
  | [] =>
    stop
    simp (config := {contextual := true})
      [insert_in_list, slot_s_inv_hash, distinct_keys, List.pairwise_rel, List.lookup]
  | (k, v)::tl0 =>
    simp [insert_in_list]
    if h: k = key then
      stop
      simp [h]
      split_conjs
      . intros; simp [List.lookup, *]
      . simp [AList.v, slot_s_inv_hash] at *
        simp [*]
      . simp [*, distinct_keys] at *
        apply hdk
      . tauto
    else
      have hInd :=
        insert_in_list_spec l key value tl0 (by simp_all [AList.v, slot_s_inv_hash])
                                            (by simp [distinct_keys] at hdk
                                                simp [hdk, distinct_keys])
      simp at hInd
      next =>
      have : slot_s_inv_hash l (↑key % l) ((k, v) :: (insert_in_list key value tl0).2) := by
        simp [distinct_keys] at *
        simp [*]
      simp (config := {contextual := true}) [insert_in_list, List.lookup, *]
      simp [distinct_keys, *]
      -- TODO: canonize addition by default?
      simp_all [Int.add_assoc, Int.add_comm, Int.add_left_comm]
      stop
      have : slot_s_inv_hash l (hash_mod_key key l) (AList.v tl0) := by
        simp_all [AList.v, slot_s_inv_hash]
      have : distinct_keys (AList.v tl0) := by
        simp [distinct_keys] at hdk
        simp [hdk, distinct_keys]
      progress keep heq as ⟨ b, tl1 .. ⟩
      simp only [insert_in_list] at heq
      have : slot_s_inv_hash l (hash_mod_key key l) (AList.v (AList.Cons k v tl1)) := by
        simp [AList.v, slot_s_inv_hash] at *
        simp [*]
      have : distinct_keys ((k, v) :: AList.v tl1) := by
        simp [distinct_keys] at *
        simp [*]
      -- TODO: canonize addition by default?
      exists b
      simp_all [Int.add_assoc, Int.add_comm, Int.add_left_comm]

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

#exit

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
  match l0 with
  | Nil =>
    exists true -- TODO: why do we need to do this?
    simp [insert_in_list]
    rw [insert_in_list_loop]
    simp (config := {contextual := true})
      [AList.v, slot_s_inv_hash, distinct_keys, List.pairwise_rel]
  | Cons k v tl0 =>
     if h: k = key then
       rw [insert_in_list]
       rw [insert_in_list_loop]
       simp [h]
       exists false; simp -- TODO: why do we need to do this?
       split_conjs
       . intros; simp [*]
       . simp [AList.v, slot_s_inv_hash] at *
         simp [*]
       . simp [*, distinct_keys] at *
         apply hdk
       . tauto
     else
       rw [insert_in_list]
       rw [insert_in_list_loop]
       simp [h]
       have : slot_s_inv_hash l (hash_mod_key key l) (AList.v tl0) := by
         simp_all [AList.v, slot_s_inv_hash]
       have : distinct_keys (AList.v tl0) := by
         simp [distinct_keys] at hdk
         simp [hdk, distinct_keys]
       progress keep heq as ⟨ b, tl1 .. ⟩
       simp only [insert_in_list] at heq
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

@[simp]
def slots_t_lookup (s : List (AList α)) (k : Usize) : Option α :=
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

--set_option profiler true
--set_option profiler.threshold 10
--set_option trace.profiler true

-- For pretty printing (useful when copy-pasting goals)
set_option pp.coercions false -- do not print coercions with ↑ (this doesn't parse)

-- The proof below is a bit expensive, so we need to increase the maximum number
-- of heart beats
set_option maxHeartbeats 2000000

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
    simp [inv, slots_t_inv, slot_t_inv] at hinv
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
    simp only [lookup, List.lookup, len_s, al_v, HashMap.v, slots_t_lookup] at *
    -- We have to do a case disjunction
    simp_all
    simp [_root_.List.update_map_eq]
    -- TODO: dependent rewrites
    have _ : key.val % hm.slots.val.len < (List.map AList.v hm.slots.val).len := by
      simp [*]
    simp [_root_.List.len_flatten_update_eq, *]
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
    . simp [hinv, h_veq, nhm_eq]
  simp_all

end HashMap-/

end hashmap
