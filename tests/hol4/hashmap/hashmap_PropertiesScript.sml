open primitivesLib primitivesArithTheory primitivesTheory listTheory ilistTheory hashmap_TypesTheory hashmap_FunsTheory

val _ = new_theory "hashmap_Properties"

val pairwise_rel_def = Define ‘
  pairwise_rel p [] = T ∧
  pairwise_rel p (x :: ls) = (EVERY (p x) ls ∧ pairwise_rel p ls)
’

(* TODO: move *)
Theorem EVERY_quant_equiv:
  ∀p ls. EVERY p ls ⇔ ∀i. 0 ≤ i ⇒ i < len ls ⇒ p (index i ls)
Proof
  strip_tac >> Induct_on ‘ls’
  >-(rw [EVERY_DEF, len_def] >> int_tac) >>
  rw [EVERY_DEF, len_def, index_eq] >>
  equiv_tac
  >-(
    rw [] >>
    Cases_on ‘i = 0’ >> fs [] >>
    first_x_assum irule >>
    int_tac) >>
  rw []
  >-(
    first_x_assum (qspec_assume ‘0’) >> fs [] >>
    first_x_assum irule >>
    qspec_assume ‘ls’ len_pos >>
    int_tac) >>
  first_x_assum (qspec_assume ‘i + 1’) >>
  fs [] >>
  sg ‘i + 1 ≠ 0 ∧ i + 1 - 1 = i’ >- int_tac >> fs [] >>
  first_x_assum irule >> int_tac
QED

(* TODO: move *)
Theorem pairwise_rel_quant_equiv:
  ∀p ls. pairwise_rel p ls ⇔
    (∀i j. 0 ≤ i ⇒ i < j ⇒ j < len ls ⇒ p (index i ls) (index j ls))
Proof
  strip_tac >> Induct_on ‘ls’
  >-(rw [pairwise_rel_def, len_def] >> int_tac) >>
  rw [pairwise_rel_def, len_def] >>
  equiv_tac
  >-(
    (* ==> *)
    rw [] >>
    sg ‘0 < j’ >- int_tac >>
    Cases_on ‘i = 0’
    >-(
      simp [index_eq] >>
      qspecl_assume [‘p h’, ‘ls’] (iffLR EVERY_quant_equiv) >>
      first_x_assum irule >> fs [] >> int_tac
    ) >>
    rw [index_eq] >>
    first_x_assum irule >> int_tac
  ) >>
  (* <== *)
  rw []
  >-(
    rw [EVERY_quant_equiv] >>
    first_x_assum (qspecl_assume [‘0’, ‘i + 1’]) >>
    sg ‘0 < i + 1 ∧ i + 1 - 1 = i’ >- int_tac >>
    fs [index_eq] >>
    first_x_assum irule >> int_tac
  ) >>
  sg ‘pairwise_rel p ls’
  >-(
    rw [pairwise_rel_def] >>
    first_x_assum (qspecl_assume [‘i' + 1’, ‘j' + 1’]) >>
    sg ‘0 < i' + 1 ∧ 0 < j' + 1’ >- int_tac >>
    fs [index_eq, int_add_minus_same_eq] >>
    first_x_assum irule >> int_tac
  ) >>
  fs []
QED

Type key_t = “:usize”

val distinct_keys_def = Define ‘
  distinct_keys (ls : (key_t # 't) list) =
    pairwise_rel (\x y. FST x ≠ FST y) ls
’

(* Conversion from “:list_t” to “:list” *)
Definition list_t_v_def:
  (list_t_v (ListNil : 't list_t) : (key_t # 't) list = []) /\
  (list_t_v (ListCons k v tl) = (k, v) :: list_t_v tl)
End

(* Invariants *)
Definition lookup_def:
  lookup key [] = NONE /\
  lookup key ((k, v) :: ls) =
    if k = key then SOME v else lookup key ls
End

Definition slot_t_lookup_def:
  slot_t_lookup key ls = lookup key (list_t_v ls)
End

Definition remove_def:
  remove key [] = [] ∧
  remove key ((k, v) :: ls) =
    if k = key then ls else (k, v) :: remove key ls
End

Definition slot_t_remove_def:
  slot_t_remove key ls = remove key (list_t_v ls)
End

Definition hash_mod_key_def:
  hash_mod_key k (l : int) : int =
    case hash_key_fwd k of
    | Return k => usize_to_int k % l
    | _ => ARB
End

Definition slot_s_inv_hash_def:
  slot_s_inv_hash (l : int) (i : int) (ls : (key_t # 'b) list) : bool =
    ∀ k v. MEM (k, v) ls ⇒ hash_mod_key k l = i
End

Definition slot_s_inv_def:
  slot_s_inv (l : int) (i : int) (ls : (key_t # 'b) list) : bool = (
    distinct_keys ls ∧
    slot_s_inv_hash l i ls
  )
End

(* TODO: try with this invariant:

Definition slot_s_inv_def:a
  slot_s_inv (i : int) (ls : (key_t # 'b) list) : bool =
    (∀ k. lookup k ls ≠ NONE ⇒ lookup k (remove k ls) = NONE) ∧
    (∀ k v. MEM (k, v) ls ⇒
      ∃ hk. hash_key_fwd k = Return hk ⇒
        usize_to_int hk = i)
    )
End

*)

Definition slot_t_inv_def:
  slot_t_inv (l : int) (i : int) (s : 't list_t) = slot_s_inv l i (list_t_v s)
End

(* Representation function of the hash map as a list of slots *)
Definition hash_map_t_v_def:
  hash_map_t_v (hm : 't hash_map_t) : (key_t # 't) list list =
    MAP list_t_v (vec_to_list hm.hash_map_slots)
End

(* Representation function of the hash map as an associative list *)
Definition hash_map_t_al_v_def:
  hash_map_t_al_v (hm : 't hash_map_t) : (key_t # 't) list = FLAT (hash_map_t_v hm)
End

Definition slots_s_inv_def:
  slots_s_inv (s : 'a list_t list) =
    ∀ (i : int). 0 ≤ i ⇒ i < len s ⇒ slot_t_inv (len s) i (index i s)
End

Definition slots_t_inv_def:
  slots_t_inv (s : 'a list_t vec) = slots_s_inv (vec_to_list s)
End

Definition hash_map_t_base_inv_def:
  hash_map_t_base_inv (hm : 't hash_map_t) =
    let al = hash_map_t_al_v hm in
    (* [num_entries] correctly tracks the number of entries in the table *)
    usize_to_int hm.hash_map_num_entries = len al /\
    (* Slots invariant *)
    slots_t_inv hm.hash_map_slots ∧
    (* The capacity must be > 0 (otherwise we can't resize, because when we
       resize we multiply the capacity by two) *)
    len (vec_to_list hm.hash_map_slots) > 0 ∧
    (* Load computation *)
    (let capacity = len (vec_to_list hm.hash_map_slots) in
     let (dividend, divisor) = hm.hash_map_max_load_factor in
     let dividend = usize_to_int dividend in
     let divisor = usize_to_int divisor in
     0 < dividend /\ dividend < divisor /\
     capacity * dividend >= divisor /\
     usize_to_int (hm.hash_map_max_load) = (capacity * dividend) / divisor
    )
End

(* The invariant that we reveal to the user *)
Definition hash_map_t_inv_def:
  hash_map_t_inv (hm : 't hash_map_t) : bool = (
    (* Base invariant *)
    hash_map_t_base_inv hm /\
    (* The hash map is either: not overloaded, or we can't resize it *)
    (let (dividend, divisor) = hm.hash_map_max_load_factor in
     (usize_to_int hm.hash_map_num_entries <= usize_to_int hm.hash_map_max_load) ∨
     (len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int dividend > usize_max)
    )
  )
End

(* The specification functions that we reveal in the top-level theorems *)
Definition len_s_def:
  len_s hm = len (hash_map_t_al_v hm)
End

Definition slots_t_lookup_def:
  slots_t_lookup (s : 't list_t list) (k : key_t) : 't option = 
    let i = hash_mod_key k (len s) in
    let slot = index i s in
    slot_t_lookup k slot
End

Definition lookup_s_def:
  lookup_s (hm : 't hash_map_t) (k : key_t) : 't option =
    slots_t_lookup (vec_to_list hm.hash_map_slots) k
End

(*============================================================================*
 *============================================================================*
 *  Proofs
 *============================================================================*
 *============================================================================*)

(*============================================================================*
 *  New
 *============================================================================*)

Theorem hash_map_allocate_slots_loop_fwd_spec:
  ∀ slots n.
    EVERY (\x. x = ListNil) (vec_to_list slots) ⇒
    len (vec_to_list slots) + usize_to_int n ≤ usize_max ⇒
    ∃ nslots. hash_map_allocate_slots_loop_fwd slots n = Return nslots ∧
      len (vec_to_list nslots) = len (vec_to_list slots) + usize_to_int n ∧
      EVERY (\x. x = ListNil) (vec_to_list nslots)
Proof
  (* TODO: induction principle for usize, etc. *)
  Induct_on ‘usize_to_int n’ >> rw [] >> massage >- int_tac >>
  pure_once_rewrite_tac [hash_map_allocate_slots_loop_fwd_def] >>
  fs [usize_gt_def] >> massage >> fs [] >>
  (* TODO: would be good to simply use progress here *)
  case_tac
  >-(
    sg ‘len (vec_to_list slots) ≤ usize_max’ >- int_tac >>
    (* TODO: massage needs to know that len is >= 0 *)
    qspec_assume ‘vec_to_list slots’ len_pos >>
    progress >- (
      fs [vec_len_def] >>
      massage >>
      int_tac) >>
    progress >>
    gvs [] >>
    (* TODO: progress doesn't work here *)
    last_x_assum (qspec_assume ‘a'’) >>
    massage >> gvs [] >>
    sg ‘v = usize_to_int n - 1’ >- int_tac >> fs [] >>
    (* *)
    progress >>
    fs [vec_len_def, len_append, len_def] >>
    int_tac
  ) >>
  fs [] >>
  int_tac
QED
val _ = save_spec_thm "hash_map_allocate_slots_loop_fwd_spec"

Theorem hash_map_allocate_slots_fwd_spec:
  ∀ n.
    usize_to_int n ≤ usize_max ⇒
    ∃ slots. hash_map_allocate_slots_fwd vec_new n = Return slots ∧
    slots_t_inv slots ∧
    len (vec_to_list slots) = usize_to_int n ∧
    EVERY (\x. x = ListNil) (vec_to_list slots)
Proof
  rw [] >>
  pure_once_rewrite_tac [hash_map_allocate_slots_fwd_def] >>
  progress >> gvs [len_def, slots_t_inv_def, slots_s_inv_def, slot_s_inv_hash_def] >>
  rw [slot_t_inv_def, slot_s_inv_def, slot_s_inv_hash_def]
  >- fs [EVERY_quant_equiv, distinct_keys_def, pairwise_rel_def, list_t_v_def] >>
  fs [EVERY_quant_equiv] >>
  qpat_assum ‘∀i. _’ sg_dep_rewrite_all_tac >> gvs [list_t_v_def]
QED
val _ = save_spec_thm "hash_map_allocate_slots_fwd_spec"

(* Auxiliary lemma *)
Theorem FLAT_ListNil_is_nil:
  EVERY (λx. x = ListNil) ls ⇒ FLAT (MAP list_t_v ls) = []
Proof
  Induct_on ‘ls’ >> fs [list_t_v_def]
QED

Theorem hash_map_new_with_capacity_fwd_spec:
  ∀ capacity max_load_dividend max_load_divisor.
  0 < usize_to_int max_load_dividend ⇒
  usize_to_int max_load_dividend < usize_to_int max_load_divisor ⇒
  0 < usize_to_int capacity ⇒
  usize_to_int capacity * usize_to_int max_load_dividend >= usize_to_int max_load_divisor ⇒
  usize_to_int capacity * usize_to_int max_load_dividend <= usize_max ⇒
  ∃ hm. hash_map_new_with_capacity_fwd capacity max_load_dividend max_load_divisor = Return hm ∧
  hash_map_t_inv hm ∧
  len_s hm = 0 ∧
  ∀ k. lookup_s hm k = NONE
Proof
  rw [] >> fs [hash_map_new_with_capacity_fwd_def] >>
  progress >>
  progress >>
  progress >>
  gvs [hash_map_t_inv_def, hash_map_t_base_inv_def, hash_map_t_al_v_def, hash_map_t_v_def] >>
  rw []
  >-(massage >> sg_dep_rewrite_goal_tac FLAT_ListNil_is_nil >> fs [len_def])
  >-(int_tac)
  >-(massage >> metis_tac [])
  >-(fs [len_s_def, hash_map_t_al_v_def, hash_map_t_v_def] >>
     sg_dep_rewrite_goal_tac FLAT_ListNil_is_nil >> fs [len_def]) >>
  fs [lookup_s_def, slots_t_lookup_def, slot_t_lookup_def] >>
  fs [EVERY_quant_equiv] >>
  (* TODO: sg_dep_rewrite_goal_tac does weird things here *)
  first_x_assum (qspec_assume ‘hash_mod_key k (usize_to_int capacity)’) >>
  first_x_assum sg_premise_tac
  >- (
    fs [hash_mod_key_def, hash_key_fwd_def] >>
    massage >>
    irule pos_mod_pos_is_pos >> fs []) >>
  first_x_assum sg_premise_tac
  >-(
    fs [hash_mod_key_def, hash_key_fwd_def] >>
    massage >>
    irule pos_mod_pos_lt >> fs []
  ) >>  
  fs [list_t_v_def, lookup_def]
QED
val _ = save_spec_thm "hash_map_new_with_capacity_fwd_spec"

Theorem hash_map_new_fwd_spec:
 ∃ hm. hash_map_new_fwd = Return hm ∧
   hash_map_t_inv hm ∧
   ∀ k. lookup_s hm k = NONE ∧
   len_s hm = 0
Proof
  pure_rewrite_tac [hash_map_new_fwd_def] >>
  progress >> massage >> fs [] >>
  assume_tac usize_bounds >> fs [u16_max_def] >>
  int_tac
QED
val _ = save_spec_thm "hash_map_new_fwd_spec"

(*============================================================================*
 *  Clear
 *============================================================================*)

(* [clear]: the loop doesn't fail and simply clears the slots starting at index i *)
Theorem hash_map_clear_loop_fwd_back_spec_aux:
  ∀ n slots i.
    (* Small trick to make the induction work well *)
    n = len (vec_to_list slots) - usize_to_int i ⇒
    ∃ slots1. hash_map_clear_loop_fwd_back slots i = Return slots1 ∧
    len (vec_to_list slots1) = len (vec_to_list slots) ∧
    (*  The slots before i are left unchanged *)
    (∀ j. 0 ≤ j ⇒ j < usize_to_int i ⇒
           j < len (vec_to_list slots) ⇒
           index j (vec_to_list slots1) = index j (vec_to_list slots)) ∧
    (* The slots after i are set to ListNil *)
    (∀ j. usize_to_int i ≤ j ⇒ j < len (vec_to_list slots) ⇒
           index j (vec_to_list slots1) = ListNil)
Proof
  (* TODO: induction principle for usize, etc. *)
  Induct_on ‘n’ >> rw [] >>
  pure_once_rewrite_tac [hash_map_clear_loop_fwd_back_def] >>
  fs [usize_lt_def, vec_len_def] >>
  (* TODO: automate that *)
  qspec_assume ‘slots’ vec_len_spec >> massage
  >-(case_tac >> rw [] >> int_tac)
  >-(rw [] >> int_tac) >>
  case_tac
  >-(
    (* usize_to_int i < len (vec_to_list slots) *)
    progress >>
    progress >> massage >- int_tac >>
    qspecl_assume [‘slots’, ‘i’, ‘ListNil’] vec_update_eq >> fs [] >>
    progress >> rw []
    >-(
      (* Use the induction hypothesis *)
      last_x_assum (qspec_assume ‘j’) >> gvs [] >>
      sg ‘j < usize_to_int i + 1’ >- int_tac >> gvs [] >>
      (* Use the vec_update eq *)
      last_x_assum (qspec_assume ‘int_to_usize j’) >> gvs [vec_len_def] >> massage >>
      gvs [] >>
      sg ‘j ≠ usize_to_int i’ >- int_tac >>
      fs [vec_index_def] >>
      massage) >>
    Cases_on ‘usize_to_int i = j’ >> fs [vec_index_def] >>
    first_x_assum (qspec_assume ‘j’) >> gvs [] >>
    sg ‘usize_to_int i + 1 ≤ j’ >- int_tac >> gvs [])
  >>
  rw [] >>
  int_tac
QED

Theorem hash_map_clear_loop_fwd_back_spec:
  ∀ slots.
    ∃ slots1. hash_map_clear_loop_fwd_back slots (int_to_usize 0) = Return slots1 ∧
    len (vec_to_list slots1) = len (vec_to_list slots) ∧
    (* All the slots are set to ListNil *)
    (∀ j. 0 ≤ j ⇒ j < len (vec_to_list slots) ⇒
           index j (vec_to_list slots1) = ListNil) ∧
    (* The map is empty *)
    (FLAT (MAP list_t_v (vec_to_list slots1)) = [])
Proof
  rw [] >>
  qspecl_assume [‘len (vec_to_list slots) − 0’, ‘slots’, ‘int_to_usize 0’]
   hash_map_clear_loop_fwd_back_spec_aux >>
  massage >> fs [] >>
  irule FLAT_ListNil_is_nil >>
  fs [EVERY_quant_equiv]
QED
val _ = save_spec_thm "hash_map_clear_loop_fwd_back_spec"

Theorem hash_map_clear_fwd_back_spec:
  ∀ hm.
    hash_map_t_inv hm ⇒
    ∃ hm1. hash_map_clear_fwd_back hm = Return hm1 ∧
    hash_map_t_inv hm1 ∧
    len_s hm1 = 0 ∧
    (∀ k. lookup_s hm1 k = NONE)
Proof
  rw [hash_map_clear_fwd_back_def] >>
  progress >>
  fs [len_s_def, hash_map_t_al_v_def, hash_map_t_v_def, lookup_s_def] >>
  fs [slots_t_lookup_def, slot_t_lookup_def, len_def] >> rw []
  >-((* Prove that the invariant is preserved *)
   fs [hash_map_t_inv_def, hash_map_t_base_inv_def, hash_map_t_al_v_def, hash_map_t_v_def, len_def] >>
   massage >> fs [] >>
   conj_tac
   >-(
     fs [slots_t_inv_def, slots_s_inv_def] >>
     rw [slot_t_inv_def, slot_s_inv_def, slot_s_inv_hash_def, list_t_v_def, distinct_keys_def, pairwise_rel_def]) >>
   Cases_on ‘hm.hash_map_max_load_factor’ >> gvs [] >>
   disj1_tac >>
   irule pos_div_pos_is_pos >>
   int_tac) >>
  fs [hash_mod_key_def, hash_key_fwd_def] >>
  (* TODO: would like to do: qpat_assum ‘∀j. _’ sg_dep_rewrite_goal_tac >> *)
  first_x_assum (qspec_assume ‘usize_to_int k % len (vec_to_list hm.hash_map_slots)’) >>
  fs [] >>
  (* TODO: automate that *)
  qspec_assume ‘hm.hash_map_slots’ vec_len_spec >> fs [] >>
  qspecl_assume [‘usize_to_int k’, ‘len (vec_to_list hm.hash_map_slots)’] integerTheory.INT_MOD_BOUNDS >>
  sg ‘len (vec_to_list hm.hash_map_slots) ≠ 0’
  >-(fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac) >>
  fs [] >>
  sg ‘~(len (vec_to_list hm.hash_map_slots) < 0)’ >- int_tac >>
  fs [list_t_v_def, lookup_def]
QED
val _ = save_spec_thm "hash_map_clear_fwd_back_spec"
  

(*============================================================================*
 *  Len
 *============================================================================*)

Theorem hash_map_len_spec:
  ∀ hm.
    hash_map_t_inv hm ⇒
    ∃ x. hash_map_len_fwd hm = Return x ∧
    usize_to_int x = len_s hm
Proof
  rw [hash_map_len_fwd_def, hash_map_t_inv_def, hash_map_t_base_inv_def, len_s_def]
QED
val _ = save_spec_thm "hash_map_len_spec"


(*============================================================================*
 *  Insert
 *============================================================================*)

Theorem hash_map_insert_in_list_loop_fwd_spec:
  !ls key value.
    ∃ b. hash_map_insert_in_list_loop_fwd key value ls = Return b ∧
    (b ⇔ slot_t_lookup key ls = NONE)
Proof
  Induct_on ‘ls’ >> pure_once_rewrite_tac [hash_map_insert_in_list_loop_fwd_def] >>
  fs [slot_t_lookup_def, lookup_def, list_t_v_def] >>
  rw []
QED
val _ = save_spec_thm "hash_map_insert_in_list_loop_fwd_spec"

Theorem hash_map_insert_in_list_fwd_spec:
  !ls key value.
    ∃ b. hash_map_insert_in_list_fwd key value ls = Return b ∧
    (b ⇔ slot_t_lookup key ls = NONE)
Proof
  rw [hash_map_insert_in_list_fwd_def] >> progress >> fs []
QED
val _ = save_spec_thm "hash_map_insert_in_list_fwd_spec"

(* Lemma about ‘hash_map_insert_in_list_loop_back’, without the invariant *)
Theorem hash_map_insert_in_list_loop_back_spec_aux:
  !ls key value.
    ∃ ls1. hash_map_insert_in_list_loop_back key value ls = Return ls1 ∧
    (* We updated the binding for key *)
    slot_t_lookup key ls1 = SOME value /\
    (* The other bindings are left unchanged *)
    (!k. k <> key ==> slot_t_lookup k ls = slot_t_lookup k ls1) ∧
    (* We preserve part of the key invariant *)
    (∀ l. slot_s_inv_hash l (hash_mod_key key l) (list_t_v ls) ==> slot_s_inv_hash l (hash_mod_key key l) (list_t_v ls1)) ∧
    (* Reasoning about the length *)
    (case slot_t_lookup key ls of
     | NONE => len (list_t_v ls1) = len (list_t_v ls) + 1
     | SOME _ => len (list_t_v ls1) = len (list_t_v ls))
Proof
  Induct_on ‘ls’ >> rw [list_t_v_def] >~ [‘ListNil’] >>
  pure_once_rewrite_tac [hash_map_insert_in_list_loop_back_def]
  >- (rw [slot_t_lookup_def, lookup_def, list_t_v_def, len_def, slot_s_inv_hash_def]) >>
  fs [] >>
  case_tac >> fs []
  >-(fs [slot_t_lookup_def, lookup_def, list_t_v_def, len_def, slot_s_inv_hash_def] >>
     metis_tac []) >>
  progress >>
  fs [slot_t_lookup_def, lookup_def, list_t_v_def, len_def] >>
  rw []
  >-(fs [slot_s_inv_hash_def] >> metis_tac []) >>
  case_tac >> fs [] >> int_tac
QED

(* Auxiliary lemma - TODO: move *)
Theorem hash_map_insert_in_list_loop_back_EVERY_distinct_keys:
  ∀k v k1 ls0 ls1.
  k1 ≠ k ⇒
  EVERY (λy. k1 ≠ FST y) (list_t_v ls0) ⇒
  pairwise_rel (λx y. FST x ≠ FST y) (list_t_v ls0) ⇒
  hash_map_insert_in_list_loop_back k v ls0 = Return ls1 ⇒
  EVERY (λy. k1 ≠ FST y) (list_t_v ls1)
Proof
  Induct_on ‘ls0’ >> rw [pairwise_rel_def] >~ [‘ListNil’] >>
  gvs [list_t_v_def, pairwise_rel_def, EVERY_DEF]
  >-(gvs [MK_BOUNDED hash_map_insert_in_list_loop_back_def 1, bind_def, list_t_v_def, EVERY_DEF]) >>
  pat_undisch_tac ‘hash_map_insert_in_list_loop_back _ _ _ = _’ >>
  simp [MK_BOUNDED hash_map_insert_in_list_loop_back_def 1, bind_def] >>
  Cases_on ‘u = k’ >> rw [] >> gvs [list_t_v_def, pairwise_rel_def, EVERY_DEF] >>
  Cases_on ‘hash_map_insert_in_list_loop_back k v ls0’ >>
  gvs [distinct_keys_def, list_t_v_def, pairwise_rel_def, EVERY_DEF] >>
  metis_tac []
QED

Theorem hash_map_insert_in_list_loop_back_distinct_keys:
  ∀ k v ls0 ls1.
  distinct_keys (list_t_v ls0) ⇒
  hash_map_insert_in_list_loop_back k v ls0 = Return ls1 ⇒
  distinct_keys (list_t_v ls1)
Proof
  Induct_on ‘ls0’ >> rw [distinct_keys_def] >~ [‘ListNil’]
  >-(
    fs [list_t_v_def, hash_map_insert_in_list_loop_back_def] >>
    gvs [list_t_v_def, pairwise_rel_def, EVERY_DEF]) >>
  last_x_assum (qspecl_assume [‘k’, ‘v’]) >>
  pat_undisch_tac ‘hash_map_insert_in_list_loop_back _ _ _ = _’ >>
  simp [MK_BOUNDED hash_map_insert_in_list_loop_back_def 1, bind_def] >>
  Cases_on ‘u = k’ >> rw [] >> gvs [list_t_v_def, pairwise_rel_def, EVERY_DEF] >>
  Cases_on ‘hash_map_insert_in_list_loop_back k v ls0’ >>
  gvs [distinct_keys_def, list_t_v_def, pairwise_rel_def, EVERY_DEF] >>
  metis_tac [hash_map_insert_in_list_loop_back_EVERY_distinct_keys]
QED

Definition insert_in_slot_t_rel_def:
  insert_in_slot_t_rel l key value slot slot1 = (
    (* We preserve the invariant *)
    slot_t_inv l (hash_mod_key key l) slot1 ∧
    (* We updated the binding for key *)
    slot_t_lookup key slot1 = SOME value /\
    (* The other bindings are left unchanged *)
    (!k. k <> key ==> slot_t_lookup k slot = slot_t_lookup k slot1) ∧
    (* Reasoning about the length *)
    (case slot_t_lookup key slot of
     | NONE => len (list_t_v slot1) = len (list_t_v slot) + 1
     | SOME _ => len (list_t_v slot1) = len (list_t_v slot)))
End

(* Lemma about ‘hash_map_insert_in_list_loop_back’, with the invariant *)
Theorem hash_map_insert_in_list_loop_back_spec:
  !i ls key value.
    distinct_keys (list_t_v ls) ⇒
    ∃ ls1. hash_map_insert_in_list_loop_back key value ls = Return ls1 ∧
    (∀l. slot_s_inv_hash l (hash_mod_key key l) (list_t_v ls) ⇒
     insert_in_slot_t_rel l key value ls ls1)
Proof
  rw [slot_t_inv_def, slot_s_inv_def] >>
  qspecl_assume [‘ls’, ‘key’, ‘value’] hash_map_insert_in_list_loop_back_spec_aux >>
  fs [] >>
  qspecl_assume [‘key’, ‘value’, ‘ls’, ‘ls1’] hash_map_insert_in_list_loop_back_distinct_keys >>
  gvs [insert_in_slot_t_rel_def, slot_t_inv_def, slot_s_inv_def]
QED
val _ = save_spec_thm "hash_map_insert_in_list_loop_back_spec"

(* TODO: move and use more *)
Theorem hash_map_t_base_inv_len_slots:
  ∀ hm. hash_map_t_base_inv hm ⇒ 0 < len (vec_to_list hm.hash_map_slots)
Proof
  rw [hash_map_t_base_inv_def, vec_len_def] >> int_tac
QED

(* TODO: automatic rewriting? *)
Theorem hash_map_insert_no_resize_fwd_back_branches_eq:
  (if slot_t_lookup key (vec_index hm.hash_map_slots a) = NONE then
    do
      i0 <- usize_add hm.hash_map_num_entries (int_to_usize 1);
      l0 <-
        hash_map_insert_in_list_back key value
          (vec_index hm.hash_map_slots a);
      v <- vec_index_mut_back hm.hash_map_slots a l0;
      Return
        (hm with <|hash_map_num_entries := i0; hash_map_slots := v|>)
    od
  else
    do
      l0 <-
        hash_map_insert_in_list_back key value
          (vec_index hm.hash_map_slots a);
      v <- vec_index_mut_back hm.hash_map_slots a l0;
      Return (hm with hash_map_slots := v)
    od) =
  (do
  i0 <- if slot_t_lookup key (vec_index hm.hash_map_slots a) = NONE then
          usize_add hm.hash_map_num_entries (int_to_usize 1)
        else
          Return hm.hash_map_num_entries;
  l0 <-
    hash_map_insert_in_list_back key value
      (vec_index hm.hash_map_slots a);
  v <- vec_index_mut_back hm.hash_map_slots a l0;
  Return
    (hm with <|hash_map_num_entries := i0; hash_map_slots := v|>)
  od)
Proof
  case_tac >>
  fs [bind_def] >>
  case_tac >>
  case_tac >>
  Cases_on ‘hm’ >> fs [] >>
  fs [hashmap_TypesTheory.recordtype_hash_map_t_seldef_hash_map_slots_fupd_def] >>
  fs [hashmap_TypesTheory.recordtype_hash_map_t_seldef_hash_map_num_entries_fupd_def]
QED

Theorem hash_map_cond_incr_thm:
  ∀ hm key a.
  hash_map_t_base_inv hm ⇒
  (slot_t_lookup key (vec_index hm.hash_map_slots a) = NONE ⇒ len_s hm < usize_max) ⇒
  ∃ n. (if slot_t_lookup key (vec_index hm.hash_map_slots a) = NONE
         then usize_add hm.hash_map_num_entries (int_to_usize 1)
         else Return hm.hash_map_num_entries) = Return n ∧
  (if slot_t_lookup key (vec_index hm.hash_map_slots a) = NONE
   then usize_to_int n = usize_to_int hm.hash_map_num_entries + 1
   else n = hm.hash_map_num_entries)
Proof
  rw [] >>
  progress >>
  massage >>
  fs [len_s_def, hash_map_t_base_inv_def] >>
  (* TODO: improve massage to not only look at variables *)
  qspec_assume ‘hm.hash_map_num_entries’ usize_to_int_bounds >> fs [] >>
  int_tac
QED

Theorem hash_map_insert_no_resize_fwd_back_spec_aux:
  !hm key value.
    (* Using the base invariant, because the full invariant is preserved only
       if we resize *)
    hash_map_t_base_inv hm ⇒
    (lookup_s hm key = NONE ⇒ len_s hm < usize_max) ⇒
    ∃ hm1 slot1. hash_map_insert_no_resize_fwd_back hm key value = Return hm1 ∧
    len (vec_to_list hm1.hash_map_slots) = len (vec_to_list hm.hash_map_slots) ∧
    let l = len (vec_to_list hm.hash_map_slots) in
    let i = hash_mod_key key (len (vec_to_list hm.hash_map_slots)) in
    let slot = index i (vec_to_list hm.hash_map_slots) in
    insert_in_slot_t_rel l key value slot slot1 ∧
    vec_to_list hm1.hash_map_slots = update (vec_to_list hm.hash_map_slots) i slot1 ∧
    hm1.hash_map_max_load_factor = hm.hash_map_max_load_factor ∧
    hm1.hash_map_max_load = hm.hash_map_max_load ∧
    (* Reasoning about the length *)
    (case lookup_s hm key of
     | NONE => usize_to_int hm1.hash_map_num_entries = usize_to_int hm.hash_map_num_entries + 1
     | SOME _ => hm1.hash_map_num_entries = hm.hash_map_num_entries)
Proof
  rw [hash_map_insert_no_resize_fwd_back_def] >>
  fs [hash_key_fwd_def] >>
  (* TODO: automate this *)
  qspec_assume ‘hm.hash_map_slots’ vec_len_spec >>
  (* TODO: improve massage to not only look at variables *)
  qspec_assume ‘hm.hash_map_num_entries’ usize_to_int_bounds >> fs [] >>
  imp_res_tac hash_map_t_base_inv_len_slots >>
  (* TODO: update usize_rem_spec? *)
  qspecl_assume [‘usize_to_int key’, ‘len (vec_to_list hm.hash_map_slots)’] pos_rem_pos_ineqs >>
  progress >>
  progress >- ( (* TODO: why not done automatically? *) massage >> fs []) >>
  progress >> gvs [] >>
  (* Taking care of the disjunction *)
  fs [hash_map_insert_no_resize_fwd_back_branches_eq] >>
  qspecl_assume [‘hm’, ‘key’, ‘a’] hash_map_cond_incr_thm >> gvs [] >>
  pop_assum sg_premise_tac
  >- (fs [lookup_s_def, slots_t_lookup_def, slot_t_lookup_def, hash_mod_key_def, hash_key_fwd_def, vec_index_def, int_rem_def]) >>
  fs [] >>
  (* TODO: lemma? *)
  sg ‘let l = len (vec_to_list hm.hash_map_slots) in
      slot_t_inv l (usize_to_int key % l) (index (usize_to_int key % l) (vec_to_list hm.hash_map_slots))’
  >-(fs [hash_map_t_base_inv_def, slots_t_inv_def, slots_s_inv_def] >>
     last_x_assum (qspec_assume ‘usize_to_int a’) >>
     gvs [vec_index_def, int_rem_def, slot_t_inv_def, slot_s_inv_def]) >>
  fs [] >>
  sg ‘usize_to_int a = usize_to_int key % len (vec_to_list hm.hash_map_slots)’
  >-(fs [int_rem_def]) >>
  sg ‘int_rem (usize_to_int key) (len (vec_to_list hm.hash_map_slots)) = usize_to_int key % len (vec_to_list hm.hash_map_slots)’
  >-(fs [int_rem_def]) >>
  fs [] >>
  sg ‘distinct_keys (list_t_v (vec_index hm.hash_map_slots a))’
  >-(fs [slot_t_inv_def, slot_s_inv_def, vec_index_def]) >>
  fs [hash_map_insert_in_list_back_def] >>
  progress >>
  progress >- ((* TODO: *) massage >> fs []) >>
  (* vec_update *)
  qspecl_assume [‘hm.hash_map_slots’, ‘a’, ‘a'’] vec_update_eq >> gvs [] >>
  (* Prove the post-condition *)
  qexists ‘a'’ >>
  rw []
  >-(gvs [insert_in_slot_t_rel_def, hash_mod_key_def, hash_key_fwd_def, vec_index_def, vec_update_def, slot_t_inv_def, slot_s_inv_def] >>
     metis_tac [])
  >-(
    fs [hash_mod_key_def, hash_key_fwd_def, vec_index_def, vec_update_def] >>
    sg_dep_rewrite_goal_tac mk_vec_axiom >> gvs []) >>
  gvs [lookup_s_def, slots_t_lookup_def, slot_t_lookup_def, hash_mod_key_def, hash_key_fwd_def, vec_index_def] >>
  case_tac >> fs []
QED

(* TODO: move *)
Theorem len_FLAT_MAP_update:
  ∀ x ls i.
  0 ≤ i ⇒ i < len ls ⇒
  len (FLAT (MAP list_t_v (update ls i x))) =
  len (FLAT (MAP list_t_v ls)) + len (list_t_v x) - len (list_t_v (index i ls))
Proof
  strip_tac >>
  Induct_on ‘ls’
  >-(rw [len_def] >> int_tac) >>
  rw [] >>
  fs [len_def, index_def, update_def] >>
  Cases_on ‘i = 0’ >> fs [len_append]
  >- int_tac >>
  sg ‘0 < i’ >- int_tac >> fs [len_append] >>
  first_x_assum (qspec_assume ‘i - 1’) >>
  fs [] >>
  (* TODO: automate *)
  sg ‘0 ≤ i - 1 ∧ i - 1 < len ls’ >- int_tac >> fs [] >>
  int_tac
QED

Theorem hash_map_insert_no_resize_fwd_back_spec:
  !hm key value.
    (* Using the base invariant, because the full invariant is preserved only
       if we resize *)
    hash_map_t_base_inv hm ⇒
    (lookup_s hm key = NONE ⇒ len_s hm < usize_max) ⇒
    ∃ hm1. hash_map_insert_no_resize_fwd_back hm key value = Return hm1 ∧
    (* We preserve the invariant *)
    hash_map_t_base_inv hm1 ∧
    (* We updated the binding for key *)
    lookup_s hm1 key = SOME value /\
    (* The other bindings are left unchanged *)
    (!k. k <> key ==> lookup_s hm k = lookup_s hm1 k) ∧
    (* Reasoning about the length *)
    (case lookup_s hm key of
     | NONE => len_s hm1 = len_s hm + 1
     | SOME _ => len_s hm1 = len_s hm)
Proof
  rw [] >>
  qspecl_assume [‘hm’, ‘key’, ‘value’] hash_map_insert_no_resize_fwd_back_spec_aux >> gvs [] >>
  (* TODO: automate this *)
  qspec_assume ‘hm.hash_map_slots’ vec_len_spec >>
  (* TODO: improve massage to not only look at variables *)
  qspec_assume ‘hm.hash_map_num_entries’ usize_to_int_bounds >> fs [] >>
  imp_res_tac hash_map_t_base_inv_len_slots >>
  (* TODO: update usize_rem_spec? *)
  qspecl_assume [‘usize_to_int key’, ‘len (vec_to_list hm.hash_map_slots)’] pos_mod_pos_ineqs >>
  massage >> gvs [] >>
  (* We need the invariant of hm1 to prove some of the postconditions *)
  sg ‘hash_map_t_base_inv hm1’
  >-(
    fs [hash_map_t_base_inv_def, hash_map_t_al_v_def, hash_map_t_v_def] >>
    rw []
    >-(
      sg_dep_rewrite_goal_tac len_FLAT_MAP_update
      >-(fs [hash_mod_key_def, hash_key_fwd_def]) >>
      fs [insert_in_slot_t_rel_def] >>
      fs [hash_mod_key_def, hash_key_fwd_def] >>
      Cases_on ‘lookup_s hm key’ >>
      fs [lookup_s_def, slots_t_lookup_def, slot_t_lookup_def, hash_mod_key_def, hash_key_fwd_def] >>
      int_tac) >>
    fs [slots_t_inv_def, slots_s_inv_def] >>
    rw [] >>
    (* Proof of the slot property: has the slot been updated∃ *)
    Cases_on ‘i = hash_mod_key key (len (vec_to_list hm.hash_map_slots))’ >> fs []
    >-(
      sg_dep_rewrite_goal_tac index_update_diff
      >-(fs [hash_mod_key_def, hash_key_fwd_def]) >>
      fs [insert_in_slot_t_rel_def]) >>
    sg_dep_rewrite_goal_tac index_update_same
    >-(fs [hash_mod_key_def, hash_key_fwd_def]) >>
    fs []) >>
  (* Prove the rest of the postcondition *)
  rw []
  >-((* The binding for key is updated *)
     fs [lookup_s_def, slots_t_lookup_def] >>
     sg_dep_rewrite_goal_tac index_update_diff
     >-(fs [hash_mod_key_def, hash_key_fwd_def]) >>
     fs [insert_in_slot_t_rel_def])
  >-((* The other bindings are unchanged *)
     fs [lookup_s_def, slots_t_lookup_def] >>
     Cases_on ‘hash_mod_key k (len (vec_to_list hm.hash_map_slots)) = hash_mod_key key (len (vec_to_list hm.hash_map_slots))’ >> gvs []
     >-(
        sg_dep_rewrite_goal_tac index_update_diff
        >-(fs [hash_mod_key_def, hash_key_fwd_def]) >>
        fs [insert_in_slot_t_rel_def]) >>
     sg_dep_rewrite_goal_tac index_update_same
     >-(fs [hash_mod_key_def, hash_key_fwd_def] >> irule pos_mod_pos_lt >> massage >> fs []) >>
     fs [insert_in_slot_t_rel_def]) >>
  (* Length *)
  Cases_on ‘lookup_s hm key’ >>
  gvs [insert_in_slot_t_rel_def, hash_map_t_inv_def, hash_map_t_base_inv_def, len_s_def]
QED
val _ = save_spec_thm "hash_map_insert_no_resize_fwd_back_spec"

(*
Theorem nth_mut_fwd_spec:
  !(ls : 't list_t) (i : u32).
    u32_to_int i < len (list_t_v ls) ==>
    case nth_mut_fwd ls i of
    | Return x => x = index (u32_to_int i) (list_t_v ls)
    | Fail _ => F
    | Diverge => F
Proof
  Induct_on ‘ls’ >> rw [list_t_v_def, len_def] >~ [‘ListNil’]
  >-(massage >> int_tac) >>
  pure_once_rewrite_tac [nth_mut_fwd_def] >> rw [] >>
  fs [index_eq] >>
  progress >> progress
QED

val _ = save_spec_thm "nth_mut_fwd_spec"

val _ = new_constant ("insert", “: u32 -> 't -> (u32 # 't) list_t -> (u32 # 't) list_t result”)
val insert_def = new_axiom ("insert_def", “
 insert (key : u32) (value : 't) (ls : (u32 # 't) list_t) : (u32 # 't) list_t result =
  case ls of
  | ListCons (ckey, cvalue) tl =>
    if ckey = key
    then Return (ListCons (ckey, value) tl)
    else
      do
      tl0 <- insert key value tl;
      Return (ListCons (ckey, cvalue) tl0)
      od
  | ListNil => Return (ListCons (key, value) ListNil)
 ”)

(* Property that keys are pairwise distinct *)
val distinct_keys_def = Define ‘
  distinct_keys (ls : (u32 # 't) list) =
    !i j.
      0 ≤ i ⇒ i < j ⇒ j < len ls ⇒
      FST (index i ls) ≠ FST (index j ls)
’

(* Lemma about ‘insert’, without the invariant *)
Theorem insert_lem_aux:
  !ls key value.
    (* The keys are pairwise distinct *)
    case insert key value ls of
    | Return ls1 =>
      (* We updated the binding *)
      lookup key ls1 = SOME value /\
      (* The other bindings are left unchanged *)
      (!k. k <> key ==> lookup k ls = lookup k ls1)
    | Fail _ => F
    | Diverge => F
Proof
  Induct_on ‘ls’ >> rw [list_t_v_def] >~ [‘ListNil’] >>
  pure_once_rewrite_tac [insert_def] >> rw []
  >- (rw [lookup_def, lookup_raw_def, list_t_v_def])
  >- (rw [lookup_def, lookup_raw_def, list_t_v_def]) >>
  case_tac >> rw []
  >- (rw [lookup_def, lookup_raw_def, list_t_v_def])
  >- (rw [lookup_def, lookup_raw_def, list_t_v_def]) >>
  progress >>
  fs [lookup_def, lookup_raw_def, list_t_v_def]
QED

(*
 * Invariant proof 1
 *)

Theorem distinct_keys_cons:
  ∀ k v ls.
  (∀ i. 0 ≤ i ⇒ i < len ls ⇒ FST (index i ls) ≠ k) ⇒
  distinct_keys ls ⇒
  distinct_keys ((k,v) :: ls)
Proof
  rw [] >>
  rw [distinct_keys_def] >>
  Cases_on ‘i = 0’ >> fs []
  >-(
    (* Use the first hypothesis *)
    fs [index_eq] >>
    last_x_assum (qspecl_assume [‘j - 1’]) >>
    sg ‘0 ≤ j - 1’ >- int_tac >>
    fs [len_def] >>
    sg ‘j - 1 < len ls’ >- int_tac >>
    fs []
  ) >>
  (* Use the second hypothesis *)
  sg ‘0 < i’ >- int_tac >>
  sg ‘0 < j’ >- int_tac >>
  fs [distinct_keys_def, index_eq, len_def] >>
  first_x_assum (qspecl_assume [‘i - 1’, ‘j - 1’]) >>
  sg ‘0 ≤ i - 1 ∧ i - 1 < j - 1 ∧ j - 1 < len ls’ >- int_tac >>
  fs []
QED

Theorem distinct_keys_tail:
  ∀ k v ls.
  distinct_keys ((k,v) :: ls) ⇒
  distinct_keys ls
Proof
  rw [distinct_keys_def] >>
  last_x_assum (qspecl_assume [‘i + 1’, ‘j + 1’]) >>
  fs [len_def] >>
  sg ‘0 ≤ i + 1 ∧ i + 1 < j + 1 ∧ j + 1 < 1 + len ls’ >- int_tac >> fs [] >>
  sg ‘0 < i + 1 ∧ 0 < j + 1’ >- int_tac >> fs [index_eq] >>
  sg ‘i + 1 - 1 = i ∧ j + 1 - 1 = j’ >- int_tac >> fs []
QED

Theorem insert_index_neq:
  ∀ q k v ls0 ls1 i.
  (∀ j. 0 ≤ j ∧ j < len (list_t_v ls0) ⇒ q ≠ FST (index j (list_t_v ls0))) ⇒
  q ≠ k ⇒
  insert k v ls0 = Return ls1 ⇒
  0 ≤ i ⇒
  i < len (list_t_v ls1) ⇒
  FST (index i (list_t_v ls1)) ≠ q
Proof
  ntac 3 strip_tac >>
  Induct_on ‘ls0’ >> rw [] >~ [‘ListNil’]
  >-(
    fs [insert_def] >>
    sg ‘ls1 = ListCons (k,v) ListNil’ >- fs [] >> fs [list_t_v_def, len_def] >>
    sg ‘i = 0’ >- int_tac >> fs [index_eq]) >>
  Cases_on ‘t’ >>
  Cases_on ‘i = 0’ >> fs []
  >-(
    qpat_x_assum ‘insert _ _ _ = _’ mp_tac >>
    simp [MK_BOUNDED insert_def 1, bind_def] >>
    Cases_on ‘q' = k’ >> rw []
    >- (fs [list_t_v_def, index_eq]) >>
    Cases_on ‘insert k v ls0’ >> fs [] >>
    gvs [list_t_v_def, index_eq] >>
    first_x_assum (qspec_assume ‘0’) >>
    fs [len_def] >>
    strip_tac >>
    qspec_assume ‘list_t_v ls0’ len_pos >>
    sg ‘0 < 1 + len (list_t_v ls0)’ >- int_tac >>
    fs []) >>
  qpat_x_assum ‘insert _ _ _ = _’ mp_tac >>
  simp [MK_BOUNDED insert_def 1, bind_def] >>
  Cases_on ‘q' = k’ >> rw []
  >-(
    fs [list_t_v_def, index_eq, len_def] >>
    first_x_assum (qspec_assume ‘i’) >> rfs []) >>
  Cases_on ‘insert k v ls0’ >> fs [] >>
  gvs [list_t_v_def, index_eq] >>
  last_x_assum (qspec_assume ‘i - 1’) >>
  fs [len_def] >>
  sg ‘0 ≤ i - 1 ∧ i - 1 < len (list_t_v a)’ >- int_tac >> fs [] >>
  first_x_assum irule >>
  rw [] >>
  last_x_assum (qspec_assume ‘j + 1’) >>
  rfs [] >>
  sg ‘j + 1 < 1 + len (list_t_v ls0) ∧ j + 1 − 1 = j ∧ j + 1 ≠ 0’ >- int_tac >> fs []
QED

Theorem distinct_keys_insert_index_neq:
  ∀ k v q r ls0 ls1 i.
  distinct_keys ((q,r)::list_t_v ls0) ⇒
  q ≠ k ⇒
  insert k v ls0 = Return ls1 ⇒
  0 ≤ i ⇒
  i < len (list_t_v ls1) ⇒
  FST (index i (list_t_v ls1)) ≠ q
Proof
  rw [] >>
  (* Use the first assumption to prove the following assertion *)
  sg ‘∀ j. 0 ≤ j ∧ j < len (list_t_v ls0) ⇒ q ≠ FST (index j (list_t_v ls0))’
  >-(
    strip_tac >>
    fs [distinct_keys_def] >>
    last_x_assum (qspecl_assume [‘0’, ‘j + 1’]) >>
    fs [index_eq] >>
    sg ‘j + 1 - 1 = j’ >- int_tac >> fs [len_def] >>
    rw []>>
    first_x_assum irule >> int_tac) >>
  qspecl_assume [‘q’, ‘k’, ‘v’, ‘ls0’, ‘ls1’, ‘i’] insert_index_neq >>
  fs []
QED

Theorem distinct_keys_insert:
  ∀ k v ls0 ls1.
  distinct_keys (list_t_v ls0) ⇒
  insert k v ls0 = Return ls1 ⇒
  distinct_keys (list_t_v ls1)
Proof
  Induct_on ‘ls0’ >~ [‘ListNil’]
  >-(
    rw [distinct_keys_def, list_t_v_def, insert_def] >>
    fs [list_t_v_def, len_def] >>
    int_tac) >>  
  Cases >>
  pure_once_rewrite_tac [insert_def] >> fs[] >>
  rw [] >> fs []
  >-(
    (* k = q *)
    last_x_assum ignore_tac >>
    fs [distinct_keys_def] >>
    rw [] >>
    last_x_assum (qspecl_assume [‘i’, ‘j’]) >>
    rfs [list_t_v_def, len_def] >>
    sg ‘0 < j’ >- int_tac >>
    Cases_on ‘i = 0’ >> gvs [index_eq]) >>
  (* k ≠ q: recursion *)
  Cases_on ‘insert k v ls0’ >> fs [bind_def] >>
  last_x_assum (qspecl_assume [‘k’, ‘v’, ‘a’]) >>
  gvs [list_t_v_def] >>
  imp_res_tac distinct_keys_tail >> fs [] >>
  irule distinct_keys_cons >> rw [] >>
  metis_tac [distinct_keys_insert_index_neq]
QED  

Theorem insert_lem:
  !ls key value.
    (* The keys are pairwise distinct *)
    distinct_keys (list_t_v ls) ==>
    case insert key value ls of
    | Return ls1 =>
      (* We updated the binding *)
      lookup key ls1 = SOME value /\
      (* The other bindings are left unchanged *)
      (!k. k <> key ==> lookup k ls = lookup k ls1) ∧
      (* The keys are still pairwise disjoint *)
      distinct_keys (list_t_v ls1)
    | Fail _ => F
    | Diverge => F
Proof
  rw [] >>
  qspecl_assume [‘ls’, ‘key’, ‘value’] insert_lem_aux >>
  case_tac >> fs [] >>
  metis_tac [distinct_keys_insert]
QED

(*
 * Invariant proof 2: functional version of the invariant
 *)

Theorem distinct_keys_f_insert_for_all:
  ∀k v k1 ls0 ls1.
  k1 ≠ k ⇒
  for_all (λy. k1 ≠ FST y) (list_t_v ls0) ⇒
  pairwise_rel (λx y. FST x ≠ FST y) (list_t_v ls0) ⇒
  insert k v ls0 = Return ls1 ⇒
  for_all (λy. k1 ≠ FST y) (list_t_v ls1)
Proof
  Induct_on ‘ls0’ >> rw [pairwise_rel_def] >~ [‘ListNil’] >>
  gvs [list_t_v_def, pairwise_rel_def, for_all_def]
  >-(gvs [MK_BOUNDED insert_def 1, bind_def, list_t_v_def, for_all_def]) >>
  pat_undisch_tac ‘insert _ _ _ = _’ >>
  simp [MK_BOUNDED insert_def 1, bind_def] >>
  Cases_on ‘t’ >> rw [] >> gvs [list_t_v_def, pairwise_rel_def, for_all_def] >>
  Cases_on ‘insert k v ls0’ >>
  gvs [distinct_keys_f_def, list_t_v_def, pairwise_rel_def, for_all_def] >>
  metis_tac []
QED

Theorem distinct_keys_f_insert:
  ∀ k v ls0 ls1.
  distinct_keys_f (list_t_v ls0) ⇒
  insert k v ls0 = Return ls1 ⇒
  distinct_keys_f (list_t_v ls1)
Proof
  Induct_on ‘ls0’ >> rw [distinct_keys_f_def] >~ [‘ListNil’]
  >-(
    fs [list_t_v_def, insert_def] >>
    gvs [list_t_v_def, pairwise_rel_def, for_all_def]) >>
  last_x_assum (qspecl_assume [‘k’, ‘v’]) >>
  pat_undisch_tac ‘insert _ _ _ = _’ >>
  simp [MK_BOUNDED insert_def 1, bind_def] >>
  (* TODO: improve case_tac *)
  Cases_on ‘t’ >> rw [] >> gvs [list_t_v_def, pairwise_rel_def, for_all_def] >>
  Cases_on ‘insert k v ls0’ >>
  gvs [distinct_keys_f_def, list_t_v_def, pairwise_rel_def, for_all_def] >>
  metis_tac [distinct_keys_f_insert_for_all]
QED

(*
 * Proving equivalence between the two version - exercise.
 *)
Theorem for_all_quant:
  ∀p ls. for_all p ls ⇔ ∀i. 0 ≤ i ⇒ i < len ls ⇒ p (index i ls)
Proof
  strip_tac >> Induct_on ‘ls’
  >-(rw [for_all_def, len_def] >> int_tac) >>
  rw [for_all_def, len_def, index_eq] >>
  equiv_tac
  >-(
    rw [] >>
    Cases_on ‘i = 0’ >> fs [] >>
    first_x_assum irule >>
    int_tac) >>
  rw []
  >-(
    first_x_assum (qspec_assume ‘0’) >> fs [] >>
    first_x_assum irule >>
    qspec_assume ‘ls’ len_pos >>
    int_tac) >>
  first_x_assum (qspec_assume ‘i + 1’) >>
  fs [] >>
  sg ‘i + 1 ≠ 0 ∧ i + 1 - 1 = i’ >- int_tac >> fs [] >>
  first_x_assum irule >> int_tac
QED

Theorem pairwise_rel_quant:
  ∀p ls. pairwise_rel p ls ⇔
    (∀i j. 0 ≤ i ⇒ i < j ⇒ j < len ls ⇒ p (index i ls) (index j ls))
Proof
  strip_tac >> Induct_on ‘ls’
  >-(rw [pairwise_rel_def, len_def] >> int_tac) >>
  rw [pairwise_rel_def, len_def] >>
  equiv_tac
  >-(
    (* ==> *)
    rw [] >>
    sg ‘0 < j’ >- int_tac >>
    Cases_on ‘i = 0’
    >-(
      simp [index_eq] >>
      qspecl_assume [‘p h’, ‘ls’] (iffLR for_all_quant) >>
      first_x_assum irule >> fs [] >> int_tac
    ) >>
    rw [index_eq] >>
    first_x_assum irule >> int_tac
  ) >>
  (* <== *)
  rw []
  >-(
    rw [for_all_quant] >>
    first_x_assum (qspecl_assume [‘0’, ‘i + 1’]) >>
    sg ‘0 < i + 1 ∧ i + 1 - 1 = i’ >- int_tac >>
    fs [index_eq] >>
    first_x_assum irule >> int_tac
  ) >>
  sg ‘pairwise_rel p ls’
  >-(
    rw [pairwise_rel_def] >>
    first_x_assum (qspecl_assume [‘i' + 1’, ‘j' + 1’]) >>
    sg ‘0 < i' + 1 ∧ 0 < j' + 1’ >- int_tac >>
    fs [index_eq, int_add_minus_same_eq] >>
    first_x_assum irule >> int_tac
  ) >>
  fs []
QED

Theorem distinct_keys_f_eq_distinct_keys:
  ∀ ls.
  distinct_keys_f ls ⇔ distinct_keys ls
Proof
  rw [distinct_keys_def, distinct_keys_f_def] >>
  qspecl_assume [‘(λx y. FST x ≠ FST y)’, ‘ls’] pairwise_rel_quant >>
  fs []
QED

val _ = export_theory ()
*)
