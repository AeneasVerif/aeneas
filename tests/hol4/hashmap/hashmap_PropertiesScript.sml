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
  >-(rw [EVERY_DEF] >> int_tac) >>
  rw [EVERY_DEF, index_eq] >>
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
  >-(rw [pairwise_rel_def] >> int_tac) >>
  rw [pairwise_rel_def] >>
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

(* TODO: the context tends to quickly saturate. In particular:
   - sg_prove_premise_tac leaves the proven assumption in the context, while it shouldn't
   - maybe massage shouldn't leave the introduced inequalities in the context: it is very noisy.
     For instance, int_tac could introduce those inequalities.
 *)

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
val _ = export_rewrites ["list_t_v_def"]

(* Invariants *)
(* TODO: add to srw_ss *)
Definition lookup_def:
  lookup key [] = NONE /\
  lookup key ((k, v) :: ls) =
    if k = key then SOME v else lookup key ls
End
val _ = export_rewrites ["lookup_def"]

Definition slot_t_lookup_def:
  slot_t_lookup key ls = lookup key (list_t_v ls)
End
val _ = export_rewrites ["slot_t_lookup_def"]

Definition remove_def:
  remove key [] = [] ∧
  remove key ((k, v) :: ls) =
    if k = key then ls else (k, v) :: remove key ls
End
val _ = export_rewrites ["remove_def"]

Definition slot_t_remove_def:
  slot_t_remove key ls = remove key (list_t_v ls)
End
val _ = export_rewrites ["slot_t_remove_def"]

Definition hash_mod_key_def:
  hash_mod_key k (l : int) : int =
    case hash_key_fwd k of
    | Return k => usize_to_int k % l
    | _ => ARB
End
val _ = export_rewrites ["hashmap_Funs.hash_key_fwd_def", "hash_mod_key_def"]
val _ = export_rewrites ["primitives.mem_replace_fwd_def", "primitives.mem_replace_back_def"]

Definition slot_s_inv_hash_def:
  slot_s_inv_hash (l : int) (i : int) (ls : (key_t # 'b) list) : bool =
    ∀ k v. MEM (k, v) ls ⇒ hash_mod_key k l = i
End
val _ = export_rewrites ["slot_s_inv_hash_def"]

Definition slot_s_inv_def:
  slot_s_inv (l : int) (i : int) (ls : (key_t # 'b) list) : bool = (
    distinct_keys ls ∧
    slot_s_inv_hash l i ls
  )
End
val _ = export_rewrites ["slot_s_inv_def"]

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
val _ = export_rewrites ["slots_s_inv_def"]

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
    (* TODO: write it as 0 < ... *)
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

(* The invariant that we reveal to the user.

   The conditions about the hash map load factor are a overkill, but we
   want to see how the non-linear arithmetic proofs go.
 *)
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

Definition hash_map_same_params_def:
  hash_map_same_params hm hm1 = (
    hm1.hash_map_max_load_factor = hm.hash_map_max_load_factor ∧
    hm1.hash_map_max_load = hm.hash_map_max_load ∧
    len (vec_to_list hm1.hash_map_slots) = len (vec_to_list hm.hash_map_slots)
  )
End

Theorem hash_map_same_params_refl:
  ∀ hm. hash_map_same_params hm hm
Proof
  fs [hash_map_same_params_def]
QED
val _ = export_rewrites ["hash_map_same_params_refl"]

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
    fs [vec_len_def] >>
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
  progress >> gvs [slots_t_inv_def] >>
  rw [slot_t_inv_def]
  >- fs [EVERY_quant_equiv, distinct_keys_def, pairwise_rel_def] >>
  fs [EVERY_quant_equiv] >>
  qpat_assum ‘∀i. _’ sg_dep_rewrite_all_tac >> gvs []
QED
val _ = save_spec_thm "hash_map_allocate_slots_fwd_spec"

(* Auxiliary lemma *)
Theorem FLAT_ListNil_is_nil:
  EVERY (λx. x = ListNil) ls ⇒ FLAT (MAP list_t_v ls) = []
Proof
  Induct_on ‘ls’ >> fs []
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
  ∀ k. lookup_s hm k = NONE ∧
  len (vec_to_list hm.hash_map_slots) = usize_to_int capacity ∧
  hm.hash_map_max_load_factor = (max_load_dividend,max_load_divisor)
Proof
  rw [] >> fs [hash_map_new_with_capacity_fwd_def] >>
  progress >>
  progress >>
  progress >>
  gvs [hash_map_t_inv_def, hash_map_t_base_inv_def, hash_map_t_al_v_def, hash_map_t_v_def] >>
  rw []
  >-(massage >> sg_dep_rewrite_goal_tac FLAT_ListNil_is_nil >> fs [])
  >-(int_tac)
  >-(massage >> metis_tac [])
  >-(fs [len_s_def, hash_map_t_al_v_def, hash_map_t_v_def] >>
     sg_dep_rewrite_goal_tac FLAT_ListNil_is_nil >> fs []) >>
  fs [lookup_s_def, slots_t_lookup_def] >>
  fs [EVERY_quant_equiv] >>
  (* TODO: sg_dep_rewrite_goal_tac does weird things here *)
  first_x_assum (qspec_assume ‘hash_mod_key k (usize_to_int capacity)’) >>
  first_x_assum sg_premise_tac
  >- (
    fs [] >>
    massage >>
    irule pos_mod_pos_is_pos >> fs []) >>
  first_x_assum sg_premise_tac
  >-(
    fs [] >>
    massage >>
    irule pos_mod_pos_lt >> fs []
  ) >>  
  fs []
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
  fs [slots_t_lookup_def] >> rw []
  >-((* Prove that the invariant is preserved *)
   fs [hash_map_t_inv_def, hash_map_t_base_inv_def, hash_map_t_al_v_def, hash_map_t_v_def] >>
   massage >> fs [] >>
   conj_tac
   >-(
     fs [slots_t_inv_def] >>
     rw [slot_t_inv_def, distinct_keys_def, pairwise_rel_def]) >>
   Cases_on ‘hm.hash_map_max_load_factor’ >> gvs [] >>
   disj1_tac >>
   irule pos_div_pos_is_pos >>
   int_tac) >>
  fs [] >>
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
  fs []
QED
val _ = save_spec_thm "hash_map_clear_fwd_back_spec"
  

(*============================================================================*
 *  Len
 *============================================================================*)

Theorem hash_map_len_spec:
  ∀ hm.
    hash_map_t_base_inv hm ⇒
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
  fs [] >>
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
  Induct_on ‘ls’ >> rw [] >~ [‘ListNil’] >>
  pure_once_rewrite_tac [hash_map_insert_in_list_loop_back_def]
  >- (rw []) >>
  fs [] >- metis_tac [] >>
  progress >> fs [] >> rw []
  >- (metis_tac [])
  >- (metis_tac []) >>
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
  gvs [pairwise_rel_def, EVERY_DEF]
  >-(gvs [MK_BOUNDED hash_map_insert_in_list_loop_back_def 1, bind_def, EVERY_DEF]) >>
  pat_undisch_tac ‘hash_map_insert_in_list_loop_back _ _ _ = _’ >>
  simp [MK_BOUNDED hash_map_insert_in_list_loop_back_def 1, bind_def] >>
  Cases_on ‘u = k’ >> rw [] >> gvs [pairwise_rel_def, EVERY_DEF] >>
  Cases_on ‘hash_map_insert_in_list_loop_back k v ls0’ >>
  gvs [distinct_keys_def, pairwise_rel_def, EVERY_DEF] >>
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
    fs [hash_map_insert_in_list_loop_back_def] >>
    gvs [pairwise_rel_def, EVERY_DEF]) >>
  last_x_assum (qspecl_assume [‘k’, ‘v’]) >>
  pat_undisch_tac ‘hash_map_insert_in_list_loop_back _ _ _ = _’ >>
  simp [MK_BOUNDED hash_map_insert_in_list_loop_back_def 1, bind_def] >>
  Cases_on ‘u = k’ >> rw [] >> gvs [pairwise_rel_def, EVERY_DEF] >>
  Cases_on ‘hash_map_insert_in_list_loop_back k v ls0’ >>
  gvs [distinct_keys_def, pairwise_rel_def, EVERY_DEF] >>
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
  rw [slot_t_inv_def] >>
  qspecl_assume [‘ls’, ‘key’, ‘value’] hash_map_insert_in_list_loop_back_spec_aux >>
  fs [] >>
  qspecl_assume [‘key’, ‘value’, ‘ls’, ‘ls1’] hash_map_insert_in_list_loop_back_distinct_keys >>
  gvs [insert_in_slot_t_rel_def, slot_t_inv_def] >> metis_tac []
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
  (* Remark: we initially used directly hashmap_TypesTheory.recordtype_hash_map_t_seldef_hash_map_slots_fupd_def
     and hashmap_TypesTheory.recordtype_hash_map_t_seldef_hash_map_num_entries_fupd_def,
     but it fails in the Nix derivation *)
  fs (TypeBase.updates_of “:'a hash_map_t”)
QED
val hash_map_insert_no_resize_fwd_back_branches_eq = SIMP_RULE (srw_ss ()) [] hash_map_insert_no_resize_fwd_back_branches_eq

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
     | SOME _ => hm1.hash_map_num_entries = hm.hash_map_num_entries) ∧
    hash_map_same_params hm hm1
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
  >- (fs [lookup_s_def, slots_t_lookup_def, vec_index_def, int_rem_def]) >>
  fs [] >>
  (* TODO: lemma? *)
  sg ‘let l = len (vec_to_list hm.hash_map_slots) in
      slot_t_inv l (usize_to_int key % l) (index (usize_to_int key % l) (vec_to_list hm.hash_map_slots))’
  >-(fs [hash_map_t_base_inv_def, slots_t_inv_def] >>
     last_x_assum (qspec_assume ‘usize_to_int a’) >>
     gvs [vec_index_def, int_rem_def, slot_t_inv_def] >>
     metis_tac []) >>
  fs [] >>
  sg ‘usize_to_int a = usize_to_int key % len (vec_to_list hm.hash_map_slots)’
  >-(fs [int_rem_def]) >>
  sg ‘int_rem (usize_to_int key) (len (vec_to_list hm.hash_map_slots)) = usize_to_int key % len (vec_to_list hm.hash_map_slots)’
  >-(fs [int_rem_def]) >>
  fs [] >>
  sg ‘distinct_keys (list_t_v (vec_index hm.hash_map_slots a))’
  >-(fs [slot_t_inv_def, vec_index_def]) >>
  fs [hash_map_insert_in_list_back_def] >>
  progress >>
  progress >- ((* TODO: *) massage >> fs []) >>
  (* vec_update *)
  qspecl_assume [‘hm.hash_map_slots’, ‘a’, ‘a'’] vec_update_eq >> gvs [] >>
  (* Prove the post-condition *)
  qexists ‘a'’ >>
  rw [hash_map_same_params_def]
  >-(gvs [insert_in_slot_t_rel_def, vec_index_def, vec_update_def, slot_t_inv_def] >>
     metis_tac []) >>
  gvs [lookup_s_def, slots_t_lookup_def, vec_index_def] >>
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
  >-(rw [] >> int_tac) >>
  rw [] >>
  fs [index_def, update_def] >>
  Cases_on ‘i = 0’ >> fs []
  >- int_tac >>
  sg ‘0 < i’ >- int_tac >> fs [] >>
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
     | SOME _ => len_s hm1 = len_s hm) ∧
    hash_map_same_params hm hm1
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
      >-(fs []) >>
      fs [insert_in_slot_t_rel_def] >>
      fs [] >>
      Cases_on ‘lookup_s hm key’ >>
      fs [lookup_s_def, slots_t_lookup_def] >>
      int_tac) >>
    fs [slots_t_inv_def] >>
    rw [] >>
    (* Proof of the slot property: has the slot been updated∃ *)
    Cases_on ‘i = hash_mod_key key (len (vec_to_list hm.hash_map_slots))’ >> fs []
    >-(
      sg_dep_rewrite_goal_tac index_update_diff
      >-(fs []) >>
      fs [insert_in_slot_t_rel_def]) >>
    sg_dep_rewrite_goal_tac index_update_same
    >-(fs []) >>
    fs []) >>
  (* Prove the rest of the postcondition *)
  rw []
  >-((* The binding for key is updated *)
     fs [lookup_s_def, slots_t_lookup_def] >>
     sg_dep_rewrite_goal_tac index_update_diff
     >-(fs []) >>
     fs [insert_in_slot_t_rel_def])
  >-((* The other bindings are unchanged *)
     fs [lookup_s_def, slots_t_lookup_def] >>
     Cases_on ‘hash_mod_key k (len (vec_to_list hm.hash_map_slots)) = hash_mod_key key (len (vec_to_list hm.hash_map_slots))’ >> gvs []
     >-(
        sg_dep_rewrite_goal_tac index_update_diff
        >-(fs []) >>
        fs [insert_in_slot_t_rel_def]) >>
     sg_dep_rewrite_goal_tac index_update_same
     >-(fs [] >> irule pos_mod_pos_lt >> massage >> fs []) >>
     fs [insert_in_slot_t_rel_def]) >>
  (* Length *)
  Cases_on ‘lookup_s hm key’ >>
  gvs [insert_in_slot_t_rel_def, hash_map_t_inv_def, hash_map_t_base_inv_def, len_s_def]
QED
val _ = save_spec_thm "hash_map_insert_no_resize_fwd_back_spec"

(* TODO: move *)
Theorem distinct_keys_MEM_not_eq:
  ∀ ls k1 x1 k2 x2.
  distinct_keys ((k1, x1) :: ls) ⇒
  MEM (k2, x2) ls ⇒
  k2 ≠ k1
Proof
  Induct_on ‘ls’ >> rw [] >>
  fs [distinct_keys_def, pairwise_rel_def, EVERY_DEF] >>
  metis_tac []
QED

Theorem distinct_keys_lookup_NONE:
  ∀ ls k x.
  distinct_keys ((k, x) :: ls) ⇒
  lookup k ls = NONE
Proof
  Induct_on ‘ls’ >> rw [] >>
  fs [distinct_keys_def, pairwise_rel_def, EVERY_DEF] >>
  Cases_on ‘h’ >> fs []
QED

Theorem hash_map_move_elements_from_list_fwd_back_spec:
  ∀ hm ls.
    let l = len (list_t_v ls) in
    hash_map_t_base_inv hm ⇒
    len_s hm + l ≤ usize_max ⇒
    ∃ hm1. hash_map_move_elements_from_list_fwd_back hm ls = Return hm1 ∧
    hash_map_t_base_inv hm1 ∧
    ((∀ k v. MEM (k, v) (list_t_v ls) ⇒ lookup_s hm k = NONE) ⇒
     distinct_keys (list_t_v ls) ⇒
     ((∀ k. slot_t_lookup k ls = NONE ⇒ lookup_s hm1 k = lookup_s hm k) ∧
      (∀ k. slot_t_lookup k ls ≠ NONE ⇒ lookup_s hm1 k = slot_t_lookup k ls) ∧
      len_s hm1 = len_s hm + l)) ∧
    hash_map_same_params hm hm1
Proof
  pure_rewrite_tac [hash_map_move_elements_from_list_fwd_back_def] >>
  Induct_on ‘ls’ >~ [‘ListNil’] >>
  pure_once_rewrite_tac [hash_map_move_elements_from_list_loop_fwd_back_def] >> rw [] >>
  (* TODO: improve massage to not only look at variables *)
  qspec_assume ‘hm.hash_map_num_entries’ usize_to_int_bounds >> fs [] >>
  (* TODO: automate *)
  qspec_assume ‘list_t_v ls’ len_pos >>
  (* Recursive case *)
  progress >>
  progress
  >-(Cases_on ‘lookup_s hm u’ >> fs [len_s_def, hash_map_t_base_inv_def] >> int_tac) >>
  (* Prove the postcondition *)
  (* Drop the induction hypothesis *)
  last_x_assum ignore_tac >>
  gvs [] >>
  sg ‘hash_map_same_params hm a'’ >- fs [hash_map_same_params_def] >> fs [] >>
  (* TODO: we need an intro_tac *)
  strip_tac >>
  strip_tac >>
  fs [hash_map_same_params_def] >>
  (* *)
  sg ‘distinct_keys (list_t_v ls)’
  >-(fs [distinct_keys_def, pairwise_rel_def, EVERY_DEF]) >>
  fs [] >>
  (* For some reason, if we introduce an assumption with [sg], the rewriting
     doesn't work (and I couldn't find any typing issue) *)
  qpat_assum ‘(∀ k v . _) ⇒ _’ assume_tac >>
  first_assum sg_premise_tac
  >-(
    rw [] >>
    sg ‘k ≠ u’ >-(irule distinct_keys_MEM_not_eq >> metis_tac []) >>
    last_x_assum (qspec_assume ‘k’) >>
    gvs [] >>
    first_x_assum (qspecl_assume [‘k’, ‘v’]) >>
    gvs []) >>
  gvs[] >>
  (* *)
  rw []
  >-(
    first_x_assum (qspec_assume ‘k’) >>
    first_x_assum (qspec_assume ‘k’) >>
    fs [] >>
    sg ‘lookup k (list_t_v ls) = NONE’ >-(irule distinct_keys_lookup_NONE >> metis_tac []) >>
    gvs []) >>
  (* The length *)
  fs [] >>
  int_tac
QED
val _ = save_spec_thm "hash_map_move_elements_from_list_fwd_back_spec"

(* TODO: induction theorem for vectors *)
Theorem len_index_FLAT_MAP_list_t_v:
  ∀ slots i.
    0 ≤ i ⇒ i < len slots ⇒
    len (list_t_v (index i slots)) ≤ len (FLAT (MAP list_t_v (drop i slots)))
Proof
  Induct_on ‘slots’ >> rw [vec_index_def, drop_def, index_def, len_pos, update_def, drop_eq] >> try_tac int_tac >> fs [] >>
  last_x_assum (qspec_assume ‘i - 1’) >>
  sg ‘0 ≤ i − 1 ∧ i − 1 < len slots’ >- int_tac >> fs []
QED

Theorem len_vec_FLAT_drop_update:
  ∀ slots i.
  0 ≤ i ⇒ i < len slots ⇒
  len (FLAT (MAP list_t_v (drop i  slots))) =
  len (list_t_v (index i slots)) +
  len (FLAT (MAP list_t_v (drop (i + 1) (update slots i ListNil))))
Proof
  Induct_on ‘slots’ >> fs [drop_def, update_def, len_pos, index_def] >> rw [] >> try_tac int_tac >> fs [drop_eq, len_append] >>
  last_x_assum (qspec_assume ‘i - 1’) >>
  sg ‘0 ≤ i − 1 ∧ i − 1 < len slots ∧ ~(i + 1 < 0) ∧ ~(i + 1 = 0)’ >- int_tac >> fs [] >> sg ‘i + 1 - 1 = i’ >- int_tac >> fs [drop_def]
QED

Theorem MEM_EVERY_not:
  ∀ k v ls.
    MEM (k, v) ls ⇒
    EVERY (\x. k ≠ FST x) ls ⇒
      F  
Proof
  Induct_on ‘ls’ >> rw [EVERY_DEF] >> fs [] >>
  Cases_on ‘h’ >> fs [] >>
  metis_tac []
QED

Theorem MEM_distinct_keys_lookup:
  ∀k v ls.
    MEM (k, v) ls ⇒
    distinct_keys ls ⇒
    lookup k ls = SOME v
Proof
  Induct_on ‘ls’ >> fs [distinct_keys_def, pairwise_rel_def] >>
  rw [] >> fs [] >>
  Cases_on ‘h’ >> fs [] >> rw [] >>
  (* Absurd *)
  exfalso >>
  metis_tac [MEM_EVERY_not]
QED

Theorem lookup_distinct_keys_MEM:
  ∀k v ls.
    lookup k ls = SOME v ⇒
    distinct_keys ls ⇒
    MEM (k, v) ls
Proof
  Induct_on ‘ls’ >> fs [distinct_keys_def, pairwise_rel_def] >>
  rw [] >> fs [] >>
  Cases_on ‘h’ >> fs [] >> rw [] >>
  Cases_on ‘q = k’ >> fs []
QED

Theorem key_MEM_j_lookup_i_is_NONE:
  ∀ i j slots k v.
  usize_to_int i < j ⇒ j < len (vec_to_list slots) ⇒
  (∀j. usize_to_int i ≤ j ⇒
    j < len (vec_to_list slots) ⇒
      slot_t_inv (len (vec_to_list slots)) j (index j (vec_to_list slots))) ⇒
  MEM (k,v) (list_t_v (index j (vec_to_list slots))) ⇒
  slot_t_lookup k (index (usize_to_int i) (vec_to_list slots)) = NONE
Proof
  rw [] >>
  fs [slot_t_inv_def] >>
  (* *)
  first_assum (qspec_assume ‘j’) >> fs [] >>
  pop_assum sg_premise_tac >- int_tac >> fs [] >>
  first_x_assum imp_res_tac >>
  fs [] >>
  (* Prove by contradiction *)
  first_assum (qspec_assume ‘usize_to_int i’) >> fs [] >>
  pop_assum sg_premise_tac >- int_tac >> fs [] >>
  Cases_on ‘slot_t_lookup k (index (usize_to_int i) (vec_to_list slots))’ >> fs [] >>
  sg ‘MEM (k,v) (list_t_v (index (usize_to_int i) (vec_to_list slots)))’
  >- (
    fs [] >>
    metis_tac [lookup_distinct_keys_MEM]
  ) >>
  qpat_x_assum ‘∀k. _’ imp_res_tac >>
  fs []
QED  

(* TODO: the names introduced by progress are random, which is confusing.
   It also makes the proofs less stable.
   Update the progress tactic to use the names given by the let-bindings. *)

Theorem hash_map_move_elements_loop_fwd_back_spec_aux:
  ∀ hm slots i n.
    let slots_l = len (FLAT (MAP list_t_v (drop (usize_to_int i) (vec_to_list slots)))) in
    (* Small trick for the induction *)
    n = len (vec_to_list slots) - usize_to_int i ⇒
    hash_map_t_base_inv hm ⇒
    len_s hm + slots_l ≤ usize_max ⇒
    (∀ j.
      let l = len (vec_to_list slots) in
      usize_to_int i ≤ j ⇒ j < l ⇒
      let slot = index j (vec_to_list slots) in
      slot_t_inv l j slot ∧
      (∀ k v. MEM (k, v) (list_t_v slot) ⇒ lookup_s hm k = NONE)) ⇒
    ∃ hm1 slots1. hash_map_move_elements_loop_fwd_back hm slots i = Return (hm1, slots1) ∧
    hash_map_t_base_inv hm1 ∧
    len_s hm1 = len_s hm + slots_l ∧
    (∀ k. lookup_s hm1 k =
      case lookup_s hm k of
      | SOME v => SOME v
      | NONE =>
        let j = hash_mod_key k (len (vec_to_list slots)) in
        if usize_to_int i ≤ j ∧ j < len (vec_to_list slots) then
          let slot = index j (vec_to_list slots) in
          lookup k (list_t_v slot)
        else NONE
    ) ∧
    hash_map_same_params hm hm1
Proof
  Induct_on ‘n’ >> rw [] >> pure_once_rewrite_tac [hash_map_move_elements_loop_fwd_back_def] >> fs [] >>
  (* TODO: automate *)
  qspec_assume ‘slots’ vec_len_spec >>
  (* TODO: progress on usize_lt *)
  fs [usize_lt_def, vec_len_def] >>
  massage
  >-(
    case_tac >- int_tac >> fs [] >>
    sg_dep_rewrite_goal_tac drop_more_than_length >-(int_tac) >> fs [] >>
    strip_tac >> Cases_on ‘lookup_s hm k’ >> fs [] >>
    fs [] >>
    (* Contradiction *)
    rw [] >> int_tac
    )
  >-(
    (* Same as above - TODO: this is a bit annoying, update the invariant principle (maybe base case is ≤ 0 ?) *)
    sg_dep_rewrite_goal_tac drop_more_than_length >-(int_tac) >> fs [] >>
    strip_tac >> Cases_on ‘lookup_s hm k’ >> fs [] >>
    fs [] >>
    (* Contradiction *)
    rw [] >> int_tac) >>
  (* Recursive case *)
  case_tac >> fs [] >>
  (* Eliminate the trivial case *)
  try_tac (
    sg_dep_rewrite_goal_tac drop_more_than_length >-(int_tac) >> fs [] >>
    strip_tac >> Cases_on ‘lookup_s hm k’ >> fs [] >>
    fs [] >>
    (* Contradiction *)
    rw [] >> int_tac) >>
  progress >- (fs [vec_len_def] >> massage >> fs []) >>
  progress >- (
    fs [vec_index_def] >>
    qspecl_assume [‘vec_to_list slots’, ‘usize_to_int i’] len_index_FLAT_MAP_list_t_v >>
    gvs [] >> int_tac) >>
  (* We just evaluated the call to “hash_map_move_elements_from_list_fwd_back”: prove the assumptions
     in its postcondition *)
  qpat_x_assum ‘_ ⇒ _’ sg_premise_tac
  >-(
    first_x_assum (qspec_assume ‘usize_to_int i’) >> gvs [vec_index_def] >>
    rw []
    >-(first_x_assum irule >> metis_tac []) >>
    fs [slot_t_inv_def]) >>
  gvs [] >>
  (* Continue going forward *)
  progress >>
  progress >- (fs [vec_len_def] >> massage >> fs []) >>
  progress >> fs [] >> qspecl_assume [‘slots’, ‘i’, ‘ListNil’] vec_update_eq >>
  gvs [] >>
  (* Drop the induction hypothesis *)
  last_x_assum ignore_tac
  (* TODO: when we update the theorem, progress lookups the stored (deprecated) rather than
     the inductive hypothesis *)
  (* The preconditions of the recursive call *)
  >- (
    qspecl_assume [‘vec_to_list slots’, ‘usize_to_int i’] len_vec_FLAT_drop_update >> gvs [] >>
    gvs [vec_index_def] >>
    int_tac)
  >-(
    fs [] >>
    sg_dep_rewrite_goal_tac index_update_same
    >-(fs [] >> int_tac) >>
    fs [] >>
    last_x_assum (qspec_assume ‘j’) >> gvs [] >>
    first_assum sg_premise_tac >- int_tac >>
    fs [])
  >-(
    (* Prove that index j (update slots i) = index j slots *)
    first_x_assum (qspec_assume ‘int_to_usize j’) >> gvs [] >> massage >> gvs [] >>
    fs [vec_len_def] >>
    massage >> gvs [] >>
    sg ‘j ≠ usize_to_int i’ >- int_tac >> gvs [vec_index_def, vec_update_def] >>
    massage >>
    (* Use the fact that slot_t_lookup k (index i ... slots) = NONE *)
    first_x_assum (qspec_assume ‘k’) >>
    first_assum sg_premise_tac
    >- (
      sg ‘usize_to_int i < j’ >- int_tac >> fs [] >>
      sg ‘usize_to_int i ≤ j’ >- int_tac >> fs [] >>
      (* TODO: we have to rewrite key_MEM_j_lookup_i_is_NONE before applying
         metis_tac *)
      assume_tac key_MEM_j_lookup_i_is_NONE >> fs [] >>
      metis_tac []) >>
    gvs [] >>
    (* Use the fact that as the key is in the slots after i, it can't be in “hm” (yet) *)
    last_x_assum (qspec_assume ‘j’) >> gvs [] >>
    first_x_assum sg_premise_tac >- (int_tac) >> gvs [] >>
    first_x_assum imp_res_tac >>
    metis_tac []) >>
  (* The conclusion of the theorem (the post-condition) *)
  conj_tac
  >-(
    (* Reasoning about the length *)
    qspecl_assume [‘vec_to_list slots’, ‘usize_to_int i’] len_vec_FLAT_drop_update >>
    gvs [] >>
    fs [GSYM integerTheory.INT_ADD_ASSOC, vec_index_def]) >>
  (* Same params *)
  fs [hash_map_same_params_def] >>
  (* Lookup properties *)
  strip_tac >> fs [] >>
  sg ‘usize_to_int k % len (vec_to_list slots) < len (vec_to_list slots)’
  >- (irule pos_mod_pos_lt >> massage >> fs [] >> int_tac) >> fs [] >>
  Cases_on ‘usize_to_int i = usize_to_int k % len (vec_to_list slots)’ >> fs []
  >- (
    sg ‘~ (usize_to_int i + 1 ≤ usize_to_int k % len (vec_to_list slots))’ >- int_tac >> fs [] >>
    sg ‘~ (usize_to_int k % len (vec_to_list slots) + 1 ≤ usize_to_int k % len (vec_to_list slots))’ >- int_tac >> fs [] >>
    (* Is the key is slot i ? *)
    (* TODO: use key_MEM_j_lookup_i_is_NONE? *)
    Cases_on ‘slot_t_lookup k (vec_index slots i)’ >> gvs [vec_index_def] >>
    (* The key can't be in “hm” *)
    last_x_assum (qspec_assume ‘usize_to_int i’) >>
    pop_assum sg_premise_tac >> fs [] >>
    pop_assum sg_premise_tac >> fs [] >>
    pop_assum (qspecl_assume [‘k’, ‘x’]) >>
    pop_assum sg_premise_tac
    >-(irule lookup_distinct_keys_MEM >> gvs [slot_t_inv_def]) >> fs []) >>
  (* Here: usize_to_int i ≠ usize_to_int k % len (vec_to_list slots) *)
  Cases_on ‘usize_to_int i ≤ usize_to_int k % len (vec_to_list slots)’ >> fs []
  >- (
    (* We have: usize_to_int i < usize_to_int k % len (vec_to_list slots)
       The key is not in slot i, and is added (eventually) with the recursive call on
       the remaining the slots.
     *)
    sg ‘usize_to_int i < usize_to_int k % len (vec_to_list slots)’ >- int_tac >> fs [] >>
    sg ‘usize_to_int i + 1 ≤ usize_to_int k % len (vec_to_list slots)’ >- int_tac >> fs [] >>
    (* We just need to use the fact that “lookup_s a' k = lookup_s hm k” *)
    sg ‘lookup_s a' k = lookup_s hm k’
    >- (
      first_x_assum irule  >>
      last_x_assum (qspec_assume ‘usize_to_int i’) >> gvs [] >>
      (* Prove by contradiction - TODO: turn this into a lemma? *)
      gvs [slot_t_inv_def] >>
      Cases_on ‘slot_t_lookup k (vec_index slots i)’ >> fs [vec_index_def] >> exfalso >>
      fs [] >>
      imp_res_tac lookup_distinct_keys_MEM >>
      sg ‘usize_to_int k % len (vec_to_list slots) = usize_to_int i’ >- metis_tac [] >> fs []
      ) >>
    fs [] >>
    case_tac >>
    fs [] >>
    sg_dep_rewrite_goal_tac index_update_same >> fs []
  ) >>
  (* Here: usize_to_int i > usize_to_int k % ... *)
  sg ‘~(usize_to_int i + 1 ≤ usize_to_int k % len (vec_to_list slots))’ >- int_tac >> fs [] >>
  sg ‘lookup_s a' k = lookup_s hm k’
  >- (
    first_x_assum irule >>
    (* We have to prove that the key is not in slot i *)
    last_x_assum (qspec_assume ‘usize_to_int i’) >>
    pop_assum sg_premise_tac >> fs [] >>
    pop_assum sg_premise_tac >> fs [] >>
    gvs [slot_t_inv_def] >>
    (* Prove by contradiction *)
    Cases_on ‘slot_t_lookup k (vec_index slots i)’ >> fs [vec_index_def] >> exfalso >>
    fs [] >>
    imp_res_tac lookup_distinct_keys_MEM >>
    sg ‘usize_to_int k % len (vec_to_list slots) = usize_to_int i’ >- metis_tac [] >> fs []
  ) >>
  fs []
QED

Theorem hash_map_move_elements_fwd_back_spec:
  ∀ hm slots i.
    let slots_l = len (FLAT (MAP list_t_v (drop (usize_to_int i) (vec_to_list slots)))) in
    hash_map_t_base_inv hm ⇒
    len_s hm + slots_l ≤ usize_max ⇒
    (∀ j.
      let l = len (vec_to_list slots) in
      usize_to_int i ≤ j ⇒ j < l ⇒
      let slot = index j (vec_to_list slots) in
      slot_t_inv l j slot ∧
      (∀ k v. MEM (k, v) (list_t_v slot) ⇒ lookup_s hm k = NONE)) ⇒
    ∃ hm1 slots1. hash_map_move_elements_fwd_back hm slots i = Return (hm1, slots1) ∧
    hash_map_t_base_inv hm1 ∧
    len_s hm1 = len_s hm + slots_l ∧
    (∀ k. lookup_s hm1 k =
      case lookup_s hm k of
      | SOME v => SOME v
      | NONE =>
        let j = hash_mod_key k (len (vec_to_list slots)) in
        if usize_to_int i ≤ j ∧ j < len (vec_to_list slots) then
          let slot = index j (vec_to_list slots) in
          lookup k (list_t_v slot)
        else NONE
    ) ∧
    hash_map_same_params hm hm1
Proof
  rw [hash_map_move_elements_fwd_back_def] >>
  qspecl_assume [‘hm’, ‘slots’, ‘i’] hash_map_move_elements_loop_fwd_back_spec_aux >> gvs [] >>
  pop_assum sg_premise_tac >- metis_tac [] >>
  metis_tac []
QED
val _ = save_spec_thm "hash_map_move_elements_fwd_back_spec"

(* We assume that usize = u32 - TODO: update the implementation of the hash map *)
val usize_u32_bounds = new_axiom ("usize_u32_bounds", “usize_max = u32_max”)

(* Predicate to characterize the state of the hash map just before we resize.

   The "full" invariant is broken, as we call [try_resize]
   only if the current number of entries is > the max load.

   There are two situations:
   - either we just reached the max load
   - or we were already saturated and can't resize *)
Definition hash_map_just_before_resize_pred_def:
  hash_map_just_before_resize_pred hm =
    let (dividend, divisor) = hm.hash_map_max_load_factor in
    (usize_to_int hm.hash_map_num_entries = usize_to_int hm.hash_map_max_load + 1 ∧
     len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int dividend ≤ usize_max) \/
    len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int dividend > usize_max
End

Theorem hash_map_try_resize_fwd_back_spec:
  ∀ hm.
    (* The base invariant is satisfied *)
    hash_map_t_base_inv hm ⇒
    hash_map_just_before_resize_pred hm ⇒
    ∃ hm1. hash_map_try_resize_fwd_back hm = Return hm1 ∧
    hash_map_t_inv hm1 ∧
    len_s hm1 = len_s hm ∧
    (∀ k. lookup_s hm1 k = lookup_s hm k)
Proof
  rw [hash_map_try_resize_fwd_back_def] >>
  (* “_ <-- mk_usize (u32_to_int core_num_u32_max_c)” *)
  assume_tac usize_u32_bounds >>
  fs [core_u32_max_def, u32_max_def] >>
  massage >> fs [mk_usize_def, u32_max_def] >>
  (* / 2 *)
  progress >>
  Cases_on ‘hm.hash_map_max_load_factor’ >> fs [] >>
  progress >- (fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac) >> gvs [] >>
  (* usize_le *)
  fs [usize_le_def, vec_len_def] >>
  (* TODO: automate *)
  qspec_assume ‘hm.hash_map_slots’ vec_len_spec >> fs [vec_len_def] >>
  massage >>
  case_tac >>
  (* Eliminate the case where we don't resize the hash_map *)
  try_tac (
    gvs [hash_map_t_inv_def, hash_map_t_base_inv_def, hash_map_just_before_resize_pred_def,
         len_s_def, hash_map_t_al_v_def, hash_map_t_v_def, lookup_s_def] >>
    (* Contradiction *)
    exfalso >>
    sg ‘len (vec_to_list hm.hash_map_slots) > 2147483647 / usize_to_int q’ >- int_tac >>
    sg ‘len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int q / 2 = len (vec_to_list hm.hash_map_slots) * usize_to_int q’
    >- (
      sg ‘len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int q = (len (vec_to_list hm.hash_map_slots) * usize_to_int q) * 2’
      >- (metis_tac [integerTheory.INT_MUL_COMM, integerTheory.INT_MUL_ASSOC]) >>
      fs [] >>
      irule integerTheory.INT_DIV_RMUL >> fs []) >>
    gvs [] >>
    sg ‘(len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int q) / 2 ≤ usize_max / 2’
    >-(irule pos_div_pos_le >> int_tac) >>
    sg ‘len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int q / 2 = len (vec_to_list hm.hash_map_slots) * usize_to_int q’
    >- (
      sg ‘len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int q = (len (vec_to_list hm.hash_map_slots) * usize_to_int q) * 2’
      >- (metis_tac [integerTheory.INT_MUL_COMM, integerTheory.INT_MUL_ASSOC]) >>
      fs [] >>
      irule integerTheory.INT_DIV_RMUL >> fs []) >>
    gvs [] >>
    sg ‘len (vec_to_list hm.hash_map_slots) * usize_to_int q / usize_to_int q ≤ usize_max / 2 / usize_to_int q’
    >-(irule pos_div_pos_le >> int_tac) >>
    sg ‘len (vec_to_list hm.hash_map_slots) * usize_to_int q / usize_to_int q = len (vec_to_list hm.hash_map_slots)’
    >- (irule integerTheory.INT_DIV_RMUL >> int_tac) >>
    gvs [] >>
    fail_tac "") >>
  (* Resize the hashmap *)
  sg ‘0 < usize_to_int q’ >- fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >>
  sg ‘len (vec_to_list hm.hash_map_slots) * 2 ≤ usize_max’
  >-(
    sg ‘len (vec_to_list hm.hash_map_slots) ≤ 2147483647’
    >-(
      qspecl_assume [‘2147483647’, ‘usize_to_int q’] pos_div_pos_le_init >> fs [] >>
      gvs [] >> int_tac
    ) >>
    sg ‘len (vec_to_list hm.hash_map_slots) * 2 ≤ 2147483647 * 2’
    >- (irule mul_pos_right_le >> fs []) >>
    fs [] >> int_tac
  ) >>
  progress >> gvs [] >>
  sg ‘0 < len (vec_to_list hm.hash_map_slots)’
  >- (fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac) >>
  (* TODO: automate *)
  sg ‘0 < len (vec_to_list hm.hash_map_slots) * 2’
  >- (irule int_arithTheory.positive_product_implication >> fs []) >>
  sg ‘len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int q ≥ usize_to_int r’
  >- (
    sg ‘len (vec_to_list hm.hash_map_slots) * usize_to_int q >= usize_to_int r’
    >- (fs [hash_map_t_inv_def, hash_map_t_base_inv_def]) >>
    sg ‘len (vec_to_list hm.hash_map_slots) * usize_to_int q ≤
        2 * (len (vec_to_list hm.hash_map_slots) * usize_to_int q)’
    >- (irule  pos_mul_left_pos_le >> fs []) >>
    sg ‘len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int q =
        2 * (len (vec_to_list hm.hash_map_slots) * usize_to_int q)’
    >- (metis_tac [integerTheory.INT_MUL_COMM, integerTheory.INT_MUL_ASSOC]) >>
    int_tac
   ) >>
  sg ‘len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int q ≤ usize_max’
  >- (
    sg ‘len (vec_to_list hm.hash_map_slots) * usize_to_int q ≤ (2147483647 / usize_to_int q) * usize_to_int q’
    >- (irule mul_pos_right_le >> fs []) >>
    sg ‘2147483647 / usize_to_int q * usize_to_int q ≤ 2147483647’
    >- (irule pos_div_pos_mul_le >> fs []) >>
    int_tac
    ) >>
  (* TODO: don't make progress transform conjunctions to implications *)
  progress >> try_tac (fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> fail_tac "") >>
  (* TODO: annoying that the rewriting tactics make the case disjunction over the “∨” *)
  sg ‘hash_map_t_base_inv hm’ >- fs [hash_map_t_inv_def] >>
  progress
  >-(fs [hash_map_t_inv_def])
  >-(fs [drop_eq, hash_map_t_base_inv_def, hash_map_t_v_def, hash_map_t_al_v_def] >>
     (* TODO: automate *)
     qspec_assume ‘hm.hash_map_num_entries’ usize_to_int_bounds >> fs [] >>
     int_tac)
  >-(fs [hash_map_t_base_inv_def, slots_t_inv_def]) >>
  pure_rewrite_tac [hash_map_t_inv_def] >>
  fs [len_s_def, hash_map_t_base_inv_def, hash_map_t_al_v_def, hash_map_t_v_def, drop_eq] >>
  gvs [] >>
  (* TODO: lookup post condition, parameters for the new_with_capacity *)
  conj_tac
  >-(
    (* Length *)
    gvs [hash_map_same_params_def, hash_map_just_before_resize_pred_def] >> try_tac int_tac >>
    (* We are in the case where we managed to resize the hash map *)
    disj1_tac >>
    sg ‘0 < len (vec_to_list hm.hash_map_slots) * usize_to_int q / usize_to_int r’
    >- (
      sg ‘len (vec_to_list hm.hash_map_slots) * usize_to_int q / usize_to_int r ≥ usize_to_int r / usize_to_int r’
      >- (irule pos_div_pos_ge >> int_tac) >>
      sg ‘usize_to_int r / usize_to_int r = 1’
      >- (irule integerTheory.INT_DIV_ID >> int_tac) >>
      int_tac
      ) >>
    sg ‘len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int q = (len (vec_to_list hm.hash_map_slots) * usize_to_int q) * 2’
    >- metis_tac [integerTheory.INT_MUL_COMM, integerTheory.INT_MUL_ASSOC] >>
    fs [] >>
    sg ‘len (vec_to_list hm.hash_map_slots) * usize_to_int q / usize_to_int r +
        len (vec_to_list hm.hash_map_slots) * usize_to_int q / usize_to_int r ≤
        (len (vec_to_list hm.hash_map_slots) * usize_to_int q) * 2 / usize_to_int r’
    >- (irule pos_mul_2_div_pos_decompose >> int_tac) >>
    int_tac) >>
  rw [] >>
  first_x_assum (qspec_assume ‘k’) >>
  gvs [slots_t_lookup_def, lookup_s_def] >>
  massage >>
  sg ‘0 ≤ usize_to_int k % len (vec_to_list hm.hash_map_slots)’
  >- (irule pos_mod_pos_is_pos >> fs [] >> int_tac) >> fs [] >>
  sg ‘usize_to_int k % len (vec_to_list hm.hash_map_slots) < len (vec_to_list hm.hash_map_slots)’
  >- (irule pos_mod_pos_lt >> fs [] >> int_tac) >> fs []
QED
val _ = save_spec_thm "hash_map_try_resize_fwd_back_spec"

Theorem hash_map_insert_fwd_back_spec:
  ∀ hm key value.
    hash_map_t_inv hm ⇒
    (* We can insert *)
    (lookup_s hm key = NONE ⇒ len_s hm < usize_max) ⇒
    ∃ hm1. hash_map_insert_fwd_back hm key value = Return hm1 ∧
    (* We preserve the invariant *)
    hash_map_t_inv hm1 ∧
    (* We updated the binding for key *)
    lookup_s hm1 key = SOME value /\
    (* The other bindings are left unchanged *)
    (!k. k <> key ==> lookup_s hm k = lookup_s hm1 k) ∧
    (* Reasoning about the length *)
    (case lookup_s hm key of
     | NONE => len_s hm1 = len_s hm + 1
     | SOME _ => len_s hm1 = len_s hm)
Proof
  rw [hash_map_insert_fwd_back_def] >>
  progress
  >- (fs [hash_map_t_inv_def]) >>
  gvs [] >>
  progress >>
  Cases_on ‘~(usize_gt x a.hash_map_max_load)’ >> fs []
  >-(
    gvs [hash_map_t_inv_def, hash_map_same_params_def] >>
    sg ‘len_s a = usize_to_int a.hash_map_num_entries’
    >- (fs [hash_map_t_base_inv_def, len_s_def]) >>
    fs [usize_gt_def] >>
    sg ‘usize_to_int a.hash_map_num_entries ≤ usize_to_int hm.hash_map_max_load’ >- int_tac >>
    fs [] >>
    Cases_on ‘hm.hash_map_max_load_factor’ >> fs []
  ) >>
  gvs [] >>
  progress >>
  fs [hash_map_just_before_resize_pred_def, usize_gt_def, hash_map_same_params_def] >>
  (* The length is the same: two cases depending on whether the map was already saturated or not *)
  fs [hash_map_t_inv_def] >> Cases_on ‘hm.hash_map_max_load_factor’ >> fs [] >>
  (* Remaining case: the map was not saturated *)
  (* Reasoning about the length in the cases the key was already present or not *)
  Cases_on ‘lookup_s hm key’ >> gvs []
  >-(
    Cases_on ‘~(len (vec_to_list hm.hash_map_slots) * 2 * usize_to_int q ≤ usize_max)’ >> fs []
    >- int_tac >>
    (* Not already present: we incremented the length. The map is also not saturated *)
    disj1_tac >>
    sg ‘len_s hm ≤ usize_to_int hm.hash_map_max_load’
    >- (gvs [hash_map_t_base_inv_def, len_s_def]) >>
    fs [hash_map_t_base_inv_def, len_s_def] >>
    int_tac
  ) >>
  (* The length is the same and the map was not saturated but we resized: contradiction *)
  exfalso >>
  sg ‘len_s hm ≤ usize_to_int hm.hash_map_max_load’
  >- (gvs [hash_map_t_base_inv_def, len_s_def]) >>
  int_tac  
QED
val _ = save_spec_thm "hash_map_insert_fwd_back_spec"

Theorem hash_map_contains_key_in_list_fwd_spec:
  ∀ key ls.
  hash_map_contains_key_in_list_fwd key ls = Return (slot_t_lookup key ls ≠ NONE)
Proof
  fs [hash_map_contains_key_in_list_fwd_def] >>
  Induct_on ‘ls’ >>
  pure_once_rewrite_tac [hash_map_contains_key_in_list_loop_fwd_def] >>
  fs [] >>
  (* There remains only the recursive case *)
  rw []
QED
val _ = save_spec_thm "hash_map_contains_key_in_list_fwd_spec"

Theorem hash_map_contains_key_fwd_spec:
  ∀ hm key.
  hash_map_t_inv hm ⇒
  hash_map_contains_key_fwd hm key = Return (lookup_s hm key ≠ NONE)
Proof
  fs [hash_map_contains_key_fwd_def] >>
  fs [hash_key_fwd_def] >>
  rw [] >>
  (* TODO: automate *)
  qspec_assume ‘hm.hash_map_slots’ vec_len_spec >> fs [] >>
  progress >> gvs []
  >- (
    fs [hash_map_t_inv_def, hash_map_t_base_inv_def, vec_len_def] >>
    massage >> int_tac) >>
  progress >> massage >> gvs [int_rem_def]
  >- (irule pos_mod_pos_lt >> fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac) >>
  progress >>
  fs [lookup_s_def, vec_index_def, slots_t_lookup_def]
QED
val _ = save_spec_thm "hash_map_contains_key_fwd_spec"

Theorem hash_map_get_in_list_fwd_spec:
  ∀ ls key.
  case hash_map_get_in_list_fwd key ls of
  | Diverge => F
  | Fail _ => slot_t_lookup key ls = NONE
  | Return x => slot_t_lookup key ls = SOME x
Proof
  fs [hash_map_get_in_list_fwd_def] >>
  Induct_on ‘ls’ >> pure_once_rewrite_tac [hash_map_get_in_list_loop_fwd_def] >>
  fs [] >>
  rw []
QED
val _ = save_spec_thm "hash_map_get_in_list_fwd_spec"

Theorem hash_map_get_fwd_spec:
  ∀ hm key.
  hash_map_t_inv hm ⇒
  case hash_map_get_fwd hm key of
  | Diverge => F
  | Fail _ => lookup_s hm key = NONE
  | Return x => lookup_s hm key = SOME x
Proof
  rw [hash_map_get_fwd_def] >>
  fs [hash_key_fwd_def] >>
  (* TODO: automate *)
  qspec_assume ‘hm.hash_map_slots’ vec_len_spec >> fs [] >>
  progress >> gvs []
  >- (
    fs [hash_map_t_inv_def, hash_map_t_base_inv_def, vec_len_def] >>
    massage >> int_tac) >>
  progress >> massage >> gvs [int_rem_def]
  >- (irule pos_mod_pos_lt >> fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac) >>
  progress >>
  gvs [lookup_s_def, vec_index_def, slots_t_lookup_def]
QED
val _ = save_spec_thm "hash_map_get_fwd_spec"

Theorem hash_map_get_mut_in_list_fwd_spec:
  ∀ ls key.
  case hash_map_get_mut_in_list_fwd ls key of
  | Diverge => F
  | Fail _ => slot_t_lookup key ls = NONE
  | Return x => slot_t_lookup key ls = SOME x
Proof
  fs [hash_map_get_mut_in_list_fwd_def] >>
  Induct_on ‘ls’ >> pure_once_rewrite_tac [hash_map_get_mut_in_list_loop_fwd_def] >>
  fs [] >>
  rw []
QED
val _ = save_spec_thm "hash_map_get_mut_in_list_fwd_spec"

Theorem hash_map_get_mut_fwd_spec:
  ∀ hm key.
  hash_map_t_inv hm ⇒
  case hash_map_get_mut_fwd hm key of
  | Diverge => F
  | Fail _ => lookup_s hm key = NONE
  | Return x => lookup_s hm key = SOME x
Proof
  rw [hash_map_get_mut_fwd_def] >>
  fs [hash_key_fwd_def] >>
  (* TODO: automate *)
  qspec_assume ‘hm.hash_map_slots’ vec_len_spec >> fs [] >>
  progress >> gvs []
  >- (
    fs [hash_map_t_inv_def, hash_map_t_base_inv_def, vec_len_def] >>
    massage >> int_tac) >>
  progress >> massage >> gvs [int_rem_def]
  >- (irule pos_mod_pos_lt >> fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac) >>
  progress >>
  gvs [lookup_s_def, vec_index_def, slots_t_lookup_def]
QED
val _ = save_spec_thm "hash_map_get_mut_fwd_spec"

Theorem hash_map_get_mut_in_list_back_spec:
  ∀ ls key nx.
  slot_t_lookup key ls ≠ NONE ⇒
  ∃ nls. hash_map_get_mut_in_list_back ls key nx = Return nls ∧
  slot_t_lookup key nls = SOME nx ∧
  (∀ k. k ≠ key ⇒ slot_t_lookup k nls = slot_t_lookup k ls)
Proof
  fs [hash_map_get_mut_in_list_back_def] >>
  Induct_on ‘ls’ >> pure_once_rewrite_tac [hash_map_get_mut_in_list_loop_back_def] >>
  fs [] >>
  rw [] >>
  fs [] >>
  progress >>
  fs []  
QED
val _ = save_spec_thm "hash_map_get_mut_in_list_back_spec"

Theorem hash_map_get_mut_back_spec:
  ∀ hm key nx.
  lookup_s hm key ≠ NONE ⇒
  hash_map_t_inv hm ⇒
  ∃ hm1. hash_map_get_mut_back hm key nx = Return hm1 ∧
  lookup_s hm1 key = SOME nx ∧
  (∀ k. k ≠ key ⇒ lookup_s hm1 k = lookup_s hm k)
Proof
  rw [hash_map_get_mut_back_def] >>
  fs [hash_key_fwd_def] >>
  (* TODO: automate *)
  qspec_assume ‘hm.hash_map_slots’ vec_len_spec >> fs [] >>
  progress >> gvs []
  >- (
    fs [hash_map_t_inv_def, hash_map_t_base_inv_def, vec_len_def] >>
    massage >> int_tac) >>
  progress >> massage >> gvs [int_rem_def]
  (* TODO: we did this proof many times *)
  >- (irule pos_mod_pos_lt >> fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac) >>
  progress >>
  gvs [lookup_s_def, vec_index_def, slots_t_lookup_def] >>
  progress
  (* TODO: again the same proof *)
  >- (massage >> irule pos_mod_pos_lt >> fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac) >>
  gvs [] >>
  conj_tac
  >-(
    sg_dep_rewrite_goal_tac index_update_diff
    >- (fs [] >> irule pos_mod_pos_lt >> fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac) >>
    fs []
  ) >>
  rw [] >>
  Cases_on ‘usize_to_int k % len (vec_to_list hm.hash_map_slots) = usize_to_int key % len (vec_to_list hm.hash_map_slots)’ >>
  fs []
  >- (
    sg_dep_rewrite_goal_tac index_update_diff
    >- (fs [] >> irule pos_mod_pos_lt >> fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac) >>
    fs []
  ) >>
  sg_dep_rewrite_goal_tac index_update_same
  >- (
    rw []
    >- (irule pos_mod_pos_lt >> massage >> fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac)
    >- (irule pos_mod_pos_lt >> massage >> fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac)
  ) >>
  fs []
QED
val _ = save_spec_thm "hash_map_get_mut_back_spec"

Theorem hash_map_remove_from_list_fwd_spec:
  ∀ key l i ls.
  hash_map_remove_from_list_fwd key ls = Return (slot_t_lookup key ls)
Proof
  fs [hash_map_remove_from_list_fwd_def] >>
  Induct_on ‘ls’ >> pure_once_rewrite_tac [hash_map_remove_from_list_loop_fwd_def] >>
  rw [] >>
  metis_tac []
QED
val _ = save_spec_thm "hash_map_remove_from_list_fwd_spec"

Theorem lookup_SOME_not_empty:
  ∀ ls k. lookup k ls ≠ NONE ⇒ 0 < len ls
Proof
  Induct_on ‘ls’ >> fs [] >> rw [] >>
  qspec_assume ‘ls’ len_pos >>
  int_tac
QED

Theorem slot_t_lookup_SOME_not_empty:
  ∀ ls i k.
  0 ≤ i ⇒
  i < len ls ⇒
  slot_t_lookup k (index i ls) ≠ NONE ⇒
  0 < len (FLAT (MAP list_t_v ls))
Proof
  Induct_on ‘ls’ >> rw [] >> try_tac int_tac >>
  gvs [index_eq] >>
  Cases_on ‘i = 0’ >> fs []
  >-(
    qspec_assume ‘FLAT (MAP list_t_v ls)’ len_pos >>
    imp_res_tac lookup_SOME_not_empty >> int_tac
  ) >>
  qspec_assume ‘list_t_v h’ len_pos >>
  last_x_assum (qspecl_assume [‘i - 1’, ‘k’]) >>
  sg ‘0 ≤ i - 1 ∧ i - 1 < len ls ∧ i ≠ 0’ >- int_tac >>
  gvs [] >>
  int_tac
QED

Theorem lookup_s_SOME_not_empty:
  ∀ hm key.
    hash_map_t_inv hm ⇒
    lookup_s hm key ≠ NONE ⇒ 0 < len_s hm
Proof
  rw [lookup_s_def, slots_t_lookup_def, len_s_def, hash_map_t_al_v_def, hash_map_t_v_def] >>
  sg ‘0 < len (vec_to_list hm.hash_map_slots)’
  >- (fs [hash_map_t_inv_def, hash_map_t_base_inv_def] >> int_tac) >>
  irule slot_t_lookup_SOME_not_empty >>
  qexists ‘usize_to_int key % len (vec_to_list hm.hash_map_slots)’ >>
  qexists ‘key’ >>
  rw []
  >-(irule pos_mod_pos_is_pos >> massage >> int_tac) >>
  irule pos_mod_pos_lt >> massage >> int_tac
QED

Theorem hash_map_remove_fwd_spec:
  ∀ hm key.
  hash_map_t_inv hm ⇒
  hash_map_remove_fwd hm key = Return (lookup_s hm key)
Proof
  rw [hash_map_remove_fwd_def] >>
  (* TODO: automate *)
  qspec_assume ‘hm.hash_map_slots’ vec_len_spec >> fs [] >>
  sg ‘0 < usize_to_int (vec_len hm.hash_map_slots)’
  >- (fs [hash_map_t_inv_def, hash_map_t_base_inv_def, vec_len_def] >> massage >> int_tac) >>
  fs [vec_len_def] >> massage >>
  (* TODO: rewriting for: usize_to_int (int_to_usize (len (vec_to_list v))) = len (vec_to_list v) *)
  progress >>
  progress >> fs [int_rem_def, vec_len_def] >> massage
  >- (irule pos_mod_pos_lt >> fs []) >>
  progress >>
  gvs [lookup_s_def, slots_t_lookup_def, vec_index_def] >>
  case_tac >> fs [] >>
  progress >>
  (* Prove that we can decrement the number of entries *)
  qspecl_assume [‘hm’, ‘key’] lookup_s_SOME_not_empty >>
  gvs [lookup_s_def, slots_t_lookup_def, len_s_def, hash_map_t_inv_def, hash_map_t_base_inv_def] >>
  int_tac
QED
val _ = save_spec_thm "hash_map_remove_fwd_spec"

Theorem every_distinct_remove_every_distinct:
  ∀ k0 k1 ls0.
  EVERY (λy. k1 ≠ FST y) ls0 ⇒
  EVERY (λy. k1 ≠ FST y) (remove k0 ls0)
Proof
  Induct_on ‘ls0’ >> fs [] >> rw [] >>
  Cases_on ‘h’ >> fs [] >>
  case_tac >> fs []
QED

Theorem hash_map_remove_from_list_back_spec:
  ∀ key ls.
  ∃ ls1. hash_map_remove_from_list_back key ls = Return ls1 ∧
  (∀ l i. slot_t_inv l i ls ⇒
    slot_t_inv l i ls1 ∧
    list_t_v ls1 = remove key (list_t_v ls) ∧
    slot_t_lookup key ls1 = NONE ∧
    (∀ k. k ≠ key ⇒ slot_t_lookup k ls1 = slot_t_lookup k ls) ∧
    (case slot_t_lookup key ls of
     | NONE => len (list_t_v ls1) = len (list_t_v ls)
     | SOME _ => len (list_t_v ls1) = len (list_t_v ls) - 1))
Proof
  fs [hash_map_remove_from_list_back_def] >>
  Induct_on ‘ls’ >> pure_once_rewrite_tac [hash_map_remove_from_list_loop_back_def] >>
  fs [slot_t_inv_def] >>
  fs [distinct_keys_def, pairwise_rel_def] >>
  rw []
  >- (metis_tac [])
  >- (
    last_x_assum ignore_tac >>
    pop_assum ignore_tac >>
    pop_assum ignore_tac >>
    Induct_on ‘ls’ >> fs []
  ) >>
  progress >>
  rw [] >> gvs [pairwise_rel_def]
  >- metis_tac [every_distinct_remove_every_distinct]
  >- metis_tac []
  >- metis_tac []
  >- metis_tac []
  >- metis_tac [] >>
  case_tac >> fs [] >- metis_tac [] >>
  first_x_assum (qspecl_assume [‘l’, ‘i’]) >> gvs [] >>
  pop_assum sg_premise_tac >- metis_tac [] >> fs []
QED
val _ = save_spec_thm "hash_map_remove_from_list_back_spec"

(* TODO: automate this *)
Theorem hash_map_remove_back_branch_eq:
  ∀ key hm a.
  (case lookup key (list_t_v (vec_index hm.hash_map_slots a)) of
    NONE =>
      do
        l0 <-
          hash_map_remove_from_list_back key
            (vec_index hm.hash_map_slots a);
        v <- vec_index_mut_back hm.hash_map_slots a l0;
        Return (hm with hash_map_slots := v)
      od
  | SOME x0 =>
    do
      i0 <- usize_sub hm.hash_map_num_entries (int_to_usize 1);
      l0 <-
        hash_map_remove_from_list_back key
          (vec_index hm.hash_map_slots a);
      v <- vec_index_mut_back hm.hash_map_slots a l0;
      Return
        (hm with <|hash_map_num_entries := i0; hash_map_slots := v|>)
    od) =
  (do
   i0 <- (case lookup key (list_t_v (vec_index hm.hash_map_slots a)) of
         | NONE => Return hm.hash_map_num_entries
         | SOME _ => usize_sub hm.hash_map_num_entries (int_to_usize 1));
   l0 <-
     hash_map_remove_from_list_back key
       (vec_index hm.hash_map_slots a);
   v <- vec_index_mut_back hm.hash_map_slots a l0;
   Return
     (hm with <|hash_map_num_entries := i0; hash_map_slots := v|>)
   od)
Proof
  rw [bind_def] >>
  rpt (case_tac >> fs []) >>
  Cases_on ‘hm’ >> fs [] >>
  fs (TypeBase.updates_of “:'a hash_map_t”)
QED

(* TODO: this doesn't work very well *)
Theorem lookup_cond_decr_entries_eq:
  ∀ hm key i.
  hash_map_t_inv hm ⇒
  usize_to_int i < len (vec_to_list hm.hash_map_slots) ⇒
  ∃ j.
  (case lookup key (list_t_v (vec_index hm.hash_map_slots i)) of
    NONE => Return hm.hash_map_num_entries
  | SOME v => usize_sub hm.hash_map_num_entries (int_to_usize 1)) = Return j ∧
  (lookup key (list_t_v (vec_index hm.hash_map_slots i)) = NONE ⇒ j = hm.hash_map_num_entries) ∧
  (lookup key (list_t_v (vec_index hm.hash_map_slots i)) ≠ NONE ⇒
   usize_to_int j + 1 = usize_to_int hm.hash_map_num_entries)
Proof
  rw [] >>
  case_tac >>
  progress >>
  qspecl_assume [‘vec_to_list hm.hash_map_slots’, ‘usize_to_int i’, ‘key’] slot_t_lookup_SOME_not_empty >>
  gvs [vec_index_def] >>
  fs [hash_map_t_inv_def, hash_map_t_base_inv_def, hash_map_t_al_v_def, hash_map_t_v_def] >>
  int_tac
QED

(* TODO: when saving a spec theorem, check that all the variables which appear
   in the pre/postconditions also appear in the application *)
Theorem hash_map_remove_back_spec:
  ∀ hm key.
  hash_map_t_inv hm ⇒
  ∃ hm1. hash_map_remove_back hm key = Return hm1 ∧
  hash_map_t_inv hm1 ∧
  lookup_s hm1 key = NONE ∧
  (∀ k. k ≠ key ⇒ lookup_s hm1 k = lookup_s hm k) ∧
  (case lookup_s hm key of
   | NONE => len_s hm1 = len_s hm
   | SOME _ => len_s hm1 = len_s hm - 1)
Proof
  rw [hash_map_remove_back_def] >>
  (* TODO: automate *)
  qspec_assume ‘hm.hash_map_slots’ vec_len_spec >>
  fs [vec_len_def] >>
  sg ‘0 < usize_to_int (vec_len hm.hash_map_slots)’
  >-(fs [hash_map_t_inv_def, hash_map_t_base_inv_def, gt_eq_lt, vec_len_def] >> massage >> fs []) >>
  (* TODO: we have to prove this several times - it would be good to remember the preconditions
     we proved, sometimes *)
  sg ‘usize_to_int key % len (vec_to_list hm.hash_map_slots) < usize_to_int (vec_len hm.hash_map_slots)’
  >- (fs [vec_len_def] >> massage >> irule pos_mod_pos_lt >> int_tac) >>
  (* TODO: add a rewriting rule *)
  sg ‘usize_to_int (vec_len hm.hash_map_slots) = len (vec_to_list hm.hash_map_slots)’
  >- (fs [vec_len_def] >> massage >> fs []) >>
  fs [vec_len_def] >>
  massage >>
  progress >>
  progress >> fs [int_rem_def, vec_len_def] >>
  progress >>
  gvs [] >>
  fs [hash_map_remove_back_branch_eq] >>
  qspecl_assume [‘hm’, ‘key’, ‘a’] lookup_cond_decr_entries_eq >>
  gvs [] >>
  progress >>
  progress >> fs [vec_len_def] >>
  (* Prove the post-condition *)
  sg ‘let i = usize_to_int key % len (vec_to_list hm.hash_map_slots) in
      slot_t_inv (len (vec_to_list hm.hash_map_slots)) i (index i (vec_to_list hm.hash_map_slots))’
  >- (fs [hash_map_t_inv_def, hash_map_t_base_inv_def, slots_t_inv_def]) >> fs [] >>
  gvs [vec_index_def] >>
  qpat_assum ‘∀l. _’ imp_res_tac >>
  rw []
  >- (
    fs [hash_map_t_inv_def, hash_map_t_base_inv_def, hash_map_t_al_v_def, hash_map_t_v_def] >>
    rw []
    >- (
      (* The num_entries has been correctly updated *)
      sg_dep_rewrite_goal_tac len_FLAT_MAP_update >- int_tac >> fs [] >> pop_assum ignore_tac >> gvs [] >>
      (* Case analysis on: ‘lookup key (index (key % len slots) slots)’ *)
      pop_assum mp_tac >> case_tac >> fs [] >>
      int_tac
    )
    >- (
      fs [slots_t_inv_def] >> rw [] >>
      (* TODO: this is annoying: we proved this many times *)
      last_x_assum (qspec_assume ‘i’) >>
      gvs [vec_index_def] >>
      qpat_x_assum ‘∀l. _’ imp_res_tac >>
      Cases_on ‘i = usize_to_int key % len (vec_to_list hm.hash_map_slots)’ >> fs []
      >- (
        sg_dep_rewrite_goal_tac index_update_diff
        >- (fs [] >> int_tac) >> fs []
      ) >>
      sg_dep_rewrite_goal_tac index_update_same
      >- (fs [] >> int_tac) >> fs []
    ) >>
    (* num_entries ≤ max_load *)
    Cases_on ‘lookup key (list_t_v (index
                (usize_to_int key % len (vec_to_list hm.hash_map_slots))
                (vec_to_list hm.hash_map_slots)))’ >> gvs [] >>
    (* Remains the case where we decrment num_entries - TODO: this is too much work, should be easier *)
    gvs [usize_sub_def, mk_usize_def] >>
    massage >>
    sg ‘0 ≤ len_s hm - 1 ∧ len_s hm - 1 ≤ usize_max’
    >- (fs [len_s_def, hash_map_t_al_v_def, hash_map_t_v_def] >> int_tac) >>
    fs [len_s_def, hash_map_t_al_v_def, hash_map_t_v_def] >>
    gvs [] >>
    massage >>
    Cases_on ‘hm.hash_map_max_load_factor’ >> gvs [] >>
    disj1_tac >> int_tac)
  >- (
    fs [lookup_s_def, slots_t_lookup_def] >>
    (* TODO: we did this too many times *)
    sg_dep_rewrite_goal_tac index_update_diff
    >- (fs [] >> int_tac) >> fs [] >>
    metis_tac []
  )
  >- (
    (* Lookup of k ≠ key *)
    fs [lookup_s_def, slots_t_lookup_def] >>
    Cases_on ‘usize_to_int k % len (vec_to_list hm.hash_map_slots) = usize_to_int key % len (vec_to_list hm.hash_map_slots)’ >> fs []
    >- (
      sg_dep_rewrite_goal_tac index_update_diff
      >- (fs [] >> int_tac) >> fs [] >>
      metis_tac []) >>
    sg_dep_rewrite_goal_tac index_update_same
    >- (rw [] >> try_tac int_tac >> irule pos_mod_pos_lt >> fs [] >> massage >> fs []) >> fs [] >>
    case_tac >> fs [] >>
    metis_tac []
  ) >>
  (* The length is correctly updated *)
  fs [lookup_s_def, len_s_def, slots_t_lookup_def, hash_map_t_al_v_def, hash_map_t_v_def] >>
  case_tac >> gvs [] >>  
  sg_dep_rewrite_goal_tac len_FLAT_MAP_update >> fs [] >> int_tac
QED
val _ = save_spec_thm "hash_map_remove_back_spec"

val _ = export_theory ()
