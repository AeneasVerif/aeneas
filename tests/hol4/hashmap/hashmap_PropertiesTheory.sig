signature hashmap_PropertiesTheory =
sig
  type thm = Thm.thm
  
  (*  Axioms  *)
    val usize_u32_bounds : thm
  
  (*  Definitions  *)
    val distinct_keys_def : thm
    val hash_map_just_before_resize_pred_def : thm
    val hash_map_same_params_def : thm
    val hash_map_t_al_v_def : thm
    val hash_map_t_base_inv_def : thm
    val hash_map_t_inv_def : thm
    val hash_map_t_v_def : thm
    val hash_mod_key_def : thm
    val insert_in_slot_t_rel_def : thm
    val len_s_def : thm
    val list_t_v_def : thm
    val lookup_s_def : thm
    val pairwise_rel_def : thm
    val slot_s_inv_def : thm
    val slot_s_inv_hash_def : thm
    val slot_t_inv_def : thm
    val slot_t_lookup_def : thm
    val slot_t_remove_def : thm
    val slots_s_inv_def : thm
    val slots_t_inv_def : thm
    val slots_t_lookup_def : thm
  
  (*  Theorems  *)
    val EVERY_quant_equiv : thm
    val FLAT_ListNil_is_nil : thm
    val MEM_EVERY_not : thm
    val MEM_distinct_keys_lookup : thm
    val distinct_keys_MEM_not_eq : thm
    val distinct_keys_lookup_NONE : thm
    val every_distinct_remove_every_distinct : thm
    val hash_map_allocate_slots_fwd_spec : thm
    val hash_map_allocate_slots_loop_fwd_spec : thm
    val hash_map_clear_fwd_back_spec : thm
    val hash_map_clear_loop_fwd_back_spec : thm
    val hash_map_clear_loop_fwd_back_spec_aux : thm
    val hash_map_cond_incr_thm : thm
    val hash_map_contains_key_fwd_spec : thm
    val hash_map_contains_key_in_list_fwd_spec : thm
    val hash_map_get_fwd_spec : thm
    val hash_map_get_in_list_fwd_spec : thm
    val hash_map_get_mut_back_spec : thm
    val hash_map_get_mut_fwd_spec : thm
    val hash_map_get_mut_in_list_back_spec : thm
    val hash_map_get_mut_in_list_fwd_spec : thm
    val hash_map_insert_fwd_back_spec : thm
    val hash_map_insert_in_list_fwd_spec : thm
    val hash_map_insert_in_list_loop_back_EVERY_distinct_keys : thm
    val hash_map_insert_in_list_loop_back_distinct_keys : thm
    val hash_map_insert_in_list_loop_back_spec : thm
    val hash_map_insert_in_list_loop_back_spec_aux : thm
    val hash_map_insert_in_list_loop_fwd_spec : thm
    val hash_map_insert_no_resize_fwd_back_branches_eq : thm
    val hash_map_insert_no_resize_fwd_back_spec : thm
    val hash_map_insert_no_resize_fwd_back_spec_aux : thm
    val hash_map_len_spec : thm
    val hash_map_move_elements_from_list_fwd_back_spec : thm
    val hash_map_move_elements_fwd_back_spec : thm
    val hash_map_move_elements_loop_fwd_back_spec_aux : thm
    val hash_map_new_fwd_spec : thm
    val hash_map_new_with_capacity_fwd_spec : thm
    val hash_map_remove_back_branch_eq : thm
    val hash_map_remove_back_spec : thm
    val hash_map_remove_from_list_back_spec : thm
    val hash_map_remove_from_list_fwd_spec : thm
    val hash_map_remove_fwd_spec : thm
    val hash_map_same_params_refl : thm
    val hash_map_t_base_inv_len_slots : thm
    val hash_map_try_resize_fwd_back_spec : thm
    val key_MEM_j_lookup_i_is_NONE : thm
    val len_FLAT_MAP_update : thm
    val len_index_FLAT_MAP_list_t_v : thm
    val len_vec_FLAT_drop_update : thm
    val lookup_SOME_not_empty : thm
    val lookup_cond_decr_entries_eq : thm
    val lookup_def : thm
    val lookup_distinct_keys_MEM : thm
    val lookup_ind : thm
    val lookup_s_SOME_not_empty : thm
    val pairwise_rel_quant_equiv : thm
    val remove_def : thm
    val remove_ind : thm
    val slot_t_lookup_SOME_not_empty : thm
  
  val hashmap_Properties_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [hashmap_Funs] Parent theory of "hashmap_Properties"
   
   [usize_u32_bounds]  Axiom
      
      [oracles: ] [axioms: usize_u32_bounds] [] ⊢ usize_max = u32_max
   
   [distinct_keys_def]  Definition
      
      ⊢ ∀ls. distinct_keys ls ⇔ pairwise_rel (λx y. FST x ≠ FST y) ls
   
   [hash_map_just_before_resize_pred_def]  Definition
      
      ⊢ ∀hm.
          hash_map_just_before_resize_pred hm ⇔
          (let
             (dividend,divisor) = hm.hash_map_max_load_factor
           in
             usize_to_int hm.hash_map_num_entries =
             usize_to_int hm.hash_map_max_load + 1 ∧
             len (vec_to_list hm.hash_map_slots) * 2 *
             usize_to_int dividend ≤ usize_max ∨
             len (vec_to_list hm.hash_map_slots) * 2 *
             usize_to_int dividend > usize_max)
   
   [hash_map_same_params_def]  Definition
      
      ⊢ ∀hm hm1.
          hash_map_same_params hm hm1 ⇔
          hm1.hash_map_max_load_factor = hm.hash_map_max_load_factor ∧
          hm1.hash_map_max_load = hm.hash_map_max_load ∧
          len (vec_to_list hm1.hash_map_slots) =
          len (vec_to_list hm.hash_map_slots)
   
   [hash_map_t_al_v_def]  Definition
      
      ⊢ ∀hm. hash_map_t_al_v hm = FLAT (hash_map_t_v hm)
   
   [hash_map_t_base_inv_def]  Definition
      
      ⊢ ∀hm.
          hash_map_t_base_inv hm ⇔
          (let
             al = hash_map_t_al_v hm
           in
             usize_to_int hm.hash_map_num_entries = len al ∧
             slots_t_inv hm.hash_map_slots ∧
             len (vec_to_list hm.hash_map_slots) > 0 ∧
             (let
                capacity = len (vec_to_list hm.hash_map_slots);
                (dividend,divisor) = hm.hash_map_max_load_factor;
                dividend = usize_to_int dividend;
                divisor = usize_to_int divisor
              in
                0 < dividend ∧ dividend < divisor ∧
                capacity * dividend ≥ divisor ∧
                usize_to_int hm.hash_map_max_load =
                capacity * dividend / divisor))
   
   [hash_map_t_inv_def]  Definition
      
      ⊢ ∀hm.
          hash_map_t_inv hm ⇔
          hash_map_t_base_inv hm ∧
          (let
             (dividend,divisor) = hm.hash_map_max_load_factor
           in
             usize_to_int hm.hash_map_num_entries ≤
             usize_to_int hm.hash_map_max_load ∨
             len (vec_to_list hm.hash_map_slots) * 2 *
             usize_to_int dividend > usize_max)
   
   [hash_map_t_v_def]  Definition
      
      ⊢ ∀hm. hash_map_t_v hm = MAP list_t_v (vec_to_list hm.hash_map_slots)
   
   [hash_mod_key_def]  Definition
      
      ⊢ ∀k l.
          hash_mod_key k l =
          case hash_key_fwd k of
            Return k => usize_to_int k % l
          | Fail v3 => ARB
          | Diverge => ARB
   
   [insert_in_slot_t_rel_def]  Definition
      
      ⊢ ∀l key value slot slot1.
          insert_in_slot_t_rel l key value slot slot1 ⇔
          slot_t_inv l (hash_mod_key key l) slot1 ∧
          slot_t_lookup key slot1 = SOME value ∧
          (∀k. k ≠ key ⇒ slot_t_lookup k slot = slot_t_lookup k slot1) ∧
          case slot_t_lookup key slot of
            NONE => len (list_t_v slot1) = len (list_t_v slot) + 1
          | SOME v => len (list_t_v slot1) = len (list_t_v slot)
   
   [len_s_def]  Definition
      
      ⊢ ∀hm. len_s hm = len (hash_map_t_al_v hm)
   
   [list_t_v_def]  Definition
      
      ⊢ list_t_v ListNil = [] ∧
        ∀k v tl. list_t_v (ListCons k v tl) = (k,v)::list_t_v tl
   
   [lookup_s_def]  Definition
      
      ⊢ ∀hm k.
          lookup_s hm k = slots_t_lookup (vec_to_list hm.hash_map_slots) k
   
   [pairwise_rel_def]  Definition
      
      ⊢ (∀p. pairwise_rel p [] ⇔ T) ∧
        ∀p x ls.
          pairwise_rel p (x::ls) ⇔ EVERY (p x) ls ∧ pairwise_rel p ls
   
   [slot_s_inv_def]  Definition
      
      ⊢ ∀l i ls.
          slot_s_inv l i ls ⇔ distinct_keys ls ∧ slot_s_inv_hash l i ls
   
   [slot_s_inv_hash_def]  Definition
      
      ⊢ ∀l i ls.
          slot_s_inv_hash l i ls ⇔
          ∀k v. MEM (k,v) ls ⇒ hash_mod_key k l = i
   
   [slot_t_inv_def]  Definition
      
      ⊢ ∀l i s. slot_t_inv l i s ⇔ slot_s_inv l i (list_t_v s)
   
   [slot_t_lookup_def]  Definition
      
      ⊢ ∀key ls. slot_t_lookup key ls = lookup key (list_t_v ls)
   
   [slot_t_remove_def]  Definition
      
      ⊢ ∀key ls. slot_t_remove key ls = remove key (list_t_v ls)
   
   [slots_s_inv_def]  Definition
      
      ⊢ ∀s. slots_s_inv s ⇔
            ∀i. 0 ≤ i ⇒ i < len s ⇒ slot_t_inv (len s) i (index i s)
   
   [slots_t_inv_def]  Definition
      
      ⊢ ∀s. slots_t_inv s ⇔ slots_s_inv (vec_to_list s)
   
   [slots_t_lookup_def]  Definition
      
      ⊢ ∀s k.
          slots_t_lookup s k =
          (let
             i = hash_mod_key k (len s);
             slot = index i s
           in
             slot_t_lookup k slot)
   
   [EVERY_quant_equiv]  Theorem
      
      ⊢ ∀p ls. EVERY p ls ⇔ ∀i. 0 ≤ i ⇒ i < len ls ⇒ p (index i ls)
   
   [FLAT_ListNil_is_nil]  Theorem
      
      ⊢ EVERY (λx. x = ListNil) ls ⇒ FLAT (MAP list_t_v ls) = []
   
   [MEM_EVERY_not]  Theorem
      
      ⊢ ∀k v ls. MEM (k,v) ls ⇒ EVERY (λx. k ≠ FST x) ls ⇒ F
   
   [MEM_distinct_keys_lookup]  Theorem
      
      ⊢ ∀k v ls. MEM (k,v) ls ⇒ distinct_keys ls ⇒ lookup k ls = SOME v
   
   [distinct_keys_MEM_not_eq]  Theorem
      
      ⊢ ∀ls k1 x1 k2 x2.
          distinct_keys ((k1,x1)::ls) ⇒ MEM (k2,x2) ls ⇒ k2 ≠ k1
   
   [distinct_keys_lookup_NONE]  Theorem
      
      ⊢ ∀ls k x. distinct_keys ((k,x)::ls) ⇒ lookup k ls = NONE
   
   [every_distinct_remove_every_distinct]  Theorem
      
      ⊢ ∀k0 k1 ls0.
          EVERY (λy. k1 ≠ FST y) ls0 ⇒
          EVERY (λy. k1 ≠ FST y) (remove k0 ls0)
   
   [hash_map_allocate_slots_fwd_spec]  Theorem
      
      ⊢ ∀n. usize_to_int n ≤ usize_max ⇒
            ∃slots.
              hash_map_allocate_slots_fwd vec_new n = Return slots ∧
              slots_t_inv slots ∧
              len (vec_to_list slots) = usize_to_int n ∧
              EVERY (λx. x = ListNil) (vec_to_list slots)
   
   [hash_map_allocate_slots_loop_fwd_spec]  Theorem
      
      ⊢ ∀slots n.
          EVERY (λx. x = ListNil) (vec_to_list slots) ⇒
          len (vec_to_list slots) + usize_to_int n ≤ usize_max ⇒
          ∃nslots.
            hash_map_allocate_slots_loop_fwd slots n = Return nslots ∧
            len (vec_to_list nslots) =
            len (vec_to_list slots) + usize_to_int n ∧
            EVERY (λx. x = ListNil) (vec_to_list nslots)
   
   [hash_map_clear_fwd_back_spec]  Theorem
      
      ⊢ ∀hm.
          hash_map_t_inv hm ⇒
          ∃hm1.
            hash_map_clear_fwd_back hm = Return hm1 ∧ hash_map_t_inv hm1 ∧
            len_s hm1 = 0 ∧ ∀k. lookup_s hm1 k = NONE
   
   [hash_map_clear_loop_fwd_back_spec]  Theorem
      
      ⊢ ∀slots. ∃slots1.
          hash_map_clear_loop_fwd_back slots (int_to_usize 0) =
          Return slots1 ∧
          len (vec_to_list slots1) = len (vec_to_list slots) ∧
          (∀j. 0 ≤ j ⇒
               j < len (vec_to_list slots) ⇒
               index j (vec_to_list slots1) = ListNil) ∧
          FLAT (MAP list_t_v (vec_to_list slots1)) = []
   
   [hash_map_clear_loop_fwd_back_spec_aux]  Theorem
      
      ⊢ ∀n slots i.
          n = len (vec_to_list slots) − usize_to_int i ⇒
          ∃slots1.
            hash_map_clear_loop_fwd_back slots i = Return slots1 ∧
            len (vec_to_list slots1) = len (vec_to_list slots) ∧
            (∀j. 0 ≤ j ⇒
                 j < usize_to_int i ⇒
                 j < len (vec_to_list slots) ⇒
                 index j (vec_to_list slots1) = index j (vec_to_list slots)) ∧
            ∀j. usize_to_int i ≤ j ⇒
                j < len (vec_to_list slots) ⇒
                index j (vec_to_list slots1) = ListNil
   
   [hash_map_cond_incr_thm]  Theorem
      
      ⊢ ∀hm key a.
          hash_map_t_base_inv hm ⇒
          (slot_t_lookup key (vec_index hm.hash_map_slots a) = NONE ⇒
           len_s hm < usize_max) ⇒
          ∃n. (if
                 slot_t_lookup key (vec_index hm.hash_map_slots a) = NONE
               then
                 usize_add hm.hash_map_num_entries (int_to_usize 1)
               else Return hm.hash_map_num_entries) =
              Return n ∧
              if
                slot_t_lookup key (vec_index hm.hash_map_slots a) = NONE
              then
                usize_to_int n = usize_to_int hm.hash_map_num_entries + 1
              else n = hm.hash_map_num_entries
   
   [hash_map_contains_key_fwd_spec]  Theorem
      
      ⊢ ∀hm key.
          hash_map_t_inv hm ⇒
          hash_map_contains_key_fwd hm key =
          Return (lookup_s hm key ≠ NONE)
   
   [hash_map_contains_key_in_list_fwd_spec]  Theorem
      
      ⊢ ∀key ls.
          hash_map_contains_key_in_list_fwd key ls =
          Return (slot_t_lookup key ls ≠ NONE)
   
   [hash_map_get_fwd_spec]  Theorem
      
      ⊢ ∀hm key.
          hash_map_t_inv hm ⇒
          case hash_map_get_fwd hm key of
            Return x => lookup_s hm key = SOME x
          | Fail v1 => lookup_s hm key = NONE
          | Diverge => F
   
   [hash_map_get_in_list_fwd_spec]  Theorem
      
      ⊢ ∀ls key.
          case hash_map_get_in_list_fwd key ls of
            Return x => slot_t_lookup key ls = SOME x
          | Fail v1 => slot_t_lookup key ls = NONE
          | Diverge => F
   
   [hash_map_get_mut_back_spec]  Theorem
      
      ⊢ ∀hm key nx.
          lookup_s hm key ≠ NONE ⇒
          hash_map_t_inv hm ⇒
          ∃hm1.
            hash_map_get_mut_back hm key nx = Return hm1 ∧
            lookup_s hm1 key = SOME nx ∧
            ∀k. k ≠ key ⇒ lookup_s hm1 k = lookup_s hm k
   
   [hash_map_get_mut_fwd_spec]  Theorem
      
      ⊢ ∀hm key.
          hash_map_t_inv hm ⇒
          case hash_map_get_mut_fwd hm key of
            Return x => lookup_s hm key = SOME x
          | Fail v1 => lookup_s hm key = NONE
          | Diverge => F
   
   [hash_map_get_mut_in_list_back_spec]  Theorem
      
      ⊢ ∀ls key nx.
          slot_t_lookup key ls ≠ NONE ⇒
          ∃nls.
            hash_map_get_mut_in_list_back ls key nx = Return nls ∧
            slot_t_lookup key nls = SOME nx ∧
            ∀k. k ≠ key ⇒ slot_t_lookup k nls = slot_t_lookup k ls
   
   [hash_map_get_mut_in_list_fwd_spec]  Theorem
      
      ⊢ ∀ls key.
          case hash_map_get_mut_in_list_fwd ls key of
            Return x => slot_t_lookup key ls = SOME x
          | Fail v1 => slot_t_lookup key ls = NONE
          | Diverge => F
   
   [hash_map_insert_fwd_back_spec]  Theorem
      
      [oracles: DISK_THM] [axioms: usize_u32_bounds] []
      ⊢ ∀hm key value.
          hash_map_t_inv hm ⇒
          (lookup_s hm key = NONE ⇒ len_s hm < usize_max) ⇒
          ∃hm1.
            hash_map_insert_fwd_back hm key value = Return hm1 ∧
            hash_map_t_inv hm1 ∧ lookup_s hm1 key = SOME value ∧
            (∀k. k ≠ key ⇒ lookup_s hm k = lookup_s hm1 k) ∧
            case lookup_s hm key of
              NONE => len_s hm1 = len_s hm + 1
            | SOME v => len_s hm1 = len_s hm
   
   [hash_map_insert_in_list_fwd_spec]  Theorem
      
      ⊢ ∀ls key value. ∃b.
          hash_map_insert_in_list_fwd key value ls = Return b ∧
          (b ⇔ slot_t_lookup key ls = NONE)
   
   [hash_map_insert_in_list_loop_back_EVERY_distinct_keys]  Theorem
      
      ⊢ ∀k v k1 ls0 ls1.
          k1 ≠ k ⇒
          EVERY (λy. k1 ≠ FST y) (list_t_v ls0) ⇒
          pairwise_rel (λx y. FST x ≠ FST y) (list_t_v ls0) ⇒
          hash_map_insert_in_list_loop_back k v ls0 = Return ls1 ⇒
          EVERY (λy. k1 ≠ FST y) (list_t_v ls1)
   
   [hash_map_insert_in_list_loop_back_distinct_keys]  Theorem
      
      ⊢ ∀k v ls0 ls1.
          distinct_keys (list_t_v ls0) ⇒
          hash_map_insert_in_list_loop_back k v ls0 = Return ls1 ⇒
          distinct_keys (list_t_v ls1)
   
   [hash_map_insert_in_list_loop_back_spec]  Theorem
      
      ⊢ ∀i ls key value.
          distinct_keys (list_t_v ls) ⇒
          ∃ls1.
            hash_map_insert_in_list_loop_back key value ls = Return ls1 ∧
            ∀l. slot_s_inv_hash l (hash_mod_key key l) (list_t_v ls) ⇒
                insert_in_slot_t_rel l key value ls ls1
   
   [hash_map_insert_in_list_loop_back_spec_aux]  Theorem
      
      ⊢ ∀ls key value. ∃ls1.
          hash_map_insert_in_list_loop_back key value ls = Return ls1 ∧
          slot_t_lookup key ls1 = SOME value ∧
          (∀k. k ≠ key ⇒ slot_t_lookup k ls = slot_t_lookup k ls1) ∧
          (∀l. slot_s_inv_hash l (hash_mod_key key l) (list_t_v ls) ⇒
               slot_s_inv_hash l (hash_mod_key key l) (list_t_v ls1)) ∧
          case slot_t_lookup key ls of
            NONE => len (list_t_v ls1) = len (list_t_v ls) + 1
          | SOME v => len (list_t_v ls1) = len (list_t_v ls)
   
   [hash_map_insert_in_list_loop_fwd_spec]  Theorem
      
      ⊢ ∀ls key value. ∃b.
          hash_map_insert_in_list_loop_fwd key value ls = Return b ∧
          (b ⇔ slot_t_lookup key ls = NONE)
   
   [hash_map_insert_no_resize_fwd_back_branches_eq]  Theorem
      
      ⊢ (if slot_t_lookup key (vec_index hm.hash_map_slots a) = NONE then
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
        do
          i0 <-
            if
              slot_t_lookup key (vec_index hm.hash_map_slots a) = NONE
            then
              usize_add hm.hash_map_num_entries (int_to_usize 1)
            else Return hm.hash_map_num_entries;
          l0 <-
            hash_map_insert_in_list_back key value
              (vec_index hm.hash_map_slots a);
          v <- vec_index_mut_back hm.hash_map_slots a l0;
          Return
            (hm with <|hash_map_num_entries := i0; hash_map_slots := v|>)
        od
   
   [hash_map_insert_no_resize_fwd_back_spec]  Theorem
      
      ⊢ ∀hm key value.
          hash_map_t_base_inv hm ⇒
          (lookup_s hm key = NONE ⇒ len_s hm < usize_max) ⇒
          ∃hm1.
            hash_map_insert_no_resize_fwd_back hm key value = Return hm1 ∧
            hash_map_t_base_inv hm1 ∧ lookup_s hm1 key = SOME value ∧
            (∀k. k ≠ key ⇒ lookup_s hm k = lookup_s hm1 k) ∧
            (case lookup_s hm key of
               NONE => len_s hm1 = len_s hm + 1
             | SOME v => len_s hm1 = len_s hm) ∧
            hash_map_same_params hm hm1
   
   [hash_map_insert_no_resize_fwd_back_spec_aux]  Theorem
      
      ⊢ ∀hm key value.
          hash_map_t_base_inv hm ⇒
          (lookup_s hm key = NONE ⇒ len_s hm < usize_max) ⇒
          ∃hm1 slot1.
            hash_map_insert_no_resize_fwd_back hm key value = Return hm1 ∧
            len (vec_to_list hm1.hash_map_slots) =
            len (vec_to_list hm.hash_map_slots) ∧
            (let
               l = len (vec_to_list hm.hash_map_slots);
               i = hash_mod_key key (len (vec_to_list hm.hash_map_slots));
               slot = index i (vec_to_list hm.hash_map_slots)
             in
               insert_in_slot_t_rel l key value slot slot1 ∧
               vec_to_list hm1.hash_map_slots =
               update (vec_to_list hm.hash_map_slots) i slot1 ∧
               hm1.hash_map_max_load_factor = hm.hash_map_max_load_factor ∧
               hm1.hash_map_max_load = hm.hash_map_max_load ∧
               (case lookup_s hm key of
                  NONE =>
                    usize_to_int hm1.hash_map_num_entries =
                    usize_to_int hm.hash_map_num_entries + 1
                | SOME v =>
                  hm1.hash_map_num_entries = hm.hash_map_num_entries) ∧
               hash_map_same_params hm hm1)
   
   [hash_map_len_spec]  Theorem
      
      ⊢ ∀hm.
          hash_map_t_base_inv hm ⇒
          ∃x. hash_map_len_fwd hm = Return x ∧ usize_to_int x = len_s hm
   
   [hash_map_move_elements_from_list_fwd_back_spec]  Theorem
      
      ⊢ ∀hm ls.
          (let
             l = len (list_t_v ls)
           in
             hash_map_t_base_inv hm ⇒
             len_s hm + l ≤ usize_max ⇒
             ∃hm1.
               hash_map_move_elements_from_list_fwd_back hm ls = Return hm1 ∧
               hash_map_t_base_inv hm1 ∧
               ((∀k v. MEM (k,v) (list_t_v ls) ⇒ lookup_s hm k = NONE) ⇒
                distinct_keys (list_t_v ls) ⇒
                (∀k. slot_t_lookup k ls = NONE ⇒
                     lookup_s hm1 k = lookup_s hm k) ∧
                (∀k. slot_t_lookup k ls ≠ NONE ⇒
                     lookup_s hm1 k = slot_t_lookup k ls) ∧
                len_s hm1 = len_s hm + l) ∧ hash_map_same_params hm hm1)
   
   [hash_map_move_elements_fwd_back_spec]  Theorem
      
      ⊢ ∀hm slots i.
          (let
             slots_l =
               len
                 (FLAT
                    (MAP list_t_v
                       (drop (usize_to_int i) (vec_to_list slots))))
           in
             hash_map_t_base_inv hm ⇒
             len_s hm + slots_l ≤ usize_max ⇒
             (∀j. (let
                     l = len (vec_to_list slots)
                   in
                     usize_to_int i ≤ j ⇒
                     j < l ⇒
                     (let
                        slot = index j (vec_to_list slots)
                      in
                        slot_t_inv l j slot ∧
                        ∀k v.
                          MEM (k,v) (list_t_v slot) ⇒ lookup_s hm k = NONE))) ⇒
             ∃hm1 slots1.
               hash_map_move_elements_fwd_back hm slots i =
               Return (hm1,slots1) ∧ hash_map_t_base_inv hm1 ∧
               len_s hm1 = len_s hm + slots_l ∧
               (∀k. lookup_s hm1 k =
                    case lookup_s hm k of
                      NONE =>
                        (let
                           j = hash_mod_key k (len (vec_to_list slots))
                         in
                           if
                             usize_to_int i ≤ j ∧
                             j < len (vec_to_list slots)
                           then
                             (let
                                slot = index j (vec_to_list slots)
                              in
                                lookup k (list_t_v slot))
                           else NONE)
                    | SOME v => SOME v) ∧ hash_map_same_params hm hm1)
   
   [hash_map_move_elements_loop_fwd_back_spec_aux]  Theorem
      
      ⊢ ∀hm slots i n.
          (let
             slots_l =
               len
                 (FLAT
                    (MAP list_t_v
                       (drop (usize_to_int i) (vec_to_list slots))))
           in
             n = len (vec_to_list slots) − usize_to_int i ⇒
             hash_map_t_base_inv hm ⇒
             len_s hm + slots_l ≤ usize_max ⇒
             (∀j. (let
                     l = len (vec_to_list slots)
                   in
                     usize_to_int i ≤ j ⇒
                     j < l ⇒
                     (let
                        slot = index j (vec_to_list slots)
                      in
                        slot_t_inv l j slot ∧
                        ∀k v.
                          MEM (k,v) (list_t_v slot) ⇒ lookup_s hm k = NONE))) ⇒
             ∃hm1 slots1.
               hash_map_move_elements_loop_fwd_back hm slots i =
               Return (hm1,slots1) ∧ hash_map_t_base_inv hm1 ∧
               len_s hm1 = len_s hm + slots_l ∧
               (∀k. lookup_s hm1 k =
                    case lookup_s hm k of
                      NONE =>
                        (let
                           j = hash_mod_key k (len (vec_to_list slots))
                         in
                           if
                             usize_to_int i ≤ j ∧
                             j < len (vec_to_list slots)
                           then
                             (let
                                slot = index j (vec_to_list slots)
                              in
                                lookup k (list_t_v slot))
                           else NONE)
                    | SOME v => SOME v) ∧ hash_map_same_params hm hm1)
   
   [hash_map_new_fwd_spec]  Theorem
      
      ⊢ ∃hm.
          hash_map_new_fwd = Return hm ∧ hash_map_t_inv hm ∧
          ∀k. lookup_s hm k = NONE ∧ len_s hm = 0
   
   [hash_map_new_with_capacity_fwd_spec]  Theorem
      
      ⊢ ∀capacity max_load_dividend max_load_divisor.
          0 < usize_to_int max_load_dividend ⇒
          usize_to_int max_load_dividend < usize_to_int max_load_divisor ⇒
          0 < usize_to_int capacity ⇒
          usize_to_int capacity * usize_to_int max_load_dividend ≥
          usize_to_int max_load_divisor ⇒
          usize_to_int capacity * usize_to_int max_load_dividend ≤
          usize_max ⇒
          ∃hm.
            hash_map_new_with_capacity_fwd capacity max_load_dividend
              max_load_divisor =
            Return hm ∧ hash_map_t_inv hm ∧ len_s hm = 0 ∧
            ∀k. lookup_s hm k = NONE ∧
                len (vec_to_list hm.hash_map_slots) = usize_to_int capacity ∧
                hm.hash_map_max_load_factor =
                (max_load_dividend,max_load_divisor)
   
   [hash_map_remove_back_branch_eq]  Theorem
      
      ⊢ ∀key hm a.
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
                 (hm with
                  <|hash_map_num_entries := i0; hash_map_slots := v|>)
             od) =
          do
            i0 <-
              case lookup key (list_t_v (vec_index hm.hash_map_slots a)) of
                NONE => Return hm.hash_map_num_entries
              | SOME v =>
                usize_sub hm.hash_map_num_entries (int_to_usize 1);
            l0 <-
              hash_map_remove_from_list_back key
                (vec_index hm.hash_map_slots a);
            v <- vec_index_mut_back hm.hash_map_slots a l0;
            Return
              (hm with <|hash_map_num_entries := i0; hash_map_slots := v|>)
          od
   
   [hash_map_remove_back_spec]  Theorem
      
      ⊢ ∀hm key.
          hash_map_t_inv hm ⇒
          ∃hm1.
            hash_map_remove_back hm key = Return hm1 ∧ hash_map_t_inv hm1 ∧
            lookup_s hm1 key = NONE ∧
            (∀k. k ≠ key ⇒ lookup_s hm1 k = lookup_s hm k) ∧
            case lookup_s hm key of
              NONE => len_s hm1 = len_s hm
            | SOME v => len_s hm1 = len_s hm − 1
   
   [hash_map_remove_from_list_back_spec]  Theorem
      
      ⊢ ∀key ls. ∃ls1.
          hash_map_remove_from_list_back key ls = Return ls1 ∧
          ∀l i.
            slot_t_inv l i ls ⇒
            slot_t_inv l i ls1 ∧ list_t_v ls1 = remove key (list_t_v ls) ∧
            slot_t_lookup key ls1 = NONE ∧
            (∀k. k ≠ key ⇒ slot_t_lookup k ls1 = slot_t_lookup k ls) ∧
            case slot_t_lookup key ls of
              NONE => len (list_t_v ls1) = len (list_t_v ls)
            | SOME v => len (list_t_v ls1) = len (list_t_v ls) − 1
   
   [hash_map_remove_from_list_fwd_spec]  Theorem
      
      ⊢ ∀key l i ls.
          hash_map_remove_from_list_fwd key ls =
          Return (slot_t_lookup key ls)
   
   [hash_map_remove_fwd_spec]  Theorem
      
      ⊢ ∀hm key.
          hash_map_t_inv hm ⇒
          hash_map_remove_fwd hm key = Return (lookup_s hm key)
   
   [hash_map_same_params_refl]  Theorem
      
      ⊢ ∀hm. hash_map_same_params hm hm
   
   [hash_map_t_base_inv_len_slots]  Theorem
      
      ⊢ ∀hm.
          hash_map_t_base_inv hm ⇒ 0 < len (vec_to_list hm.hash_map_slots)
   
   [hash_map_try_resize_fwd_back_spec]  Theorem
      
      [oracles: DISK_THM] [axioms: usize_u32_bounds] []
      ⊢ ∀hm.
          hash_map_t_base_inv hm ⇒
          hash_map_just_before_resize_pred hm ⇒
          ∃hm1.
            hash_map_try_resize_fwd_back hm = Return hm1 ∧
            hash_map_t_inv hm1 ∧ len_s hm1 = len_s hm ∧
            ∀k. lookup_s hm1 k = lookup_s hm k
   
   [key_MEM_j_lookup_i_is_NONE]  Theorem
      
      ⊢ ∀i j slots k v.
          usize_to_int i < j ⇒
          j < len (vec_to_list slots) ⇒
          (∀j. usize_to_int i ≤ j ⇒
               j < len (vec_to_list slots) ⇒
               slot_t_inv (len (vec_to_list slots)) j
                 (index j (vec_to_list slots))) ⇒
          MEM (k,v) (list_t_v (index j (vec_to_list slots))) ⇒
          slot_t_lookup k (index (usize_to_int i) (vec_to_list slots)) =
          NONE
   
   [len_FLAT_MAP_update]  Theorem
      
      ⊢ ∀x ls i.
          0 ≤ i ⇒
          i < len ls ⇒
          len (FLAT (MAP list_t_v (update ls i x))) =
          len (FLAT (MAP list_t_v ls)) + len (list_t_v x) −
          len (list_t_v (index i ls))
   
   [len_index_FLAT_MAP_list_t_v]  Theorem
      
      ⊢ ∀slots i.
          0 ≤ i ⇒
          i < len slots ⇒
          len (list_t_v (index i slots)) ≤
          len (FLAT (MAP list_t_v (drop i slots)))
   
   [len_vec_FLAT_drop_update]  Theorem
      
      ⊢ ∀slots i.
          0 ≤ i ⇒
          i < len slots ⇒
          len (FLAT (MAP list_t_v (drop i slots))) =
          len (list_t_v (index i slots)) +
          len (FLAT (MAP list_t_v (drop (i + 1) (update slots i ListNil))))
   
   [lookup_SOME_not_empty]  Theorem
      
      ⊢ ∀ls k. lookup k ls ≠ NONE ⇒ 0 < len ls
   
   [lookup_cond_decr_entries_eq]  Theorem
      
      ⊢ ∀hm key i.
          hash_map_t_inv hm ⇒
          usize_to_int i < len (vec_to_list hm.hash_map_slots) ⇒
          ∃j. (case
                 lookup key (list_t_v (vec_index hm.hash_map_slots i))
               of
                 NONE => Return hm.hash_map_num_entries
               | SOME v =>
                 usize_sub hm.hash_map_num_entries (int_to_usize 1)) =
              Return j ∧
              (lookup key (list_t_v (vec_index hm.hash_map_slots i)) = NONE ⇒
               j = hm.hash_map_num_entries) ∧
              (lookup key (list_t_v (vec_index hm.hash_map_slots i)) ≠ NONE ⇒
               usize_to_int j + 1 = usize_to_int hm.hash_map_num_entries)
   
   [lookup_def]  Theorem
      
      ⊢ (∀key. lookup key [] = NONE) ∧
        ∀v ls key k.
          lookup key ((k,v)::ls) =
          if k = key then SOME v else lookup key ls
   
   [lookup_distinct_keys_MEM]  Theorem
      
      ⊢ ∀k v ls. lookup k ls = SOME v ⇒ distinct_keys ls ⇒ MEM (k,v) ls
   
   [lookup_ind]  Theorem
      
      ⊢ ∀P. (∀key. P key []) ∧
            (∀key k v ls. (k ≠ key ⇒ P key ls) ⇒ P key ((k,v)::ls)) ⇒
            ∀v v1. P v v1
   
   [lookup_s_SOME_not_empty]  Theorem
      
      ⊢ ∀hm key. hash_map_t_inv hm ⇒ lookup_s hm key ≠ NONE ⇒ 0 < len_s hm
   
   [pairwise_rel_quant_equiv]  Theorem
      
      ⊢ ∀p ls.
          pairwise_rel p ls ⇔
          ∀i j. 0 ≤ i ⇒ i < j ⇒ j < len ls ⇒ p (index i ls) (index j ls)
   
   [remove_def]  Theorem
      
      ⊢ (∀key. remove key [] = []) ∧
        ∀v ls key k.
          remove key ((k,v)::ls) =
          if k = key then ls else (k,v)::remove key ls
   
   [remove_ind]  Theorem
      
      ⊢ ∀P. (∀key. P key []) ∧
            (∀key k v ls. (k ≠ key ⇒ P key ls) ⇒ P key ((k,v)::ls)) ⇒
            ∀v v1. P v v1
   
   [slot_t_lookup_SOME_not_empty]  Theorem
      
      ⊢ ∀ls i k.
          0 ≤ i ⇒
          i < len ls ⇒
          slot_t_lookup k (index i ls) ≠ NONE ⇒
          0 < len (FLAT (MAP list_t_v ls))
   
   
*)
end
