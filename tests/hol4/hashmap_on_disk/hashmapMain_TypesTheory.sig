signature hashmapMain_TypesTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val hashmap_hash_map_t_TY_DEF : thm
    val hashmap_hash_map_t_case_def : thm
    val hashmap_hash_map_t_hashmap_hash_map_max_load : thm
    val hashmap_hash_map_t_hashmap_hash_map_max_load_factor : thm
    val hashmap_hash_map_t_hashmap_hash_map_max_load_factor_fupd : thm
    val hashmap_hash_map_t_hashmap_hash_map_max_load_fupd : thm
    val hashmap_hash_map_t_hashmap_hash_map_num_entries : thm
    val hashmap_hash_map_t_hashmap_hash_map_num_entries_fupd : thm
    val hashmap_hash_map_t_hashmap_hash_map_slots : thm
    val hashmap_hash_map_t_hashmap_hash_map_slots_fupd : thm
    val hashmap_hash_map_t_size_def : thm
    val hashmap_list_t_TY_DEF : thm
    val hashmap_list_t_case_def : thm
    val hashmap_list_t_size_def : thm
  
  (*  Theorems  *)
    val EXISTS_hashmap_hash_map_t : thm
    val FORALL_hashmap_hash_map_t : thm
    val datatype_hashmap_hash_map_t : thm
    val datatype_hashmap_list_t : thm
    val hashmap_hash_map_t_11 : thm
    val hashmap_hash_map_t_Axiom : thm
    val hashmap_hash_map_t_accessors : thm
    val hashmap_hash_map_t_accfupds : thm
    val hashmap_hash_map_t_case_cong : thm
    val hashmap_hash_map_t_case_eq : thm
    val hashmap_hash_map_t_component_equality : thm
    val hashmap_hash_map_t_fn_updates : thm
    val hashmap_hash_map_t_fupdcanon : thm
    val hashmap_hash_map_t_fupdcanon_comp : thm
    val hashmap_hash_map_t_fupdfupds : thm
    val hashmap_hash_map_t_fupdfupds_comp : thm
    val hashmap_hash_map_t_induction : thm
    val hashmap_hash_map_t_literal_11 : thm
    val hashmap_hash_map_t_literal_nchotomy : thm
    val hashmap_hash_map_t_nchotomy : thm
    val hashmap_hash_map_t_updates_eq_literal : thm
    val hashmap_list_t_11 : thm
    val hashmap_list_t_Axiom : thm
    val hashmap_list_t_case_cong : thm
    val hashmap_list_t_case_eq : thm
    val hashmap_list_t_distinct : thm
    val hashmap_list_t_induction : thm
    val hashmap_list_t_nchotomy : thm
  
  val hashmapMain_Types_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [divDef] Parent theory of "hashmapMain_Types"
   
   [hashmap_hash_map_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('hashmap_hash_map_t').
                   (∀a0'.
                      (∃a0 a1 a2 a3.
                         a0' =
                         (λa0 a1 a2 a3.
                              ind_type$CONSTR 0 (a0,a1,a2,a3)
                                (λn. ind_type$BOTTOM)) a0 a1 a2 a3) ⇒
                      $var$('hashmap_hash_map_t') a0') ⇒
                   $var$('hashmap_hash_map_t') a0') rep
   
   [hashmap_hash_map_t_case_def]  Definition
      
      ⊢ ∀a0 a1 a2 a3 f.
          hashmap_hash_map_t_CASE (hashmap_hash_map_t a0 a1 a2 a3) f =
          f a0 a1 a2 a3
   
   [hashmap_hash_map_t_hashmap_hash_map_max_load]  Definition
      
      ⊢ ∀u p u0 v.
          (hashmap_hash_map_t u p u0 v).hashmap_hash_map_max_load = u0
   
   [hashmap_hash_map_t_hashmap_hash_map_max_load_factor]  Definition
      
      ⊢ ∀u p u0 v.
          (hashmap_hash_map_t u p u0 v).hashmap_hash_map_max_load_factor =
          p
   
   [hashmap_hash_map_t_hashmap_hash_map_max_load_factor_fupd]  Definition
      
      ⊢ ∀f u p u0 v.
          hashmap_hash_map_t u p u0 v with
          hashmap_hash_map_max_load_factor updated_by f =
          hashmap_hash_map_t u (f p) u0 v
   
   [hashmap_hash_map_t_hashmap_hash_map_max_load_fupd]  Definition
      
      ⊢ ∀f u p u0 v.
          hashmap_hash_map_t u p u0 v with
          hashmap_hash_map_max_load updated_by f =
          hashmap_hash_map_t u p (f u0) v
   
   [hashmap_hash_map_t_hashmap_hash_map_num_entries]  Definition
      
      ⊢ ∀u p u0 v.
          (hashmap_hash_map_t u p u0 v).hashmap_hash_map_num_entries = u
   
   [hashmap_hash_map_t_hashmap_hash_map_num_entries_fupd]  Definition
      
      ⊢ ∀f u p u0 v.
          hashmap_hash_map_t u p u0 v with
          hashmap_hash_map_num_entries updated_by f =
          hashmap_hash_map_t (f u) p u0 v
   
   [hashmap_hash_map_t_hashmap_hash_map_slots]  Definition
      
      ⊢ ∀u p u0 v. (hashmap_hash_map_t u p u0 v).hashmap_hash_map_slots = v
   
   [hashmap_hash_map_t_hashmap_hash_map_slots_fupd]  Definition
      
      ⊢ ∀f u p u0 v.
          hashmap_hash_map_t u p u0 v with
          hashmap_hash_map_slots updated_by f =
          hashmap_hash_map_t u p u0 (f v)
   
   [hashmap_hash_map_t_size_def]  Definition
      
      ⊢ ∀f a0 a1 a2 a3.
          hashmap_hash_map_t_size f (hashmap_hash_map_t a0 a1 a2 a3) =
          1 + pair_size (λv. 0) (λv. 0) a1
   
   [hashmap_list_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('hashmap_list_t').
                   (∀a0'.
                      (∃a0 a1 a2.
                         a0' =
                         (λa0 a1 a2.
                              ind_type$CONSTR 0 (a0,a1)
                                (ind_type$FCONS a2 (λn. ind_type$BOTTOM)))
                           a0 a1 a2 ∧ $var$('hashmap_list_t') a2) ∨
                      a0' =
                      ind_type$CONSTR (SUC 0) (ARB,ARB)
                        (λn. ind_type$BOTTOM) ⇒
                      $var$('hashmap_list_t') a0') ⇒
                   $var$('hashmap_list_t') a0') rep
   
   [hashmap_list_t_case_def]  Definition
      
      ⊢ (∀a0 a1 a2 f v.
           hashmap_list_t_CASE (HashmapListCons a0 a1 a2) f v = f a0 a1 a2) ∧
        ∀f v. hashmap_list_t_CASE HashmapListNil f v = v
   
   [hashmap_list_t_size_def]  Definition
      
      ⊢ (∀f a0 a1 a2.
           hashmap_list_t_size f (HashmapListCons a0 a1 a2) =
           1 + (f a1 + hashmap_list_t_size f a2)) ∧
        ∀f. hashmap_list_t_size f HashmapListNil = 0
   
   [EXISTS_hashmap_hash_map_t]  Theorem
      
      ⊢ ∀P. (∃h. P h) ⇔
            ∃u0 p u v.
              P
                <|hashmap_hash_map_num_entries := u0;
                  hashmap_hash_map_max_load_factor := p;
                  hashmap_hash_map_max_load := u;
                  hashmap_hash_map_slots := v|>
   
   [FORALL_hashmap_hash_map_t]  Theorem
      
      ⊢ ∀P. (∀h. P h) ⇔
            ∀u0 p u v.
              P
                <|hashmap_hash_map_num_entries := u0;
                  hashmap_hash_map_max_load_factor := p;
                  hashmap_hash_map_max_load := u;
                  hashmap_hash_map_slots := v|>
   
   [datatype_hashmap_hash_map_t]  Theorem
      
      ⊢ DATATYPE
          (record hashmap_hash_map_t hashmap_hash_map_num_entries
             hashmap_hash_map_max_load_factor hashmap_hash_map_max_load
             hashmap_hash_map_slots)
   
   [datatype_hashmap_list_t]  Theorem
      
      ⊢ DATATYPE (hashmap_list_t HashmapListCons HashmapListNil)
   
   [hashmap_hash_map_t_11]  Theorem
      
      ⊢ ∀a0 a1 a2 a3 a0' a1' a2' a3'.
          hashmap_hash_map_t a0 a1 a2 a3 =
          hashmap_hash_map_t a0' a1' a2' a3' ⇔
          a0 = a0' ∧ a1 = a1' ∧ a2 = a2' ∧ a3 = a3'
   
   [hashmap_hash_map_t_Axiom]  Theorem
      
      ⊢ ∀f. ∃fn. ∀a0 a1 a2 a3.
          fn (hashmap_hash_map_t a0 a1 a2 a3) = f a0 a1 a2 a3
   
   [hashmap_hash_map_t_accessors]  Theorem
      
      ⊢ (∀u p u0 v.
           (hashmap_hash_map_t u p u0 v).hashmap_hash_map_num_entries = u) ∧
        (∀u p u0 v.
           (hashmap_hash_map_t u p u0 v).hashmap_hash_map_max_load_factor =
           p) ∧
        (∀u p u0 v.
           (hashmap_hash_map_t u p u0 v).hashmap_hash_map_max_load = u0) ∧
        ∀u p u0 v. (hashmap_hash_map_t u p u0 v).hashmap_hash_map_slots = v
   
   [hashmap_hash_map_t_accfupds]  Theorem
      
      ⊢ (∀h f.
           (h with hashmap_hash_map_max_load_factor updated_by f).
           hashmap_hash_map_num_entries =
           h.hashmap_hash_map_num_entries) ∧
        (∀h f.
           (h with hashmap_hash_map_max_load updated_by f).
           hashmap_hash_map_num_entries =
           h.hashmap_hash_map_num_entries) ∧
        (∀h f.
           (h with hashmap_hash_map_slots updated_by f).
           hashmap_hash_map_num_entries =
           h.hashmap_hash_map_num_entries) ∧
        (∀h f.
           (h with hashmap_hash_map_num_entries updated_by f).
           hashmap_hash_map_max_load_factor =
           h.hashmap_hash_map_max_load_factor) ∧
        (∀h f.
           (h with hashmap_hash_map_max_load updated_by f).
           hashmap_hash_map_max_load_factor =
           h.hashmap_hash_map_max_load_factor) ∧
        (∀h f.
           (h with hashmap_hash_map_slots updated_by f).
           hashmap_hash_map_max_load_factor =
           h.hashmap_hash_map_max_load_factor) ∧
        (∀h f.
           (h with hashmap_hash_map_num_entries updated_by f).
           hashmap_hash_map_max_load =
           h.hashmap_hash_map_max_load) ∧
        (∀h f.
           (h with hashmap_hash_map_max_load_factor updated_by f).
           hashmap_hash_map_max_load =
           h.hashmap_hash_map_max_load) ∧
        (∀h f.
           (h with hashmap_hash_map_slots updated_by f).
           hashmap_hash_map_max_load =
           h.hashmap_hash_map_max_load) ∧
        (∀h f.
           (h with hashmap_hash_map_num_entries updated_by f).
           hashmap_hash_map_slots =
           h.hashmap_hash_map_slots) ∧
        (∀h f.
           (h with hashmap_hash_map_max_load_factor updated_by f).
           hashmap_hash_map_slots =
           h.hashmap_hash_map_slots) ∧
        (∀h f.
           (h with hashmap_hash_map_max_load updated_by f).
           hashmap_hash_map_slots =
           h.hashmap_hash_map_slots) ∧
        (∀h f.
           (h with hashmap_hash_map_num_entries updated_by f).
           hashmap_hash_map_num_entries =
           f h.hashmap_hash_map_num_entries) ∧
        (∀h f.
           (h with hashmap_hash_map_max_load_factor updated_by f).
           hashmap_hash_map_max_load_factor =
           f h.hashmap_hash_map_max_load_factor) ∧
        (∀h f.
           (h with hashmap_hash_map_max_load updated_by f).
           hashmap_hash_map_max_load =
           f h.hashmap_hash_map_max_load) ∧
        ∀h f.
          (h with hashmap_hash_map_slots updated_by f).
          hashmap_hash_map_slots =
          f h.hashmap_hash_map_slots
   
   [hashmap_hash_map_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧
          (∀a0 a1 a2 a3.
             M' = hashmap_hash_map_t a0 a1 a2 a3 ⇒
             f a0 a1 a2 a3 = f' a0 a1 a2 a3) ⇒
          hashmap_hash_map_t_CASE M f = hashmap_hash_map_t_CASE M' f'
   
   [hashmap_hash_map_t_case_eq]  Theorem
      
      ⊢ hashmap_hash_map_t_CASE x f = v ⇔
        ∃u p u0 v'. x = hashmap_hash_map_t u p u0 v' ∧ f u p u0 v' = v
   
   [hashmap_hash_map_t_component_equality]  Theorem
      
      ⊢ ∀h1 h2.
          h1 = h2 ⇔
          h1.hashmap_hash_map_num_entries = h2.hashmap_hash_map_num_entries ∧
          h1.hashmap_hash_map_max_load_factor =
          h2.hashmap_hash_map_max_load_factor ∧
          h1.hashmap_hash_map_max_load = h2.hashmap_hash_map_max_load ∧
          h1.hashmap_hash_map_slots = h2.hashmap_hash_map_slots
   
   [hashmap_hash_map_t_fn_updates]  Theorem
      
      ⊢ (∀f u p u0 v.
           hashmap_hash_map_t u p u0 v with
           hashmap_hash_map_num_entries updated_by f =
           hashmap_hash_map_t (f u) p u0 v) ∧
        (∀f u p u0 v.
           hashmap_hash_map_t u p u0 v with
           hashmap_hash_map_max_load_factor updated_by f =
           hashmap_hash_map_t u (f p) u0 v) ∧
        (∀f u p u0 v.
           hashmap_hash_map_t u p u0 v with
           hashmap_hash_map_max_load updated_by f =
           hashmap_hash_map_t u p (f u0) v) ∧
        ∀f u p u0 v.
          hashmap_hash_map_t u p u0 v with
          hashmap_hash_map_slots updated_by f =
          hashmap_hash_map_t u p u0 (f v)
   
   [hashmap_hash_map_t_fupdcanon]  Theorem
      
      ⊢ (∀h g f.
           h with
           <|hashmap_hash_map_max_load_factor updated_by f;
             hashmap_hash_map_num_entries updated_by g|> =
           h with
           <|hashmap_hash_map_num_entries updated_by g;
             hashmap_hash_map_max_load_factor updated_by f|>) ∧
        (∀h g f.
           h with
           <|hashmap_hash_map_max_load updated_by f;
             hashmap_hash_map_num_entries updated_by g|> =
           h with
           <|hashmap_hash_map_num_entries updated_by g;
             hashmap_hash_map_max_load updated_by f|>) ∧
        (∀h g f.
           h with
           <|hashmap_hash_map_max_load updated_by f;
             hashmap_hash_map_max_load_factor updated_by g|> =
           h with
           <|hashmap_hash_map_max_load_factor updated_by g;
             hashmap_hash_map_max_load updated_by f|>) ∧
        (∀h g f.
           h with
           <|hashmap_hash_map_slots updated_by f;
             hashmap_hash_map_num_entries updated_by g|> =
           h with
           <|hashmap_hash_map_num_entries updated_by g;
             hashmap_hash_map_slots updated_by f|>) ∧
        (∀h g f.
           h with
           <|hashmap_hash_map_slots updated_by f;
             hashmap_hash_map_max_load_factor updated_by g|> =
           h with
           <|hashmap_hash_map_max_load_factor updated_by g;
             hashmap_hash_map_slots updated_by f|>) ∧
        ∀h g f.
          h with
          <|hashmap_hash_map_slots updated_by f;
            hashmap_hash_map_max_load updated_by g|> =
          h with
          <|hashmap_hash_map_max_load updated_by g;
            hashmap_hash_map_slots updated_by f|>
   
   [hashmap_hash_map_t_fupdcanon_comp]  Theorem
      
      ⊢ ((∀g f.
            hashmap_hash_map_max_load_factor_fupd f ∘
            hashmap_hash_map_num_entries_fupd g =
            hashmap_hash_map_num_entries_fupd g ∘
            hashmap_hash_map_max_load_factor_fupd f) ∧
         ∀h g f.
           hashmap_hash_map_max_load_factor_fupd f ∘
           hashmap_hash_map_num_entries_fupd g ∘ h =
           hashmap_hash_map_num_entries_fupd g ∘
           hashmap_hash_map_max_load_factor_fupd f ∘ h) ∧
        ((∀g f.
            hashmap_hash_map_max_load_fupd f ∘
            hashmap_hash_map_num_entries_fupd g =
            hashmap_hash_map_num_entries_fupd g ∘
            hashmap_hash_map_max_load_fupd f) ∧
         ∀h g f.
           hashmap_hash_map_max_load_fupd f ∘
           hashmap_hash_map_num_entries_fupd g ∘ h =
           hashmap_hash_map_num_entries_fupd g ∘
           hashmap_hash_map_max_load_fupd f ∘ h) ∧
        ((∀g f.
            hashmap_hash_map_max_load_fupd f ∘
            hashmap_hash_map_max_load_factor_fupd g =
            hashmap_hash_map_max_load_factor_fupd g ∘
            hashmap_hash_map_max_load_fupd f) ∧
         ∀h g f.
           hashmap_hash_map_max_load_fupd f ∘
           hashmap_hash_map_max_load_factor_fupd g ∘ h =
           hashmap_hash_map_max_load_factor_fupd g ∘
           hashmap_hash_map_max_load_fupd f ∘ h) ∧
        ((∀g f.
            hashmap_hash_map_slots_fupd f ∘
            hashmap_hash_map_num_entries_fupd g =
            hashmap_hash_map_num_entries_fupd g ∘
            hashmap_hash_map_slots_fupd f) ∧
         ∀h g f.
           hashmap_hash_map_slots_fupd f ∘
           hashmap_hash_map_num_entries_fupd g ∘ h =
           hashmap_hash_map_num_entries_fupd g ∘
           hashmap_hash_map_slots_fupd f ∘ h) ∧
        ((∀g f.
            hashmap_hash_map_slots_fupd f ∘
            hashmap_hash_map_max_load_factor_fupd g =
            hashmap_hash_map_max_load_factor_fupd g ∘
            hashmap_hash_map_slots_fupd f) ∧
         ∀h g f.
           hashmap_hash_map_slots_fupd f ∘
           hashmap_hash_map_max_load_factor_fupd g ∘ h =
           hashmap_hash_map_max_load_factor_fupd g ∘
           hashmap_hash_map_slots_fupd f ∘ h) ∧
        (∀g f.
           hashmap_hash_map_slots_fupd f ∘ hashmap_hash_map_max_load_fupd g =
           hashmap_hash_map_max_load_fupd g ∘ hashmap_hash_map_slots_fupd f) ∧
        ∀h g f.
          hashmap_hash_map_slots_fupd f ∘
          hashmap_hash_map_max_load_fupd g ∘ h =
          hashmap_hash_map_max_load_fupd g ∘
          hashmap_hash_map_slots_fupd f ∘ h
   
   [hashmap_hash_map_t_fupdfupds]  Theorem
      
      ⊢ (∀h g f.
           h with
           <|hashmap_hash_map_num_entries updated_by f;
             hashmap_hash_map_num_entries updated_by g|> =
           h with hashmap_hash_map_num_entries updated_by f ∘ g) ∧
        (∀h g f.
           h with
           <|hashmap_hash_map_max_load_factor updated_by f;
             hashmap_hash_map_max_load_factor updated_by g|> =
           h with hashmap_hash_map_max_load_factor updated_by f ∘ g) ∧
        (∀h g f.
           h with
           <|hashmap_hash_map_max_load updated_by f;
             hashmap_hash_map_max_load updated_by g|> =
           h with hashmap_hash_map_max_load updated_by f ∘ g) ∧
        ∀h g f.
          h with
          <|hashmap_hash_map_slots updated_by f;
            hashmap_hash_map_slots updated_by g|> =
          h with hashmap_hash_map_slots updated_by f ∘ g
   
   [hashmap_hash_map_t_fupdfupds_comp]  Theorem
      
      ⊢ ((∀g f.
            hashmap_hash_map_num_entries_fupd f ∘
            hashmap_hash_map_num_entries_fupd g =
            hashmap_hash_map_num_entries_fupd (f ∘ g)) ∧
         ∀h g f.
           hashmap_hash_map_num_entries_fupd f ∘
           hashmap_hash_map_num_entries_fupd g ∘ h =
           hashmap_hash_map_num_entries_fupd (f ∘ g) ∘ h) ∧
        ((∀g f.
            hashmap_hash_map_max_load_factor_fupd f ∘
            hashmap_hash_map_max_load_factor_fupd g =
            hashmap_hash_map_max_load_factor_fupd (f ∘ g)) ∧
         ∀h g f.
           hashmap_hash_map_max_load_factor_fupd f ∘
           hashmap_hash_map_max_load_factor_fupd g ∘ h =
           hashmap_hash_map_max_load_factor_fupd (f ∘ g) ∘ h) ∧
        ((∀g f.
            hashmap_hash_map_max_load_fupd f ∘
            hashmap_hash_map_max_load_fupd g =
            hashmap_hash_map_max_load_fupd (f ∘ g)) ∧
         ∀h g f.
           hashmap_hash_map_max_load_fupd f ∘
           hashmap_hash_map_max_load_fupd g ∘ h =
           hashmap_hash_map_max_load_fupd (f ∘ g) ∘ h) ∧
        (∀g f.
           hashmap_hash_map_slots_fupd f ∘ hashmap_hash_map_slots_fupd g =
           hashmap_hash_map_slots_fupd (f ∘ g)) ∧
        ∀h g f.
          hashmap_hash_map_slots_fupd f ∘ hashmap_hash_map_slots_fupd g ∘ h =
          hashmap_hash_map_slots_fupd (f ∘ g) ∘ h
   
   [hashmap_hash_map_t_induction]  Theorem
      
      ⊢ ∀P. (∀u p u0 v. P (hashmap_hash_map_t u p u0 v)) ⇒ ∀h. P h
   
   [hashmap_hash_map_t_literal_11]  Theorem
      
      ⊢ ∀u01 p1 u1 v1 u02 p2 u2 v2.
          <|hashmap_hash_map_num_entries := u01;
            hashmap_hash_map_max_load_factor := p1;
            hashmap_hash_map_max_load := u1; hashmap_hash_map_slots := v1|> =
          <|hashmap_hash_map_num_entries := u02;
            hashmap_hash_map_max_load_factor := p2;
            hashmap_hash_map_max_load := u2; hashmap_hash_map_slots := v2|> ⇔
          u01 = u02 ∧ p1 = p2 ∧ u1 = u2 ∧ v1 = v2
   
   [hashmap_hash_map_t_literal_nchotomy]  Theorem
      
      ⊢ ∀h. ∃u0 p u v.
          h =
          <|hashmap_hash_map_num_entries := u0;
            hashmap_hash_map_max_load_factor := p;
            hashmap_hash_map_max_load := u; hashmap_hash_map_slots := v|>
   
   [hashmap_hash_map_t_nchotomy]  Theorem
      
      ⊢ ∀hh. ∃u p u0 v. hh = hashmap_hash_map_t u p u0 v
   
   [hashmap_hash_map_t_updates_eq_literal]  Theorem
      
      ⊢ ∀h u0 p u v.
          h with
          <|hashmap_hash_map_num_entries := u0;
            hashmap_hash_map_max_load_factor := p;
            hashmap_hash_map_max_load := u; hashmap_hash_map_slots := v|> =
          <|hashmap_hash_map_num_entries := u0;
            hashmap_hash_map_max_load_factor := p;
            hashmap_hash_map_max_load := u; hashmap_hash_map_slots := v|>
   
   [hashmap_list_t_11]  Theorem
      
      ⊢ ∀a0 a1 a2 a0' a1' a2'.
          HashmapListCons a0 a1 a2 = HashmapListCons a0' a1' a2' ⇔
          a0 = a0' ∧ a1 = a1' ∧ a2 = a2'
   
   [hashmap_list_t_Axiom]  Theorem
      
      ⊢ ∀f0 f1. ∃fn.
          (∀a0 a1 a2. fn (HashmapListCons a0 a1 a2) = f0 a0 a1 a2 (fn a2)) ∧
          fn HashmapListNil = f1
   
   [hashmap_list_t_case_cong]  Theorem
      
      ⊢ ∀M M' f v.
          M = M' ∧
          (∀a0 a1 a2.
             M' = HashmapListCons a0 a1 a2 ⇒ f a0 a1 a2 = f' a0 a1 a2) ∧
          (M' = HashmapListNil ⇒ v = v') ⇒
          hashmap_list_t_CASE M f v = hashmap_list_t_CASE M' f' v'
   
   [hashmap_list_t_case_eq]  Theorem
      
      ⊢ hashmap_list_t_CASE x f v = v' ⇔
        (∃u t h. x = HashmapListCons u t h ∧ f u t h = v') ∨
        x = HashmapListNil ∧ v = v'
   
   [hashmap_list_t_distinct]  Theorem
      
      ⊢ ∀a2 a1 a0. HashmapListCons a0 a1 a2 ≠ HashmapListNil
   
   [hashmap_list_t_induction]  Theorem
      
      ⊢ ∀P. (∀h. P h ⇒ ∀t u. P (HashmapListCons u t h)) ∧ P HashmapListNil ⇒
            ∀h. P h
   
   [hashmap_list_t_nchotomy]  Theorem
      
      ⊢ ∀hh. (∃u t h. hh = HashmapListCons u t h) ∨ hh = HashmapListNil
   
   
*)
end
