signature hashmap_TypesTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val hash_map_t_TY_DEF : thm
    val hash_map_t_case_def : thm
    val hash_map_t_hash_map_max_load : thm
    val hash_map_t_hash_map_max_load_factor : thm
    val hash_map_t_hash_map_max_load_factor_fupd : thm
    val hash_map_t_hash_map_max_load_fupd : thm
    val hash_map_t_hash_map_num_entries : thm
    val hash_map_t_hash_map_num_entries_fupd : thm
    val hash_map_t_hash_map_slots : thm
    val hash_map_t_hash_map_slots_fupd : thm
    val hash_map_t_size_def : thm
    val list_t_TY_DEF : thm
    val list_t_case_def : thm
    val list_t_size_def : thm
  
  (*  Theorems  *)
    val EXISTS_hash_map_t : thm
    val FORALL_hash_map_t : thm
    val datatype_hash_map_t : thm
    val datatype_list_t : thm
    val hash_map_t_11 : thm
    val hash_map_t_Axiom : thm
    val hash_map_t_accessors : thm
    val hash_map_t_accfupds : thm
    val hash_map_t_case_cong : thm
    val hash_map_t_case_eq : thm
    val hash_map_t_component_equality : thm
    val hash_map_t_fn_updates : thm
    val hash_map_t_fupdcanon : thm
    val hash_map_t_fupdcanon_comp : thm
    val hash_map_t_fupdfupds : thm
    val hash_map_t_fupdfupds_comp : thm
    val hash_map_t_induction : thm
    val hash_map_t_literal_11 : thm
    val hash_map_t_literal_nchotomy : thm
    val hash_map_t_nchotomy : thm
    val hash_map_t_updates_eq_literal : thm
    val list_t_11 : thm
    val list_t_Axiom : thm
    val list_t_case_cong : thm
    val list_t_case_eq : thm
    val list_t_distinct : thm
    val list_t_induction : thm
    val list_t_nchotomy : thm
  
  val hashmap_Types_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [divDef] Parent theory of "hashmap_Types"
   
   [hash_map_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('hash_map_t').
                   (∀a0'.
                      (∃a0 a1 a2 a3.
                         a0' =
                         (λa0 a1 a2 a3.
                              ind_type$CONSTR 0 (a0,a1,a2,a3)
                                (λn. ind_type$BOTTOM)) a0 a1 a2 a3) ⇒
                      $var$('hash_map_t') a0') ⇒
                   $var$('hash_map_t') a0') rep
   
   [hash_map_t_case_def]  Definition
      
      ⊢ ∀a0 a1 a2 a3 f.
          hash_map_t_CASE (hash_map_t a0 a1 a2 a3) f = f a0 a1 a2 a3
   
   [hash_map_t_hash_map_max_load]  Definition
      
      ⊢ ∀u p u0 v. (hash_map_t u p u0 v).hash_map_max_load = u0
   
   [hash_map_t_hash_map_max_load_factor]  Definition
      
      ⊢ ∀u p u0 v. (hash_map_t u p u0 v).hash_map_max_load_factor = p
   
   [hash_map_t_hash_map_max_load_factor_fupd]  Definition
      
      ⊢ ∀f u p u0 v.
          hash_map_t u p u0 v with hash_map_max_load_factor updated_by f =
          hash_map_t u (f p) u0 v
   
   [hash_map_t_hash_map_max_load_fupd]  Definition
      
      ⊢ ∀f u p u0 v.
          hash_map_t u p u0 v with hash_map_max_load updated_by f =
          hash_map_t u p (f u0) v
   
   [hash_map_t_hash_map_num_entries]  Definition
      
      ⊢ ∀u p u0 v. (hash_map_t u p u0 v).hash_map_num_entries = u
   
   [hash_map_t_hash_map_num_entries_fupd]  Definition
      
      ⊢ ∀f u p u0 v.
          hash_map_t u p u0 v with hash_map_num_entries updated_by f =
          hash_map_t (f u) p u0 v
   
   [hash_map_t_hash_map_slots]  Definition
      
      ⊢ ∀u p u0 v. (hash_map_t u p u0 v).hash_map_slots = v
   
   [hash_map_t_hash_map_slots_fupd]  Definition
      
      ⊢ ∀f u p u0 v.
          hash_map_t u p u0 v with hash_map_slots updated_by f =
          hash_map_t u p u0 (f v)
   
   [hash_map_t_size_def]  Definition
      
      ⊢ ∀f a0 a1 a2 a3.
          hash_map_t_size f (hash_map_t a0 a1 a2 a3) =
          1 + pair_size (λv. 0) (λv. 0) a1
   
   [list_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('list_t').
                   (∀a0'.
                      (∃a0 a1 a2.
                         a0' =
                         (λa0 a1 a2.
                              ind_type$CONSTR 0 (a0,a1)
                                (ind_type$FCONS a2 (λn. ind_type$BOTTOM)))
                           a0 a1 a2 ∧ $var$('list_t') a2) ∨
                      a0' =
                      ind_type$CONSTR (SUC 0) (ARB,ARB)
                        (λn. ind_type$BOTTOM) ⇒
                      $var$('list_t') a0') ⇒
                   $var$('list_t') a0') rep
   
   [list_t_case_def]  Definition
      
      ⊢ (∀a0 a1 a2 f v. list_t_CASE (ListCons a0 a1 a2) f v = f a0 a1 a2) ∧
        ∀f v. list_t_CASE ListNil f v = v
   
   [list_t_size_def]  Definition
      
      ⊢ (∀f a0 a1 a2.
           list_t_size f (ListCons a0 a1 a2) =
           1 + (f a1 + list_t_size f a2)) ∧ ∀f. list_t_size f ListNil = 0
   
   [EXISTS_hash_map_t]  Theorem
      
      ⊢ ∀P. (∃h. P h) ⇔
            ∃u0 p u v.
              P
                <|hash_map_num_entries := u0;
                  hash_map_max_load_factor := p; hash_map_max_load := u;
                  hash_map_slots := v|>
   
   [FORALL_hash_map_t]  Theorem
      
      ⊢ ∀P. (∀h. P h) ⇔
            ∀u0 p u v.
              P
                <|hash_map_num_entries := u0;
                  hash_map_max_load_factor := p; hash_map_max_load := u;
                  hash_map_slots := v|>
   
   [datatype_hash_map_t]  Theorem
      
      ⊢ DATATYPE
          (record hash_map_t hash_map_num_entries hash_map_max_load_factor
             hash_map_max_load hash_map_slots)
   
   [datatype_list_t]  Theorem
      
      ⊢ DATATYPE (list_t ListCons ListNil)
   
   [hash_map_t_11]  Theorem
      
      ⊢ ∀a0 a1 a2 a3 a0' a1' a2' a3'.
          hash_map_t a0 a1 a2 a3 = hash_map_t a0' a1' a2' a3' ⇔
          a0 = a0' ∧ a1 = a1' ∧ a2 = a2' ∧ a3 = a3'
   
   [hash_map_t_Axiom]  Theorem
      
      ⊢ ∀f. ∃fn. ∀a0 a1 a2 a3. fn (hash_map_t a0 a1 a2 a3) = f a0 a1 a2 a3
   
   [hash_map_t_accessors]  Theorem
      
      ⊢ (∀u p u0 v. (hash_map_t u p u0 v).hash_map_num_entries = u) ∧
        (∀u p u0 v. (hash_map_t u p u0 v).hash_map_max_load_factor = p) ∧
        (∀u p u0 v. (hash_map_t u p u0 v).hash_map_max_load = u0) ∧
        ∀u p u0 v. (hash_map_t u p u0 v).hash_map_slots = v
   
   [hash_map_t_accfupds]  Theorem
      
      ⊢ (∀h f.
           (h with hash_map_max_load_factor updated_by f).
           hash_map_num_entries =
           h.hash_map_num_entries) ∧
        (∀h f.
           (h with hash_map_max_load updated_by f).hash_map_num_entries =
           h.hash_map_num_entries) ∧
        (∀h f.
           (h with hash_map_slots updated_by f).hash_map_num_entries =
           h.hash_map_num_entries) ∧
        (∀h f.
           (h with hash_map_num_entries updated_by f).
           hash_map_max_load_factor =
           h.hash_map_max_load_factor) ∧
        (∀h f.
           (h with hash_map_max_load updated_by f).hash_map_max_load_factor =
           h.hash_map_max_load_factor) ∧
        (∀h f.
           (h with hash_map_slots updated_by f).hash_map_max_load_factor =
           h.hash_map_max_load_factor) ∧
        (∀h f.
           (h with hash_map_num_entries updated_by f).hash_map_max_load =
           h.hash_map_max_load) ∧
        (∀h f.
           (h with hash_map_max_load_factor updated_by f).hash_map_max_load =
           h.hash_map_max_load) ∧
        (∀h f.
           (h with hash_map_slots updated_by f).hash_map_max_load =
           h.hash_map_max_load) ∧
        (∀h f.
           (h with hash_map_num_entries updated_by f).hash_map_slots =
           h.hash_map_slots) ∧
        (∀h f.
           (h with hash_map_max_load_factor updated_by f).hash_map_slots =
           h.hash_map_slots) ∧
        (∀h f.
           (h with hash_map_max_load updated_by f).hash_map_slots =
           h.hash_map_slots) ∧
        (∀h f.
           (h with hash_map_num_entries updated_by f).hash_map_num_entries =
           f h.hash_map_num_entries) ∧
        (∀h f.
           (h with hash_map_max_load_factor updated_by f).
           hash_map_max_load_factor =
           f h.hash_map_max_load_factor) ∧
        (∀h f.
           (h with hash_map_max_load updated_by f).hash_map_max_load =
           f h.hash_map_max_load) ∧
        ∀h f.
          (h with hash_map_slots updated_by f).hash_map_slots =
          f h.hash_map_slots
   
   [hash_map_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧
          (∀a0 a1 a2 a3.
             M' = hash_map_t a0 a1 a2 a3 ⇒ f a0 a1 a2 a3 = f' a0 a1 a2 a3) ⇒
          hash_map_t_CASE M f = hash_map_t_CASE M' f'
   
   [hash_map_t_case_eq]  Theorem
      
      ⊢ hash_map_t_CASE x f = v ⇔
        ∃u p u0 v'. x = hash_map_t u p u0 v' ∧ f u p u0 v' = v
   
   [hash_map_t_component_equality]  Theorem
      
      ⊢ ∀h1 h2.
          h1 = h2 ⇔
          h1.hash_map_num_entries = h2.hash_map_num_entries ∧
          h1.hash_map_max_load_factor = h2.hash_map_max_load_factor ∧
          h1.hash_map_max_load = h2.hash_map_max_load ∧
          h1.hash_map_slots = h2.hash_map_slots
   
   [hash_map_t_fn_updates]  Theorem
      
      ⊢ (∀f u p u0 v.
           hash_map_t u p u0 v with hash_map_num_entries updated_by f =
           hash_map_t (f u) p u0 v) ∧
        (∀f u p u0 v.
           hash_map_t u p u0 v with hash_map_max_load_factor updated_by f =
           hash_map_t u (f p) u0 v) ∧
        (∀f u p u0 v.
           hash_map_t u p u0 v with hash_map_max_load updated_by f =
           hash_map_t u p (f u0) v) ∧
        ∀f u p u0 v.
          hash_map_t u p u0 v with hash_map_slots updated_by f =
          hash_map_t u p u0 (f v)
   
   [hash_map_t_fupdcanon]  Theorem
      
      ⊢ (∀h g f.
           h with
           <|hash_map_max_load_factor updated_by f;
             hash_map_num_entries updated_by g|> =
           h with
           <|hash_map_num_entries updated_by g;
             hash_map_max_load_factor updated_by f|>) ∧
        (∀h g f.
           h with
           <|hash_map_max_load updated_by f;
             hash_map_num_entries updated_by g|> =
           h with
           <|hash_map_num_entries updated_by g;
             hash_map_max_load updated_by f|>) ∧
        (∀h g f.
           h with
           <|hash_map_max_load updated_by f;
             hash_map_max_load_factor updated_by g|> =
           h with
           <|hash_map_max_load_factor updated_by g;
             hash_map_max_load updated_by f|>) ∧
        (∀h g f.
           h with
           <|hash_map_slots updated_by f;
             hash_map_num_entries updated_by g|> =
           h with
           <|hash_map_num_entries updated_by g;
             hash_map_slots updated_by f|>) ∧
        (∀h g f.
           h with
           <|hash_map_slots updated_by f;
             hash_map_max_load_factor updated_by g|> =
           h with
           <|hash_map_max_load_factor updated_by g;
             hash_map_slots updated_by f|>) ∧
        ∀h g f.
          h with
          <|hash_map_slots updated_by f; hash_map_max_load updated_by g|> =
          h with
          <|hash_map_max_load updated_by g; hash_map_slots updated_by f|>
   
   [hash_map_t_fupdcanon_comp]  Theorem
      
      ⊢ ((∀g f.
            hash_map_max_load_factor_fupd f ∘ hash_map_num_entries_fupd g =
            hash_map_num_entries_fupd g ∘ hash_map_max_load_factor_fupd f) ∧
         ∀h g f.
           hash_map_max_load_factor_fupd f ∘ hash_map_num_entries_fupd g ∘
           h =
           hash_map_num_entries_fupd g ∘ hash_map_max_load_factor_fupd f ∘
           h) ∧
        ((∀g f.
            hash_map_max_load_fupd f ∘ hash_map_num_entries_fupd g =
            hash_map_num_entries_fupd g ∘ hash_map_max_load_fupd f) ∧
         ∀h g f.
           hash_map_max_load_fupd f ∘ hash_map_num_entries_fupd g ∘ h =
           hash_map_num_entries_fupd g ∘ hash_map_max_load_fupd f ∘ h) ∧
        ((∀g f.
            hash_map_max_load_fupd f ∘ hash_map_max_load_factor_fupd g =
            hash_map_max_load_factor_fupd g ∘ hash_map_max_load_fupd f) ∧
         ∀h g f.
           hash_map_max_load_fupd f ∘ hash_map_max_load_factor_fupd g ∘ h =
           hash_map_max_load_factor_fupd g ∘ hash_map_max_load_fupd f ∘ h) ∧
        ((∀g f.
            hash_map_slots_fupd f ∘ hash_map_num_entries_fupd g =
            hash_map_num_entries_fupd g ∘ hash_map_slots_fupd f) ∧
         ∀h g f.
           hash_map_slots_fupd f ∘ hash_map_num_entries_fupd g ∘ h =
           hash_map_num_entries_fupd g ∘ hash_map_slots_fupd f ∘ h) ∧
        ((∀g f.
            hash_map_slots_fupd f ∘ hash_map_max_load_factor_fupd g =
            hash_map_max_load_factor_fupd g ∘ hash_map_slots_fupd f) ∧
         ∀h g f.
           hash_map_slots_fupd f ∘ hash_map_max_load_factor_fupd g ∘ h =
           hash_map_max_load_factor_fupd g ∘ hash_map_slots_fupd f ∘ h) ∧
        (∀g f.
           hash_map_slots_fupd f ∘ hash_map_max_load_fupd g =
           hash_map_max_load_fupd g ∘ hash_map_slots_fupd f) ∧
        ∀h g f.
          hash_map_slots_fupd f ∘ hash_map_max_load_fupd g ∘ h =
          hash_map_max_load_fupd g ∘ hash_map_slots_fupd f ∘ h
   
   [hash_map_t_fupdfupds]  Theorem
      
      ⊢ (∀h g f.
           h with
           <|hash_map_num_entries updated_by f;
             hash_map_num_entries updated_by g|> =
           h with hash_map_num_entries updated_by f ∘ g) ∧
        (∀h g f.
           h with
           <|hash_map_max_load_factor updated_by f;
             hash_map_max_load_factor updated_by g|> =
           h with hash_map_max_load_factor updated_by f ∘ g) ∧
        (∀h g f.
           h with
           <|hash_map_max_load updated_by f;
             hash_map_max_load updated_by g|> =
           h with hash_map_max_load updated_by f ∘ g) ∧
        ∀h g f.
          h with
          <|hash_map_slots updated_by f; hash_map_slots updated_by g|> =
          h with hash_map_slots updated_by f ∘ g
   
   [hash_map_t_fupdfupds_comp]  Theorem
      
      ⊢ ((∀g f.
            hash_map_num_entries_fupd f ∘ hash_map_num_entries_fupd g =
            hash_map_num_entries_fupd (f ∘ g)) ∧
         ∀h g f.
           hash_map_num_entries_fupd f ∘ hash_map_num_entries_fupd g ∘ h =
           hash_map_num_entries_fupd (f ∘ g) ∘ h) ∧
        ((∀g f.
            hash_map_max_load_factor_fupd f ∘
            hash_map_max_load_factor_fupd g =
            hash_map_max_load_factor_fupd (f ∘ g)) ∧
         ∀h g f.
           hash_map_max_load_factor_fupd f ∘
           hash_map_max_load_factor_fupd g ∘ h =
           hash_map_max_load_factor_fupd (f ∘ g) ∘ h) ∧
        ((∀g f.
            hash_map_max_load_fupd f ∘ hash_map_max_load_fupd g =
            hash_map_max_load_fupd (f ∘ g)) ∧
         ∀h g f.
           hash_map_max_load_fupd f ∘ hash_map_max_load_fupd g ∘ h =
           hash_map_max_load_fupd (f ∘ g) ∘ h) ∧
        (∀g f.
           hash_map_slots_fupd f ∘ hash_map_slots_fupd g =
           hash_map_slots_fupd (f ∘ g)) ∧
        ∀h g f.
          hash_map_slots_fupd f ∘ hash_map_slots_fupd g ∘ h =
          hash_map_slots_fupd (f ∘ g) ∘ h
   
   [hash_map_t_induction]  Theorem
      
      ⊢ ∀P. (∀u p u0 v. P (hash_map_t u p u0 v)) ⇒ ∀h. P h
   
   [hash_map_t_literal_11]  Theorem
      
      ⊢ ∀u01 p1 u1 v1 u02 p2 u2 v2.
          <|hash_map_num_entries := u01; hash_map_max_load_factor := p1;
            hash_map_max_load := u1; hash_map_slots := v1|> =
          <|hash_map_num_entries := u02; hash_map_max_load_factor := p2;
            hash_map_max_load := u2; hash_map_slots := v2|> ⇔
          u01 = u02 ∧ p1 = p2 ∧ u1 = u2 ∧ v1 = v2
   
   [hash_map_t_literal_nchotomy]  Theorem
      
      ⊢ ∀h. ∃u0 p u v.
          h =
          <|hash_map_num_entries := u0; hash_map_max_load_factor := p;
            hash_map_max_load := u; hash_map_slots := v|>
   
   [hash_map_t_nchotomy]  Theorem
      
      ⊢ ∀hh. ∃u p u0 v. hh = hash_map_t u p u0 v
   
   [hash_map_t_updates_eq_literal]  Theorem
      
      ⊢ ∀h u0 p u v.
          h with
          <|hash_map_num_entries := u0; hash_map_max_load_factor := p;
            hash_map_max_load := u; hash_map_slots := v|> =
          <|hash_map_num_entries := u0; hash_map_max_load_factor := p;
            hash_map_max_load := u; hash_map_slots := v|>
   
   [list_t_11]  Theorem
      
      ⊢ ∀a0 a1 a2 a0' a1' a2'.
          ListCons a0 a1 a2 = ListCons a0' a1' a2' ⇔
          a0 = a0' ∧ a1 = a1' ∧ a2 = a2'
   
   [list_t_Axiom]  Theorem
      
      ⊢ ∀f0 f1. ∃fn.
          (∀a0 a1 a2. fn (ListCons a0 a1 a2) = f0 a0 a1 a2 (fn a2)) ∧
          fn ListNil = f1
   
   [list_t_case_cong]  Theorem
      
      ⊢ ∀M M' f v.
          M = M' ∧
          (∀a0 a1 a2. M' = ListCons a0 a1 a2 ⇒ f a0 a1 a2 = f' a0 a1 a2) ∧
          (M' = ListNil ⇒ v = v') ⇒
          list_t_CASE M f v = list_t_CASE M' f' v'
   
   [list_t_case_eq]  Theorem
      
      ⊢ list_t_CASE x f v = v' ⇔
        (∃u t l. x = ListCons u t l ∧ f u t l = v') ∨ x = ListNil ∧ v = v'
   
   [list_t_distinct]  Theorem
      
      ⊢ ∀a2 a1 a0. ListCons a0 a1 a2 ≠ ListNil
   
   [list_t_induction]  Theorem
      
      ⊢ ∀P. (∀l. P l ⇒ ∀t u. P (ListCons u t l)) ∧ P ListNil ⇒ ∀l. P l
   
   [list_t_nchotomy]  Theorem
      
      ⊢ ∀ll. (∃u t l. ll = ListCons u t l) ∨ ll = ListNil
   
   
*)
end
