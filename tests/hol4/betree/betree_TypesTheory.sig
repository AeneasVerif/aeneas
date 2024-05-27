signature betree_TypesTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val betree_be_tree_t_TY_DEF : thm
    val betree_be_tree_t_betree_be_tree_node_id_cnt : thm
    val betree_be_tree_t_betree_be_tree_node_id_cnt_fupd : thm
    val betree_be_tree_t_betree_be_tree_params : thm
    val betree_be_tree_t_betree_be_tree_params_fupd : thm
    val betree_be_tree_t_betree_be_tree_root : thm
    val betree_be_tree_t_betree_be_tree_root_fupd : thm
    val betree_be_tree_t_case_def : thm
    val betree_be_tree_t_size_def : thm
    val betree_internal_t_TY_DEF : thm
    val betree_internal_t_betree_internal_id : thm
    val betree_internal_t_betree_internal_id_fupd : thm
    val betree_internal_t_betree_internal_left : thm
    val betree_internal_t_betree_internal_left_fupd : thm
    val betree_internal_t_betree_internal_pivot : thm
    val betree_internal_t_betree_internal_pivot_fupd : thm
    val betree_internal_t_betree_internal_right : thm
    val betree_internal_t_betree_internal_right_fupd : thm
    val betree_internal_t_case_def : thm
    val betree_internal_t_size_def : thm
    val betree_leaf_t_TY_DEF : thm
    val betree_leaf_t_betree_leaf_id : thm
    val betree_leaf_t_betree_leaf_id_fupd : thm
    val betree_leaf_t_betree_leaf_size : thm
    val betree_leaf_t_betree_leaf_size_fupd : thm
    val betree_leaf_t_case_def : thm
    val betree_leaf_t_size_def : thm
    val betree_list_t_TY_DEF : thm
    val betree_list_t_case_def : thm
    val betree_list_t_size_def : thm
    val betree_message_t_TY_DEF : thm
    val betree_message_t_case_def : thm
    val betree_message_t_size_def : thm
    val betree_node_id_counter_t_TY_DEF : thm
    val betree_node_id_counter_t_betree_node_id_counter_next_node_id : thm
    val betree_node_id_counter_t_betree_node_id_counter_next_node_id_fupd : thm
    val betree_node_id_counter_t_case_def : thm
    val betree_node_id_counter_t_size_def : thm
    val betree_node_t_TY_DEF : thm
    val betree_node_t_case_def : thm
    val betree_params_t_TY_DEF : thm
    val betree_params_t_betree_params_min_flush_size : thm
    val betree_params_t_betree_params_min_flush_size_fupd : thm
    val betree_params_t_betree_params_split_size : thm
    val betree_params_t_betree_params_split_size_fupd : thm
    val betree_params_t_case_def : thm
    val betree_params_t_size_def : thm
    val betree_upsert_fun_state_t_TY_DEF : thm
    val betree_upsert_fun_state_t_case_def : thm
    val betree_upsert_fun_state_t_size_def : thm
  
  (*  Theorems  *)
    val EXISTS_betree_be_tree_t : thm
    val EXISTS_betree_internal_t : thm
    val EXISTS_betree_leaf_t : thm
    val EXISTS_betree_node_id_counter_t : thm
    val EXISTS_betree_params_t : thm
    val FORALL_betree_be_tree_t : thm
    val FORALL_betree_internal_t : thm
    val FORALL_betree_leaf_t : thm
    val FORALL_betree_node_id_counter_t : thm
    val FORALL_betree_params_t : thm
    val betree_be_tree_t_11 : thm
    val betree_be_tree_t_Axiom : thm
    val betree_be_tree_t_accessors : thm
    val betree_be_tree_t_accfupds : thm
    val betree_be_tree_t_case_cong : thm
    val betree_be_tree_t_case_eq : thm
    val betree_be_tree_t_component_equality : thm
    val betree_be_tree_t_fn_updates : thm
    val betree_be_tree_t_fupdcanon : thm
    val betree_be_tree_t_fupdcanon_comp : thm
    val betree_be_tree_t_fupdfupds : thm
    val betree_be_tree_t_fupdfupds_comp : thm
    val betree_be_tree_t_induction : thm
    val betree_be_tree_t_literal_11 : thm
    val betree_be_tree_t_literal_nchotomy : thm
    val betree_be_tree_t_nchotomy : thm
    val betree_be_tree_t_updates_eq_literal : thm
    val betree_internal_t_11 : thm
    val betree_internal_t_Axiom : thm
    val betree_internal_t_accessors : thm
    val betree_internal_t_accfupds : thm
    val betree_internal_t_case_cong : thm
    val betree_internal_t_case_eq : thm
    val betree_internal_t_component_equality : thm
    val betree_internal_t_fn_updates : thm
    val betree_internal_t_fupdcanon : thm
    val betree_internal_t_fupdcanon_comp : thm
    val betree_internal_t_fupdfupds : thm
    val betree_internal_t_fupdfupds_comp : thm
    val betree_internal_t_induction : thm
    val betree_internal_t_literal_11 : thm
    val betree_internal_t_literal_nchotomy : thm
    val betree_internal_t_nchotomy : thm
    val betree_internal_t_updates_eq_literal : thm
    val betree_leaf_t_11 : thm
    val betree_leaf_t_Axiom : thm
    val betree_leaf_t_accessors : thm
    val betree_leaf_t_accfupds : thm
    val betree_leaf_t_case_cong : thm
    val betree_leaf_t_case_eq : thm
    val betree_leaf_t_component_equality : thm
    val betree_leaf_t_fn_updates : thm
    val betree_leaf_t_fupdcanon : thm
    val betree_leaf_t_fupdcanon_comp : thm
    val betree_leaf_t_fupdfupds : thm
    val betree_leaf_t_fupdfupds_comp : thm
    val betree_leaf_t_induction : thm
    val betree_leaf_t_literal_11 : thm
    val betree_leaf_t_literal_nchotomy : thm
    val betree_leaf_t_nchotomy : thm
    val betree_leaf_t_updates_eq_literal : thm
    val betree_list_t_11 : thm
    val betree_list_t_Axiom : thm
    val betree_list_t_case_cong : thm
    val betree_list_t_case_eq : thm
    val betree_list_t_distinct : thm
    val betree_list_t_induction : thm
    val betree_list_t_nchotomy : thm
    val betree_message_t_11 : thm
    val betree_message_t_Axiom : thm
    val betree_message_t_case_cong : thm
    val betree_message_t_case_eq : thm
    val betree_message_t_distinct : thm
    val betree_message_t_induction : thm
    val betree_message_t_nchotomy : thm
    val betree_node_id_counter_t_11 : thm
    val betree_node_id_counter_t_Axiom : thm
    val betree_node_id_counter_t_accessors : thm
    val betree_node_id_counter_t_accfupds : thm
    val betree_node_id_counter_t_case_cong : thm
    val betree_node_id_counter_t_case_eq : thm
    val betree_node_id_counter_t_component_equality : thm
    val betree_node_id_counter_t_fn_updates : thm
    val betree_node_id_counter_t_fupdfupds : thm
    val betree_node_id_counter_t_fupdfupds_comp : thm
    val betree_node_id_counter_t_induction : thm
    val betree_node_id_counter_t_literal_11 : thm
    val betree_node_id_counter_t_literal_nchotomy : thm
    val betree_node_id_counter_t_nchotomy : thm
    val betree_node_id_counter_t_updates_eq_literal : thm
    val betree_node_t_11 : thm
    val betree_node_t_Axiom : thm
    val betree_node_t_case_cong : thm
    val betree_node_t_case_eq : thm
    val betree_node_t_distinct : thm
    val betree_node_t_induction : thm
    val betree_node_t_nchotomy : thm
    val betree_params_t_11 : thm
    val betree_params_t_Axiom : thm
    val betree_params_t_accessors : thm
    val betree_params_t_accfupds : thm
    val betree_params_t_case_cong : thm
    val betree_params_t_case_eq : thm
    val betree_params_t_component_equality : thm
    val betree_params_t_fn_updates : thm
    val betree_params_t_fupdcanon : thm
    val betree_params_t_fupdcanon_comp : thm
    val betree_params_t_fupdfupds : thm
    val betree_params_t_fupdfupds_comp : thm
    val betree_params_t_induction : thm
    val betree_params_t_literal_11 : thm
    val betree_params_t_literal_nchotomy : thm
    val betree_params_t_nchotomy : thm
    val betree_params_t_updates_eq_literal : thm
    val betree_upsert_fun_state_t_11 : thm
    val betree_upsert_fun_state_t_Axiom : thm
    val betree_upsert_fun_state_t_case_cong : thm
    val betree_upsert_fun_state_t_case_eq : thm
    val betree_upsert_fun_state_t_distinct : thm
    val betree_upsert_fun_state_t_induction : thm
    val betree_upsert_fun_state_t_nchotomy : thm
    val datatype_betree_be_tree_t : thm
    val datatype_betree_internal_t : thm
    val datatype_betree_leaf_t : thm
    val datatype_betree_list_t : thm
    val datatype_betree_message_t : thm
    val datatype_betree_node_id_counter_t : thm
    val datatype_betree_params_t : thm
    val datatype_betree_upsert_fun_state_t : thm
  
  val betree_Types_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [divDef] Parent theory of "betree_Types"
   
   [betree_be_tree_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('betree_be_tree_t').
                   (∀a0'.
                      (∃a0 a1 a2.
                         a0' =
                         (λa0 a1 a2.
                              ind_type$CONSTR 0 (a0,a1,a2)
                                (λn. ind_type$BOTTOM)) a0 a1 a2) ⇒
                      $var$('betree_be_tree_t') a0') ⇒
                   $var$('betree_be_tree_t') a0') rep
   
   [betree_be_tree_t_betree_be_tree_node_id_cnt]  Definition
      
      ⊢ ∀b b0 b1.
          (betree_be_tree_t b b0 b1).betree_be_tree_node_id_cnt = b0
   
   [betree_be_tree_t_betree_be_tree_node_id_cnt_fupd]  Definition
      
      ⊢ ∀f b b0 b1.
          betree_be_tree_t b b0 b1 with
          betree_be_tree_node_id_cnt updated_by f =
          betree_be_tree_t b (f b0) b1
   
   [betree_be_tree_t_betree_be_tree_params]  Definition
      
      ⊢ ∀b b0 b1. (betree_be_tree_t b b0 b1).betree_be_tree_params = b
   
   [betree_be_tree_t_betree_be_tree_params_fupd]  Definition
      
      ⊢ ∀f b b0 b1.
          betree_be_tree_t b b0 b1 with betree_be_tree_params updated_by f =
          betree_be_tree_t (f b) b0 b1
   
   [betree_be_tree_t_betree_be_tree_root]  Definition
      
      ⊢ ∀b b0 b1. (betree_be_tree_t b b0 b1).betree_be_tree_root = b1
   
   [betree_be_tree_t_betree_be_tree_root_fupd]  Definition
      
      ⊢ ∀f b b0 b1.
          betree_be_tree_t b b0 b1 with betree_be_tree_root updated_by f =
          betree_be_tree_t b b0 (f b1)
   
   [betree_be_tree_t_case_def]  Definition
      
      ⊢ ∀a0 a1 a2 f.
          betree_be_tree_t_CASE (betree_be_tree_t a0 a1 a2) f = f a0 a1 a2
   
   [betree_be_tree_t_size_def]  Definition
      
      ⊢ ∀a0 a1 a2.
          betree_be_tree_t_size (betree_be_tree_t a0 a1 a2) =
          1 +
          (betree_params_t_size a0 +
           (betree_node_id_counter_t_size a1 + betree_node_t_size a2))
   
   [betree_internal_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('betree_internal_t') $var$('betree_node_t').
                   (∀a0'.
                      (∃a0 a1 a2 a3.
                         a0' =
                         (λa0 a1 a2 a3.
                              ind_type$CONSTR 0 (a0,a1,ARB)
                                (ind_type$FCONS a2
                                   (ind_type$FCONS a3 (λn. ind_type$BOTTOM))))
                           a0 a1 a2 a3 ∧ $var$('betree_node_t') a2 ∧
                         $var$('betree_node_t') a3) ⇒
                      $var$('betree_internal_t') a0') ∧
                   (∀a1'.
                      (∃a. a1' =
                           (λa.
                                ind_type$CONSTR (SUC 0) (ARB,ARB,ARB)
                                  (ind_type$FCONS a (λn. ind_type$BOTTOM)))
                             a ∧ $var$('betree_internal_t') a) ∨
                      (∃a. a1' =
                           (λa.
                                ind_type$CONSTR (SUC (SUC 0)) (ARB,ARB,a)
                                  (λn. ind_type$BOTTOM)) a) ⇒
                      $var$('betree_node_t') a1') ⇒
                   $var$('betree_internal_t') a0') rep
   
   [betree_internal_t_betree_internal_id]  Definition
      
      ⊢ ∀u u0 b b0. (betree_internal_t u u0 b b0).betree_internal_id = u
   
   [betree_internal_t_betree_internal_id_fupd]  Definition
      
      ⊢ ∀f u u0 b b0.
          betree_internal_t u u0 b b0 with betree_internal_id updated_by f =
          betree_internal_t (f u) u0 b b0
   
   [betree_internal_t_betree_internal_left]  Definition
      
      ⊢ ∀u u0 b b0. (betree_internal_t u u0 b b0).betree_internal_left = b
   
   [betree_internal_t_betree_internal_left_fupd]  Definition
      
      ⊢ ∀f u u0 b b0.
          betree_internal_t u u0 b b0 with
          betree_internal_left updated_by f =
          betree_internal_t u u0 (f b) b0
   
   [betree_internal_t_betree_internal_pivot]  Definition
      
      ⊢ ∀u u0 b b0.
          (betree_internal_t u u0 b b0).betree_internal_pivot = u0
   
   [betree_internal_t_betree_internal_pivot_fupd]  Definition
      
      ⊢ ∀f u u0 b b0.
          betree_internal_t u u0 b b0 with
          betree_internal_pivot updated_by f =
          betree_internal_t u (f u0) b b0
   
   [betree_internal_t_betree_internal_right]  Definition
      
      ⊢ ∀u u0 b b0.
          (betree_internal_t u u0 b b0).betree_internal_right = b0
   
   [betree_internal_t_betree_internal_right_fupd]  Definition
      
      ⊢ ∀f u u0 b b0.
          betree_internal_t u u0 b b0 with
          betree_internal_right updated_by f =
          betree_internal_t u u0 b (f b0)
   
   [betree_internal_t_case_def]  Definition
      
      ⊢ ∀a0 a1 a2 a3 f.
          betree_internal_t_CASE (betree_internal_t a0 a1 a2 a3) f =
          f a0 a1 a2 a3
   
   [betree_internal_t_size_def]  Definition
      
      ⊢ (∀a0 a1 a2 a3.
           betree_internal_t_size (betree_internal_t a0 a1 a2 a3) =
           1 + (betree_node_t_size a2 + betree_node_t_size a3)) ∧
        (∀a. betree_node_t_size (BetreeNodeInternal a) =
             1 + betree_internal_t_size a) ∧
        ∀a. betree_node_t_size (BetreeNodeLeaf a) =
            1 + betree_leaf_t_size a
   
   [betree_leaf_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('betree_leaf_t').
                   (∀a0'.
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR 0 (a0,a1)
                                (λn. ind_type$BOTTOM)) a0 a1) ⇒
                      $var$('betree_leaf_t') a0') ⇒
                   $var$('betree_leaf_t') a0') rep
   
   [betree_leaf_t_betree_leaf_id]  Definition
      
      ⊢ ∀u u0. (betree_leaf_t u u0).betree_leaf_id = u
   
   [betree_leaf_t_betree_leaf_id_fupd]  Definition
      
      ⊢ ∀f u u0.
          betree_leaf_t u u0 with betree_leaf_id updated_by f =
          betree_leaf_t (f u) u0
   
   [betree_leaf_t_betree_leaf_size]  Definition
      
      ⊢ ∀u u0. (betree_leaf_t u u0).betree_leaf_size = u0
   
   [betree_leaf_t_betree_leaf_size_fupd]  Definition
      
      ⊢ ∀f u u0.
          betree_leaf_t u u0 with betree_leaf_size updated_by f =
          betree_leaf_t u (f u0)
   
   [betree_leaf_t_case_def]  Definition
      
      ⊢ ∀a0 a1 f. betree_leaf_t_CASE (betree_leaf_t a0 a1) f = f a0 a1
   
   [betree_leaf_t_size_def]  Definition
      
      ⊢ ∀a0 a1. betree_leaf_t_size (betree_leaf_t a0 a1) = 1
   
   [betree_list_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('betree_list_t').
                   (∀a0'.
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR 0 a0
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))
                           a0 a1 ∧ $var$('betree_list_t') a1) ∨
                      a0' =
                      ind_type$CONSTR (SUC 0) ARB (λn. ind_type$BOTTOM) ⇒
                      $var$('betree_list_t') a0') ⇒
                   $var$('betree_list_t') a0') rep
   
   [betree_list_t_case_def]  Definition
      
      ⊢ (∀a0 a1 f v.
           betree_list_t_CASE (BetreeListCons a0 a1) f v = f a0 a1) ∧
        ∀f v. betree_list_t_CASE BetreeListNil f v = v
   
   [betree_list_t_size_def]  Definition
      
      ⊢ (∀f a0 a1.
           betree_list_t_size f (BetreeListCons a0 a1) =
           1 + (f a0 + betree_list_t_size f a1)) ∧
        ∀f. betree_list_t_size f BetreeListNil = 0
   
   [betree_message_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0.
                 ∀ $var$('betree_message_t').
                   (∀a0.
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR 0 (a,ARB)
                                  (λn. ind_type$BOTTOM)) a) ∨
                      a0 =
                      ind_type$CONSTR (SUC 0) (ARB,ARB)
                        (λn. ind_type$BOTTOM) ∨
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR (SUC (SUC 0)) (ARB,a)
                                  (λn. ind_type$BOTTOM)) a) ⇒
                      $var$('betree_message_t') a0) ⇒
                   $var$('betree_message_t') a0) rep
   
   [betree_message_t_case_def]  Definition
      
      ⊢ (∀a f v f1.
           betree_message_t_CASE (BetreeMessageInsert a) f v f1 = f a) ∧
        (∀f v f1. betree_message_t_CASE BetreeMessageDelete f v f1 = v) ∧
        ∀a f v f1.
          betree_message_t_CASE (BetreeMessageUpsert a) f v f1 = f1 a
   
   [betree_message_t_size_def]  Definition
      
      ⊢ (∀a. betree_message_t_size (BetreeMessageInsert a) = 1) ∧
        betree_message_t_size BetreeMessageDelete = 0 ∧
        ∀a. betree_message_t_size (BetreeMessageUpsert a) =
            1 + betree_upsert_fun_state_t_size a
   
   [betree_node_id_counter_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0.
                 ∀ $var$('betree_node_id_counter_t').
                   (∀a0.
                      (∃a. a0 =
                           (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                             a) ⇒
                      $var$('betree_node_id_counter_t') a0) ⇒
                   $var$('betree_node_id_counter_t') a0) rep
   
   [betree_node_id_counter_t_betree_node_id_counter_next_node_id]  Definition
      
      ⊢ ∀u. (betree_node_id_counter_t u).
            betree_node_id_counter_next_node_id =
            u
   
   [betree_node_id_counter_t_betree_node_id_counter_next_node_id_fupd]  Definition
      
      ⊢ ∀f u.
          betree_node_id_counter_t u with
          betree_node_id_counter_next_node_id updated_by f =
          betree_node_id_counter_t (f u)
   
   [betree_node_id_counter_t_case_def]  Definition
      
      ⊢ ∀a f.
          betree_node_id_counter_t_CASE (betree_node_id_counter_t a) f =
          f a
   
   [betree_node_id_counter_t_size_def]  Definition
      
      ⊢ ∀a. betree_node_id_counter_t_size (betree_node_id_counter_t a) = 1
   
   [betree_node_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa1'.
                 ∀ $var$('betree_internal_t') $var$('betree_node_t').
                   (∀a0'.
                      (∃a0 a1 a2 a3.
                         a0' =
                         (λa0 a1 a2 a3.
                              ind_type$CONSTR 0 (a0,a1,ARB)
                                (ind_type$FCONS a2
                                   (ind_type$FCONS a3 (λn. ind_type$BOTTOM))))
                           a0 a1 a2 a3 ∧ $var$('betree_node_t') a2 ∧
                         $var$('betree_node_t') a3) ⇒
                      $var$('betree_internal_t') a0') ∧
                   (∀a1'.
                      (∃a. a1' =
                           (λa.
                                ind_type$CONSTR (SUC 0) (ARB,ARB,ARB)
                                  (ind_type$FCONS a (λn. ind_type$BOTTOM)))
                             a ∧ $var$('betree_internal_t') a) ∨
                      (∃a. a1' =
                           (λa.
                                ind_type$CONSTR (SUC (SUC 0)) (ARB,ARB,a)
                                  (λn. ind_type$BOTTOM)) a) ⇒
                      $var$('betree_node_t') a1') ⇒
                   $var$('betree_node_t') a1') rep
   
   [betree_node_t_case_def]  Definition
      
      ⊢ (∀a f f1. betree_node_t_CASE (BetreeNodeInternal a) f f1 = f a) ∧
        ∀a f f1. betree_node_t_CASE (BetreeNodeLeaf a) f f1 = f1 a
   
   [betree_params_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('betree_params_t').
                   (∀a0'.
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR 0 (a0,a1)
                                (λn. ind_type$BOTTOM)) a0 a1) ⇒
                      $var$('betree_params_t') a0') ⇒
                   $var$('betree_params_t') a0') rep
   
   [betree_params_t_betree_params_min_flush_size]  Definition
      
      ⊢ ∀u u0. (betree_params_t u u0).betree_params_min_flush_size = u
   
   [betree_params_t_betree_params_min_flush_size_fupd]  Definition
      
      ⊢ ∀f u u0.
          betree_params_t u u0 with
          betree_params_min_flush_size updated_by f =
          betree_params_t (f u) u0
   
   [betree_params_t_betree_params_split_size]  Definition
      
      ⊢ ∀u u0. (betree_params_t u u0).betree_params_split_size = u0
   
   [betree_params_t_betree_params_split_size_fupd]  Definition
      
      ⊢ ∀f u u0.
          betree_params_t u u0 with betree_params_split_size updated_by f =
          betree_params_t u (f u0)
   
   [betree_params_t_case_def]  Definition
      
      ⊢ ∀a0 a1 f. betree_params_t_CASE (betree_params_t a0 a1) f = f a0 a1
   
   [betree_params_t_size_def]  Definition
      
      ⊢ ∀a0 a1. betree_params_t_size (betree_params_t a0 a1) = 1
   
   [betree_upsert_fun_state_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0.
                 ∀ $var$('betree_upsert_fun_state_t').
                   (∀a0.
                      (∃a. a0 =
                           (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                             a) ∨
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR (SUC 0) a
                                  (λn. ind_type$BOTTOM)) a) ⇒
                      $var$('betree_upsert_fun_state_t') a0) ⇒
                   $var$('betree_upsert_fun_state_t') a0) rep
   
   [betree_upsert_fun_state_t_case_def]  Definition
      
      ⊢ (∀a f f1.
           betree_upsert_fun_state_t_CASE (BetreeUpsertFunStateAdd a) f f1 =
           f a) ∧
        ∀a f f1.
          betree_upsert_fun_state_t_CASE (BetreeUpsertFunStateSub a) f f1 =
          f1 a
   
   [betree_upsert_fun_state_t_size_def]  Definition
      
      ⊢ (∀a. betree_upsert_fun_state_t_size (BetreeUpsertFunStateAdd a) = 1) ∧
        ∀a. betree_upsert_fun_state_t_size (BetreeUpsertFunStateSub a) = 1
   
   [EXISTS_betree_be_tree_t]  Theorem
      
      ⊢ ∀P. (∃b. P b) ⇔
            ∃b2 b1 b0.
              P
                <|betree_be_tree_params := b2;
                  betree_be_tree_node_id_cnt := b1;
                  betree_be_tree_root := b0|>
   
   [EXISTS_betree_internal_t]  Theorem
      
      ⊢ ∀P. (∃b. P b) ⇔
            ∃u0 u b1 b0.
              P
                <|betree_internal_id := u0; betree_internal_pivot := u;
                  betree_internal_left := b1; betree_internal_right := b0|>
   
   [EXISTS_betree_leaf_t]  Theorem
      
      ⊢ ∀P. (∃b. P b) ⇔
            ∃u0 u. P <|betree_leaf_id := u0; betree_leaf_size := u|>
   
   [EXISTS_betree_node_id_counter_t]  Theorem
      
      ⊢ ∀P. (∃b. P b) ⇔ ∃u. P <|betree_node_id_counter_next_node_id := u|>
   
   [EXISTS_betree_params_t]  Theorem
      
      ⊢ ∀P. (∃b. P b) ⇔
            ∃u0 u.
              P
                <|betree_params_min_flush_size := u0;
                  betree_params_split_size := u|>
   
   [FORALL_betree_be_tree_t]  Theorem
      
      ⊢ ∀P. (∀b. P b) ⇔
            ∀b2 b1 b0.
              P
                <|betree_be_tree_params := b2;
                  betree_be_tree_node_id_cnt := b1;
                  betree_be_tree_root := b0|>
   
   [FORALL_betree_internal_t]  Theorem
      
      ⊢ ∀P. (∀b. P b) ⇔
            ∀u0 u b1 b0.
              P
                <|betree_internal_id := u0; betree_internal_pivot := u;
                  betree_internal_left := b1; betree_internal_right := b0|>
   
   [FORALL_betree_leaf_t]  Theorem
      
      ⊢ ∀P. (∀b. P b) ⇔
            ∀u0 u. P <|betree_leaf_id := u0; betree_leaf_size := u|>
   
   [FORALL_betree_node_id_counter_t]  Theorem
      
      ⊢ ∀P. (∀b. P b) ⇔ ∀u. P <|betree_node_id_counter_next_node_id := u|>
   
   [FORALL_betree_params_t]  Theorem
      
      ⊢ ∀P. (∀b. P b) ⇔
            ∀u0 u.
              P
                <|betree_params_min_flush_size := u0;
                  betree_params_split_size := u|>
   
   [betree_be_tree_t_11]  Theorem
      
      ⊢ ∀a0 a1 a2 a0' a1' a2'.
          betree_be_tree_t a0 a1 a2 = betree_be_tree_t a0' a1' a2' ⇔
          a0 = a0' ∧ a1 = a1' ∧ a2 = a2'
   
   [betree_be_tree_t_Axiom]  Theorem
      
      ⊢ ∀f. ∃fn. ∀a0 a1 a2. fn (betree_be_tree_t a0 a1 a2) = f a0 a1 a2
   
   [betree_be_tree_t_accessors]  Theorem
      
      ⊢ (∀b b0 b1. (betree_be_tree_t b b0 b1).betree_be_tree_params = b) ∧
        (∀b b0 b1.
           (betree_be_tree_t b b0 b1).betree_be_tree_node_id_cnt = b0) ∧
        ∀b b0 b1. (betree_be_tree_t b b0 b1).betree_be_tree_root = b1
   
   [betree_be_tree_t_accfupds]  Theorem
      
      ⊢ (∀f b.
           (b with betree_be_tree_node_id_cnt updated_by f).
           betree_be_tree_params =
           b.betree_be_tree_params) ∧
        (∀f b.
           (b with betree_be_tree_root updated_by f).betree_be_tree_params =
           b.betree_be_tree_params) ∧
        (∀f b.
           (b with betree_be_tree_params updated_by f).
           betree_be_tree_node_id_cnt =
           b.betree_be_tree_node_id_cnt) ∧
        (∀f b.
           (b with betree_be_tree_root updated_by f).
           betree_be_tree_node_id_cnt =
           b.betree_be_tree_node_id_cnt) ∧
        (∀f b.
           (b with betree_be_tree_params updated_by f).betree_be_tree_root =
           b.betree_be_tree_root) ∧
        (∀f b.
           (b with betree_be_tree_node_id_cnt updated_by f).
           betree_be_tree_root =
           b.betree_be_tree_root) ∧
        (∀f b.
           (b with betree_be_tree_params updated_by f).
           betree_be_tree_params =
           f b.betree_be_tree_params) ∧
        (∀f b.
           (b with betree_be_tree_node_id_cnt updated_by f).
           betree_be_tree_node_id_cnt =
           f b.betree_be_tree_node_id_cnt) ∧
        ∀f b.
          (b with betree_be_tree_root updated_by f).betree_be_tree_root =
          f b.betree_be_tree_root
   
   [betree_be_tree_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧
          (∀a0 a1 a2.
             M' = betree_be_tree_t a0 a1 a2 ⇒ f a0 a1 a2 = f' a0 a1 a2) ⇒
          betree_be_tree_t_CASE M f = betree_be_tree_t_CASE M' f'
   
   [betree_be_tree_t_case_eq]  Theorem
      
      ⊢ betree_be_tree_t_CASE x f = v ⇔
        ∃b b0 b1. x = betree_be_tree_t b b0 b1 ∧ f b b0 b1 = v
   
   [betree_be_tree_t_component_equality]  Theorem
      
      ⊢ ∀b1 b2.
          b1 = b2 ⇔
          b1.betree_be_tree_params = b2.betree_be_tree_params ∧
          b1.betree_be_tree_node_id_cnt = b2.betree_be_tree_node_id_cnt ∧
          b1.betree_be_tree_root = b2.betree_be_tree_root
   
   [betree_be_tree_t_fn_updates]  Theorem
      
      ⊢ (∀f b b0 b1.
           betree_be_tree_t b b0 b1 with betree_be_tree_params updated_by f =
           betree_be_tree_t (f b) b0 b1) ∧
        (∀f b b0 b1.
           betree_be_tree_t b b0 b1 with
           betree_be_tree_node_id_cnt updated_by f =
           betree_be_tree_t b (f b0) b1) ∧
        ∀f b b0 b1.
          betree_be_tree_t b b0 b1 with betree_be_tree_root updated_by f =
          betree_be_tree_t b b0 (f b1)
   
   [betree_be_tree_t_fupdcanon]  Theorem
      
      ⊢ (∀g f b.
           b with
           <|betree_be_tree_node_id_cnt updated_by f;
             betree_be_tree_params updated_by g|> =
           b with
           <|betree_be_tree_params updated_by g;
             betree_be_tree_node_id_cnt updated_by f|>) ∧
        (∀g f b.
           b with
           <|betree_be_tree_root updated_by f;
             betree_be_tree_params updated_by g|> =
           b with
           <|betree_be_tree_params updated_by g;
             betree_be_tree_root updated_by f|>) ∧
        ∀g f b.
          b with
          <|betree_be_tree_root updated_by f;
            betree_be_tree_node_id_cnt updated_by g|> =
          b with
          <|betree_be_tree_node_id_cnt updated_by g;
            betree_be_tree_root updated_by f|>
   
   [betree_be_tree_t_fupdcanon_comp]  Theorem
      
      ⊢ ((∀g f.
            betree_be_tree_node_id_cnt_fupd f ∘
            betree_be_tree_params_fupd g =
            betree_be_tree_params_fupd g ∘
            betree_be_tree_node_id_cnt_fupd f) ∧
         ∀h g f.
           betree_be_tree_node_id_cnt_fupd f ∘
           betree_be_tree_params_fupd g ∘ h =
           betree_be_tree_params_fupd g ∘
           betree_be_tree_node_id_cnt_fupd f ∘ h) ∧
        ((∀g f.
            betree_be_tree_root_fupd f ∘ betree_be_tree_params_fupd g =
            betree_be_tree_params_fupd g ∘ betree_be_tree_root_fupd f) ∧
         ∀h g f.
           betree_be_tree_root_fupd f ∘ betree_be_tree_params_fupd g ∘ h =
           betree_be_tree_params_fupd g ∘ betree_be_tree_root_fupd f ∘ h) ∧
        (∀g f.
           betree_be_tree_root_fupd f ∘ betree_be_tree_node_id_cnt_fupd g =
           betree_be_tree_node_id_cnt_fupd g ∘ betree_be_tree_root_fupd f) ∧
        ∀h g f.
          betree_be_tree_root_fupd f ∘ betree_be_tree_node_id_cnt_fupd g ∘
          h =
          betree_be_tree_node_id_cnt_fupd g ∘ betree_be_tree_root_fupd f ∘
          h
   
   [betree_be_tree_t_fupdfupds]  Theorem
      
      ⊢ (∀g f b.
           b with
           <|betree_be_tree_params updated_by f;
             betree_be_tree_params updated_by g|> =
           b with betree_be_tree_params updated_by f ∘ g) ∧
        (∀g f b.
           b with
           <|betree_be_tree_node_id_cnt updated_by f;
             betree_be_tree_node_id_cnt updated_by g|> =
           b with betree_be_tree_node_id_cnt updated_by f ∘ g) ∧
        ∀g f b.
          b with
          <|betree_be_tree_root updated_by f;
            betree_be_tree_root updated_by g|> =
          b with betree_be_tree_root updated_by f ∘ g
   
   [betree_be_tree_t_fupdfupds_comp]  Theorem
      
      ⊢ ((∀g f.
            betree_be_tree_params_fupd f ∘ betree_be_tree_params_fupd g =
            betree_be_tree_params_fupd (f ∘ g)) ∧
         ∀h g f.
           betree_be_tree_params_fupd f ∘ betree_be_tree_params_fupd g ∘ h =
           betree_be_tree_params_fupd (f ∘ g) ∘ h) ∧
        ((∀g f.
            betree_be_tree_node_id_cnt_fupd f ∘
            betree_be_tree_node_id_cnt_fupd g =
            betree_be_tree_node_id_cnt_fupd (f ∘ g)) ∧
         ∀h g f.
           betree_be_tree_node_id_cnt_fupd f ∘
           betree_be_tree_node_id_cnt_fupd g ∘ h =
           betree_be_tree_node_id_cnt_fupd (f ∘ g) ∘ h) ∧
        (∀g f.
           betree_be_tree_root_fupd f ∘ betree_be_tree_root_fupd g =
           betree_be_tree_root_fupd (f ∘ g)) ∧
        ∀h g f.
          betree_be_tree_root_fupd f ∘ betree_be_tree_root_fupd g ∘ h =
          betree_be_tree_root_fupd (f ∘ g) ∘ h
   
   [betree_be_tree_t_induction]  Theorem
      
      ⊢ ∀P. (∀b b0 b1. P (betree_be_tree_t b b0 b1)) ⇒ ∀b. P b
   
   [betree_be_tree_t_literal_11]  Theorem
      
      ⊢ ∀b21 b11 b01 b22 b12 b02.
          <|betree_be_tree_params := b21;
            betree_be_tree_node_id_cnt := b11; betree_be_tree_root := b01|> =
          <|betree_be_tree_params := b22;
            betree_be_tree_node_id_cnt := b12; betree_be_tree_root := b02|> ⇔
          b21 = b22 ∧ b11 = b12 ∧ b01 = b02
   
   [betree_be_tree_t_literal_nchotomy]  Theorem
      
      ⊢ ∀b. ∃b2 b1 b0.
          b =
          <|betree_be_tree_params := b2; betree_be_tree_node_id_cnt := b1;
            betree_be_tree_root := b0|>
   
   [betree_be_tree_t_nchotomy]  Theorem
      
      ⊢ ∀bb. ∃b b0 b1. bb = betree_be_tree_t b b0 b1
   
   [betree_be_tree_t_updates_eq_literal]  Theorem
      
      ⊢ ∀b b2 b1 b0.
          b with
          <|betree_be_tree_params := b2; betree_be_tree_node_id_cnt := b1;
            betree_be_tree_root := b0|> =
          <|betree_be_tree_params := b2; betree_be_tree_node_id_cnt := b1;
            betree_be_tree_root := b0|>
   
   [betree_internal_t_11]  Theorem
      
      ⊢ ∀a0 a1 a2 a3 a0' a1' a2' a3'.
          betree_internal_t a0 a1 a2 a3 = betree_internal_t a0' a1' a2' a3' ⇔
          a0 = a0' ∧ a1 = a1' ∧ a2 = a2' ∧ a3 = a3'
   
   [betree_internal_t_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2. ∃fn0 fn1.
          (∀a0 a1 a2 a3.
             fn0 (betree_internal_t a0 a1 a2 a3) =
             f0 a0 a1 a2 a3 (fn1 a2) (fn1 a3)) ∧
          (∀a. fn1 (BetreeNodeInternal a) = f1 a (fn0 a)) ∧
          ∀a. fn1 (BetreeNodeLeaf a) = f2 a
   
   [betree_internal_t_accessors]  Theorem
      
      ⊢ (∀u u0 b b0. (betree_internal_t u u0 b b0).betree_internal_id = u) ∧
        (∀u u0 b b0.
           (betree_internal_t u u0 b b0).betree_internal_pivot = u0) ∧
        (∀u u0 b b0. (betree_internal_t u u0 b b0).betree_internal_left = b) ∧
        ∀u u0 b b0.
          (betree_internal_t u u0 b b0).betree_internal_right = b0
   
   [betree_internal_t_accfupds]  Theorem
      
      ⊢ (∀f b.
           (b with betree_internal_pivot updated_by f).betree_internal_id =
           b.betree_internal_id) ∧
        (∀f b.
           (b with betree_internal_left updated_by f).betree_internal_id =
           b.betree_internal_id) ∧
        (∀f b.
           (b with betree_internal_right updated_by f).betree_internal_id =
           b.betree_internal_id) ∧
        (∀f b.
           (b with betree_internal_id updated_by f).betree_internal_pivot =
           b.betree_internal_pivot) ∧
        (∀f b.
           (b with betree_internal_left updated_by f).betree_internal_pivot =
           b.betree_internal_pivot) ∧
        (∀f b.
           (b with betree_internal_right updated_by f).
           betree_internal_pivot =
           b.betree_internal_pivot) ∧
        (∀f b.
           (b with betree_internal_id updated_by f).betree_internal_left =
           b.betree_internal_left) ∧
        (∀f b.
           (b with betree_internal_pivot updated_by f).betree_internal_left =
           b.betree_internal_left) ∧
        (∀f b.
           (b with betree_internal_right updated_by f).betree_internal_left =
           b.betree_internal_left) ∧
        (∀f b.
           (b with betree_internal_id updated_by f).betree_internal_right =
           b.betree_internal_right) ∧
        (∀f b.
           (b with betree_internal_pivot updated_by f).
           betree_internal_right =
           b.betree_internal_right) ∧
        (∀f b.
           (b with betree_internal_left updated_by f).betree_internal_right =
           b.betree_internal_right) ∧
        (∀f b.
           (b with betree_internal_id updated_by f).betree_internal_id =
           f b.betree_internal_id) ∧
        (∀f b.
           (b with betree_internal_pivot updated_by f).
           betree_internal_pivot =
           f b.betree_internal_pivot) ∧
        (∀f b.
           (b with betree_internal_left updated_by f).betree_internal_left =
           f b.betree_internal_left) ∧
        ∀f b.
          (b with betree_internal_right updated_by f).betree_internal_right =
          f b.betree_internal_right
   
   [betree_internal_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧
          (∀a0 a1 a2 a3.
             M' = betree_internal_t a0 a1 a2 a3 ⇒
             f a0 a1 a2 a3 = f' a0 a1 a2 a3) ⇒
          betree_internal_t_CASE M f = betree_internal_t_CASE M' f'
   
   [betree_internal_t_case_eq]  Theorem
      
      ⊢ betree_internal_t_CASE x f = v ⇔
        ∃u0 u b b0. x = betree_internal_t u0 u b b0 ∧ f u0 u b b0 = v
   
   [betree_internal_t_component_equality]  Theorem
      
      ⊢ ∀b1 b2.
          b1 = b2 ⇔
          b1.betree_internal_id = b2.betree_internal_id ∧
          b1.betree_internal_pivot = b2.betree_internal_pivot ∧
          b1.betree_internal_left = b2.betree_internal_left ∧
          b1.betree_internal_right = b2.betree_internal_right
   
   [betree_internal_t_fn_updates]  Theorem
      
      ⊢ (∀f u u0 b b0.
           betree_internal_t u u0 b b0 with betree_internal_id updated_by f =
           betree_internal_t (f u) u0 b b0) ∧
        (∀f u u0 b b0.
           betree_internal_t u u0 b b0 with
           betree_internal_pivot updated_by f =
           betree_internal_t u (f u0) b b0) ∧
        (∀f u u0 b b0.
           betree_internal_t u u0 b b0 with
           betree_internal_left updated_by f =
           betree_internal_t u u0 (f b) b0) ∧
        ∀f u u0 b b0.
          betree_internal_t u u0 b b0 with
          betree_internal_right updated_by f =
          betree_internal_t u u0 b (f b0)
   
   [betree_internal_t_fupdcanon]  Theorem
      
      ⊢ (∀g f b.
           b with
           <|betree_internal_pivot updated_by f;
             betree_internal_id updated_by g|> =
           b with
           <|betree_internal_id updated_by g;
             betree_internal_pivot updated_by f|>) ∧
        (∀g f b.
           b with
           <|betree_internal_left updated_by f;
             betree_internal_id updated_by g|> =
           b with
           <|betree_internal_id updated_by g;
             betree_internal_left updated_by f|>) ∧
        (∀g f b.
           b with
           <|betree_internal_left updated_by f;
             betree_internal_pivot updated_by g|> =
           b with
           <|betree_internal_pivot updated_by g;
             betree_internal_left updated_by f|>) ∧
        (∀g f b.
           b with
           <|betree_internal_right updated_by f;
             betree_internal_id updated_by g|> =
           b with
           <|betree_internal_id updated_by g;
             betree_internal_right updated_by f|>) ∧
        (∀g f b.
           b with
           <|betree_internal_right updated_by f;
             betree_internal_pivot updated_by g|> =
           b with
           <|betree_internal_pivot updated_by g;
             betree_internal_right updated_by f|>) ∧
        ∀g f b.
          b with
          <|betree_internal_right updated_by f;
            betree_internal_left updated_by g|> =
          b with
          <|betree_internal_left updated_by g;
            betree_internal_right updated_by f|>
   
   [betree_internal_t_fupdcanon_comp]  Theorem
      
      ⊢ ((∀g f.
            betree_internal_pivot_fupd f ∘ betree_internal_id_fupd g =
            betree_internal_id_fupd g ∘ betree_internal_pivot_fupd f) ∧
         ∀h g f.
           betree_internal_pivot_fupd f ∘ betree_internal_id_fupd g ∘ h =
           betree_internal_id_fupd g ∘ betree_internal_pivot_fupd f ∘ h) ∧
        ((∀g f.
            betree_internal_left_fupd f ∘ betree_internal_id_fupd g =
            betree_internal_id_fupd g ∘ betree_internal_left_fupd f) ∧
         ∀h g f.
           betree_internal_left_fupd f ∘ betree_internal_id_fupd g ∘ h =
           betree_internal_id_fupd g ∘ betree_internal_left_fupd f ∘ h) ∧
        ((∀g f.
            betree_internal_left_fupd f ∘ betree_internal_pivot_fupd g =
            betree_internal_pivot_fupd g ∘ betree_internal_left_fupd f) ∧
         ∀h g f.
           betree_internal_left_fupd f ∘ betree_internal_pivot_fupd g ∘ h =
           betree_internal_pivot_fupd g ∘ betree_internal_left_fupd f ∘ h) ∧
        ((∀g f.
            betree_internal_right_fupd f ∘ betree_internal_id_fupd g =
            betree_internal_id_fupd g ∘ betree_internal_right_fupd f) ∧
         ∀h g f.
           betree_internal_right_fupd f ∘ betree_internal_id_fupd g ∘ h =
           betree_internal_id_fupd g ∘ betree_internal_right_fupd f ∘ h) ∧
        ((∀g f.
            betree_internal_right_fupd f ∘ betree_internal_pivot_fupd g =
            betree_internal_pivot_fupd g ∘ betree_internal_right_fupd f) ∧
         ∀h g f.
           betree_internal_right_fupd f ∘ betree_internal_pivot_fupd g ∘ h =
           betree_internal_pivot_fupd g ∘ betree_internal_right_fupd f ∘ h) ∧
        (∀g f.
           betree_internal_right_fupd f ∘ betree_internal_left_fupd g =
           betree_internal_left_fupd g ∘ betree_internal_right_fupd f) ∧
        ∀h g f.
          betree_internal_right_fupd f ∘ betree_internal_left_fupd g ∘ h =
          betree_internal_left_fupd g ∘ betree_internal_right_fupd f ∘ h
   
   [betree_internal_t_fupdfupds]  Theorem
      
      ⊢ (∀g f b.
           b with
           <|betree_internal_id updated_by f;
             betree_internal_id updated_by g|> =
           b with betree_internal_id updated_by f ∘ g) ∧
        (∀g f b.
           b with
           <|betree_internal_pivot updated_by f;
             betree_internal_pivot updated_by g|> =
           b with betree_internal_pivot updated_by f ∘ g) ∧
        (∀g f b.
           b with
           <|betree_internal_left updated_by f;
             betree_internal_left updated_by g|> =
           b with betree_internal_left updated_by f ∘ g) ∧
        ∀g f b.
          b with
          <|betree_internal_right updated_by f;
            betree_internal_right updated_by g|> =
          b with betree_internal_right updated_by f ∘ g
   
   [betree_internal_t_fupdfupds_comp]  Theorem
      
      ⊢ ((∀g f.
            betree_internal_id_fupd f ∘ betree_internal_id_fupd g =
            betree_internal_id_fupd (f ∘ g)) ∧
         ∀h g f.
           betree_internal_id_fupd f ∘ betree_internal_id_fupd g ∘ h =
           betree_internal_id_fupd (f ∘ g) ∘ h) ∧
        ((∀g f.
            betree_internal_pivot_fupd f ∘ betree_internal_pivot_fupd g =
            betree_internal_pivot_fupd (f ∘ g)) ∧
         ∀h g f.
           betree_internal_pivot_fupd f ∘ betree_internal_pivot_fupd g ∘ h =
           betree_internal_pivot_fupd (f ∘ g) ∘ h) ∧
        ((∀g f.
            betree_internal_left_fupd f ∘ betree_internal_left_fupd g =
            betree_internal_left_fupd (f ∘ g)) ∧
         ∀h g f.
           betree_internal_left_fupd f ∘ betree_internal_left_fupd g ∘ h =
           betree_internal_left_fupd (f ∘ g) ∘ h) ∧
        (∀g f.
           betree_internal_right_fupd f ∘ betree_internal_right_fupd g =
           betree_internal_right_fupd (f ∘ g)) ∧
        ∀h g f.
          betree_internal_right_fupd f ∘ betree_internal_right_fupd g ∘ h =
          betree_internal_right_fupd (f ∘ g) ∘ h
   
   [betree_internal_t_induction]  Theorem
      
      ⊢ ∀P0 P1.
          (∀b b0. P1 b ∧ P1 b0 ⇒ ∀u u0. P0 (betree_internal_t u0 u b b0)) ∧
          (∀b. P0 b ⇒ P1 (BetreeNodeInternal b)) ∧
          (∀b. P1 (BetreeNodeLeaf b)) ⇒
          (∀b. P0 b) ∧ ∀b. P1 b
   
   [betree_internal_t_literal_11]  Theorem
      
      ⊢ ∀u01 u1 b11 b01 u02 u2 b12 b02.
          <|betree_internal_id := u01; betree_internal_pivot := u1;
            betree_internal_left := b11; betree_internal_right := b01|> =
          <|betree_internal_id := u02; betree_internal_pivot := u2;
            betree_internal_left := b12; betree_internal_right := b02|> ⇔
          u01 = u02 ∧ u1 = u2 ∧ b11 = b12 ∧ b01 = b02
   
   [betree_internal_t_literal_nchotomy]  Theorem
      
      ⊢ ∀b. ∃u0 u b1 b0.
          b =
          <|betree_internal_id := u0; betree_internal_pivot := u;
            betree_internal_left := b1; betree_internal_right := b0|>
   
   [betree_internal_t_nchotomy]  Theorem
      
      ⊢ ∀bb. ∃u0 u b b0. bb = betree_internal_t u0 u b b0
   
   [betree_internal_t_updates_eq_literal]  Theorem
      
      ⊢ ∀b u0 u b1 b0.
          b with
          <|betree_internal_id := u0; betree_internal_pivot := u;
            betree_internal_left := b1; betree_internal_right := b0|> =
          <|betree_internal_id := u0; betree_internal_pivot := u;
            betree_internal_left := b1; betree_internal_right := b0|>
   
   [betree_leaf_t_11]  Theorem
      
      ⊢ ∀a0 a1 a0' a1'.
          betree_leaf_t a0 a1 = betree_leaf_t a0' a1' ⇔ a0 = a0' ∧ a1 = a1'
   
   [betree_leaf_t_Axiom]  Theorem
      
      ⊢ ∀f. ∃fn. ∀a0 a1. fn (betree_leaf_t a0 a1) = f a0 a1
   
   [betree_leaf_t_accessors]  Theorem
      
      ⊢ (∀u u0. (betree_leaf_t u u0).betree_leaf_id = u) ∧
        ∀u u0. (betree_leaf_t u u0).betree_leaf_size = u0
   
   [betree_leaf_t_accfupds]  Theorem
      
      ⊢ (∀f b.
           (b with betree_leaf_size updated_by f).betree_leaf_id =
           b.betree_leaf_id) ∧
        (∀f b.
           (b with betree_leaf_id updated_by f).betree_leaf_size =
           b.betree_leaf_size) ∧
        (∀f b.
           (b with betree_leaf_id updated_by f).betree_leaf_id =
           f b.betree_leaf_id) ∧
        ∀f b.
          (b with betree_leaf_size updated_by f).betree_leaf_size =
          f b.betree_leaf_size
   
   [betree_leaf_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧ (∀a0 a1. M' = betree_leaf_t a0 a1 ⇒ f a0 a1 = f' a0 a1) ⇒
          betree_leaf_t_CASE M f = betree_leaf_t_CASE M' f'
   
   [betree_leaf_t_case_eq]  Theorem
      
      ⊢ betree_leaf_t_CASE x f = v ⇔
        ∃u u0. x = betree_leaf_t u u0 ∧ f u u0 = v
   
   [betree_leaf_t_component_equality]  Theorem
      
      ⊢ ∀b1 b2.
          b1 = b2 ⇔
          b1.betree_leaf_id = b2.betree_leaf_id ∧
          b1.betree_leaf_size = b2.betree_leaf_size
   
   [betree_leaf_t_fn_updates]  Theorem
      
      ⊢ (∀f u u0.
           betree_leaf_t u u0 with betree_leaf_id updated_by f =
           betree_leaf_t (f u) u0) ∧
        ∀f u u0.
          betree_leaf_t u u0 with betree_leaf_size updated_by f =
          betree_leaf_t u (f u0)
   
   [betree_leaf_t_fupdcanon]  Theorem
      
      ⊢ ∀g f b.
          b with
          <|betree_leaf_size updated_by f; betree_leaf_id updated_by g|> =
          b with
          <|betree_leaf_id updated_by g; betree_leaf_size updated_by f|>
   
   [betree_leaf_t_fupdcanon_comp]  Theorem
      
      ⊢ (∀g f.
           betree_leaf_size_fupd f ∘ betree_leaf_id_fupd g =
           betree_leaf_id_fupd g ∘ betree_leaf_size_fupd f) ∧
        ∀h g f.
          betree_leaf_size_fupd f ∘ betree_leaf_id_fupd g ∘ h =
          betree_leaf_id_fupd g ∘ betree_leaf_size_fupd f ∘ h
   
   [betree_leaf_t_fupdfupds]  Theorem
      
      ⊢ (∀g f b.
           b with
           <|betree_leaf_id updated_by f; betree_leaf_id updated_by g|> =
           b with betree_leaf_id updated_by f ∘ g) ∧
        ∀g f b.
          b with
          <|betree_leaf_size updated_by f; betree_leaf_size updated_by g|> =
          b with betree_leaf_size updated_by f ∘ g
   
   [betree_leaf_t_fupdfupds_comp]  Theorem
      
      ⊢ ((∀g f.
            betree_leaf_id_fupd f ∘ betree_leaf_id_fupd g =
            betree_leaf_id_fupd (f ∘ g)) ∧
         ∀h g f.
           betree_leaf_id_fupd f ∘ betree_leaf_id_fupd g ∘ h =
           betree_leaf_id_fupd (f ∘ g) ∘ h) ∧
        (∀g f.
           betree_leaf_size_fupd f ∘ betree_leaf_size_fupd g =
           betree_leaf_size_fupd (f ∘ g)) ∧
        ∀h g f.
          betree_leaf_size_fupd f ∘ betree_leaf_size_fupd g ∘ h =
          betree_leaf_size_fupd (f ∘ g) ∘ h
   
   [betree_leaf_t_induction]  Theorem
      
      ⊢ ∀P. (∀u u0. P (betree_leaf_t u u0)) ⇒ ∀b. P b
   
   [betree_leaf_t_literal_11]  Theorem
      
      ⊢ ∀u01 u1 u02 u2.
          <|betree_leaf_id := u01; betree_leaf_size := u1|> =
          <|betree_leaf_id := u02; betree_leaf_size := u2|> ⇔
          u01 = u02 ∧ u1 = u2
   
   [betree_leaf_t_literal_nchotomy]  Theorem
      
      ⊢ ∀b. ∃u0 u. b = <|betree_leaf_id := u0; betree_leaf_size := u|>
   
   [betree_leaf_t_nchotomy]  Theorem
      
      ⊢ ∀bb. ∃u u0. bb = betree_leaf_t u u0
   
   [betree_leaf_t_updates_eq_literal]  Theorem
      
      ⊢ ∀b u0 u.
          b with <|betree_leaf_id := u0; betree_leaf_size := u|> =
          <|betree_leaf_id := u0; betree_leaf_size := u|>
   
   [betree_list_t_11]  Theorem
      
      ⊢ ∀a0 a1 a0' a1'.
          BetreeListCons a0 a1 = BetreeListCons a0' a1' ⇔
          a0 = a0' ∧ a1 = a1'
   
   [betree_list_t_Axiom]  Theorem
      
      ⊢ ∀f0 f1. ∃fn.
          (∀a0 a1. fn (BetreeListCons a0 a1) = f0 a0 a1 (fn a1)) ∧
          fn BetreeListNil = f1
   
   [betree_list_t_case_cong]  Theorem
      
      ⊢ ∀M M' f v.
          M = M' ∧
          (∀a0 a1. M' = BetreeListCons a0 a1 ⇒ f a0 a1 = f' a0 a1) ∧
          (M' = BetreeListNil ⇒ v = v') ⇒
          betree_list_t_CASE M f v = betree_list_t_CASE M' f' v'
   
   [betree_list_t_case_eq]  Theorem
      
      ⊢ betree_list_t_CASE x f v = v' ⇔
        (∃t b. x = BetreeListCons t b ∧ f t b = v') ∨
        x = BetreeListNil ∧ v = v'
   
   [betree_list_t_distinct]  Theorem
      
      ⊢ ∀a1 a0. BetreeListCons a0 a1 ≠ BetreeListNil
   
   [betree_list_t_induction]  Theorem
      
      ⊢ ∀P. (∀b. P b ⇒ ∀t. P (BetreeListCons t b)) ∧ P BetreeListNil ⇒
            ∀b. P b
   
   [betree_list_t_nchotomy]  Theorem
      
      ⊢ ∀bb. (∃t b. bb = BetreeListCons t b) ∨ bb = BetreeListNil
   
   [betree_message_t_11]  Theorem
      
      ⊢ (∀a a'. BetreeMessageInsert a = BetreeMessageInsert a' ⇔ a = a') ∧
        ∀a a'. BetreeMessageUpsert a = BetreeMessageUpsert a' ⇔ a = a'
   
   [betree_message_t_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2. ∃fn.
          (∀a. fn (BetreeMessageInsert a) = f0 a) ∧
          fn BetreeMessageDelete = f1 ∧
          ∀a. fn (BetreeMessageUpsert a) = f2 a
   
   [betree_message_t_case_cong]  Theorem
      
      ⊢ ∀M M' f v f1.
          M = M' ∧ (∀a. M' = BetreeMessageInsert a ⇒ f a = f' a) ∧
          (M' = BetreeMessageDelete ⇒ v = v') ∧
          (∀a. M' = BetreeMessageUpsert a ⇒ f1 a = f1' a) ⇒
          betree_message_t_CASE M f v f1 =
          betree_message_t_CASE M' f' v' f1'
   
   [betree_message_t_case_eq]  Theorem
      
      ⊢ betree_message_t_CASE x f v f1 = v' ⇔
        (∃u. x = BetreeMessageInsert u ∧ f u = v') ∨
        x = BetreeMessageDelete ∧ v = v' ∨
        ∃b. x = BetreeMessageUpsert b ∧ f1 b = v'
   
   [betree_message_t_distinct]  Theorem
      
      ⊢ (∀a. BetreeMessageInsert a ≠ BetreeMessageDelete) ∧
        (∀a' a. BetreeMessageInsert a ≠ BetreeMessageUpsert a') ∧
        ∀a. BetreeMessageDelete ≠ BetreeMessageUpsert a
   
   [betree_message_t_induction]  Theorem
      
      ⊢ ∀P. (∀u. P (BetreeMessageInsert u)) ∧ P BetreeMessageDelete ∧
            (∀b. P (BetreeMessageUpsert b)) ⇒
            ∀b. P b
   
   [betree_message_t_nchotomy]  Theorem
      
      ⊢ ∀bb.
          (∃u. bb = BetreeMessageInsert u) ∨ bb = BetreeMessageDelete ∨
          ∃b. bb = BetreeMessageUpsert b
   
   [betree_node_id_counter_t_11]  Theorem
      
      ⊢ ∀a a'.
          betree_node_id_counter_t a = betree_node_id_counter_t a' ⇔ a = a'
   
   [betree_node_id_counter_t_Axiom]  Theorem
      
      ⊢ ∀f. ∃fn. ∀a. fn (betree_node_id_counter_t a) = f a
   
   [betree_node_id_counter_t_accessors]  Theorem
      
      ⊢ ∀u. (betree_node_id_counter_t u).
            betree_node_id_counter_next_node_id =
            u
   
   [betree_node_id_counter_t_accfupds]  Theorem
      
      ⊢ ∀f b.
          (b with betree_node_id_counter_next_node_id updated_by f).
          betree_node_id_counter_next_node_id =
          f b.betree_node_id_counter_next_node_id
   
   [betree_node_id_counter_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧ (∀a. M' = betree_node_id_counter_t a ⇒ f a = f' a) ⇒
          betree_node_id_counter_t_CASE M f =
          betree_node_id_counter_t_CASE M' f'
   
   [betree_node_id_counter_t_case_eq]  Theorem
      
      ⊢ betree_node_id_counter_t_CASE x f = v ⇔
        ∃u. x = betree_node_id_counter_t u ∧ f u = v
   
   [betree_node_id_counter_t_component_equality]  Theorem
      
      ⊢ ∀b1 b2.
          b1 = b2 ⇔
          b1.betree_node_id_counter_next_node_id =
          b2.betree_node_id_counter_next_node_id
   
   [betree_node_id_counter_t_fn_updates]  Theorem
      
      ⊢ ∀f u.
          betree_node_id_counter_t u with
          betree_node_id_counter_next_node_id updated_by f =
          betree_node_id_counter_t (f u)
   
   [betree_node_id_counter_t_fupdfupds]  Theorem
      
      ⊢ ∀g f b.
          b with
          <|betree_node_id_counter_next_node_id updated_by f;
            betree_node_id_counter_next_node_id updated_by g|> =
          b with betree_node_id_counter_next_node_id updated_by f ∘ g
   
   [betree_node_id_counter_t_fupdfupds_comp]  Theorem
      
      ⊢ (∀g f.
           betree_node_id_counter_next_node_id_fupd f ∘
           betree_node_id_counter_next_node_id_fupd g =
           betree_node_id_counter_next_node_id_fupd (f ∘ g)) ∧
        ∀h g f.
          betree_node_id_counter_next_node_id_fupd f ∘
          betree_node_id_counter_next_node_id_fupd g ∘ h =
          betree_node_id_counter_next_node_id_fupd (f ∘ g) ∘ h
   
   [betree_node_id_counter_t_induction]  Theorem
      
      ⊢ ∀P. (∀u. P (betree_node_id_counter_t u)) ⇒ ∀b. P b
   
   [betree_node_id_counter_t_literal_11]  Theorem
      
      ⊢ ∀u1 u2.
          <|betree_node_id_counter_next_node_id := u1|> =
          <|betree_node_id_counter_next_node_id := u2|> ⇔ u1 = u2
   
   [betree_node_id_counter_t_literal_nchotomy]  Theorem
      
      ⊢ ∀b. ∃u. b = <|betree_node_id_counter_next_node_id := u|>
   
   [betree_node_id_counter_t_nchotomy]  Theorem
      
      ⊢ ∀bb. ∃u. bb = betree_node_id_counter_t u
   
   [betree_node_id_counter_t_updates_eq_literal]  Theorem
      
      ⊢ ∀b u.
          b with betree_node_id_counter_next_node_id := u =
          <|betree_node_id_counter_next_node_id := u|>
   
   [betree_node_t_11]  Theorem
      
      ⊢ (∀a a'. BetreeNodeInternal a = BetreeNodeInternal a' ⇔ a = a') ∧
        ∀a a'. BetreeNodeLeaf a = BetreeNodeLeaf a' ⇔ a = a'
   
   [betree_node_t_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2. ∃fn0 fn1.
          (∀a0 a1 a2 a3.
             fn0 (betree_internal_t a0 a1 a2 a3) =
             f0 a0 a1 a2 a3 (fn1 a2) (fn1 a3)) ∧
          (∀a. fn1 (BetreeNodeInternal a) = f1 a (fn0 a)) ∧
          ∀a. fn1 (BetreeNodeLeaf a) = f2 a
   
   [betree_node_t_case_cong]  Theorem
      
      ⊢ ∀M M' f f1.
          M = M' ∧ (∀a. M' = BetreeNodeInternal a ⇒ f a = f' a) ∧
          (∀a. M' = BetreeNodeLeaf a ⇒ f1 a = f1' a) ⇒
          betree_node_t_CASE M f f1 = betree_node_t_CASE M' f' f1'
   
   [betree_node_t_case_eq]  Theorem
      
      ⊢ betree_node_t_CASE x f f1 = v ⇔
        (∃b. x = BetreeNodeInternal b ∧ f b = v) ∨
        ∃b. x = BetreeNodeLeaf b ∧ f1 b = v
   
   [betree_node_t_distinct]  Theorem
      
      ⊢ ∀a' a. BetreeNodeInternal a ≠ BetreeNodeLeaf a'
   
   [betree_node_t_induction]  Theorem
      
      ⊢ ∀P0 P1.
          (∀b b0. P1 b ∧ P1 b0 ⇒ ∀u u0. P0 (betree_internal_t u0 u b b0)) ∧
          (∀b. P0 b ⇒ P1 (BetreeNodeInternal b)) ∧
          (∀b. P1 (BetreeNodeLeaf b)) ⇒
          (∀b. P0 b) ∧ ∀b. P1 b
   
   [betree_node_t_nchotomy]  Theorem
      
      ⊢ ∀bb. (∃b. bb = BetreeNodeInternal b) ∨ ∃b. bb = BetreeNodeLeaf b
   
   [betree_params_t_11]  Theorem
      
      ⊢ ∀a0 a1 a0' a1'.
          betree_params_t a0 a1 = betree_params_t a0' a1' ⇔
          a0 = a0' ∧ a1 = a1'
   
   [betree_params_t_Axiom]  Theorem
      
      ⊢ ∀f. ∃fn. ∀a0 a1. fn (betree_params_t a0 a1) = f a0 a1
   
   [betree_params_t_accessors]  Theorem
      
      ⊢ (∀u u0. (betree_params_t u u0).betree_params_min_flush_size = u) ∧
        ∀u u0. (betree_params_t u u0).betree_params_split_size = u0
   
   [betree_params_t_accfupds]  Theorem
      
      ⊢ (∀f b.
           (b with betree_params_split_size updated_by f).
           betree_params_min_flush_size =
           b.betree_params_min_flush_size) ∧
        (∀f b.
           (b with betree_params_min_flush_size updated_by f).
           betree_params_split_size =
           b.betree_params_split_size) ∧
        (∀f b.
           (b with betree_params_min_flush_size updated_by f).
           betree_params_min_flush_size =
           f b.betree_params_min_flush_size) ∧
        ∀f b.
          (b with betree_params_split_size updated_by f).
          betree_params_split_size =
          f b.betree_params_split_size
   
   [betree_params_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧
          (∀a0 a1. M' = betree_params_t a0 a1 ⇒ f a0 a1 = f' a0 a1) ⇒
          betree_params_t_CASE M f = betree_params_t_CASE M' f'
   
   [betree_params_t_case_eq]  Theorem
      
      ⊢ betree_params_t_CASE x f = v ⇔
        ∃u u0. x = betree_params_t u u0 ∧ f u u0 = v
   
   [betree_params_t_component_equality]  Theorem
      
      ⊢ ∀b1 b2.
          b1 = b2 ⇔
          b1.betree_params_min_flush_size = b2.betree_params_min_flush_size ∧
          b1.betree_params_split_size = b2.betree_params_split_size
   
   [betree_params_t_fn_updates]  Theorem
      
      ⊢ (∀f u u0.
           betree_params_t u u0 with
           betree_params_min_flush_size updated_by f =
           betree_params_t (f u) u0) ∧
        ∀f u u0.
          betree_params_t u u0 with betree_params_split_size updated_by f =
          betree_params_t u (f u0)
   
   [betree_params_t_fupdcanon]  Theorem
      
      ⊢ ∀g f b.
          b with
          <|betree_params_split_size updated_by f;
            betree_params_min_flush_size updated_by g|> =
          b with
          <|betree_params_min_flush_size updated_by g;
            betree_params_split_size updated_by f|>
   
   [betree_params_t_fupdcanon_comp]  Theorem
      
      ⊢ (∀g f.
           betree_params_split_size_fupd f ∘
           betree_params_min_flush_size_fupd g =
           betree_params_min_flush_size_fupd g ∘
           betree_params_split_size_fupd f) ∧
        ∀h g f.
          betree_params_split_size_fupd f ∘
          betree_params_min_flush_size_fupd g ∘ h =
          betree_params_min_flush_size_fupd g ∘
          betree_params_split_size_fupd f ∘ h
   
   [betree_params_t_fupdfupds]  Theorem
      
      ⊢ (∀g f b.
           b with
           <|betree_params_min_flush_size updated_by f;
             betree_params_min_flush_size updated_by g|> =
           b with betree_params_min_flush_size updated_by f ∘ g) ∧
        ∀g f b.
          b with
          <|betree_params_split_size updated_by f;
            betree_params_split_size updated_by g|> =
          b with betree_params_split_size updated_by f ∘ g
   
   [betree_params_t_fupdfupds_comp]  Theorem
      
      ⊢ ((∀g f.
            betree_params_min_flush_size_fupd f ∘
            betree_params_min_flush_size_fupd g =
            betree_params_min_flush_size_fupd (f ∘ g)) ∧
         ∀h g f.
           betree_params_min_flush_size_fupd f ∘
           betree_params_min_flush_size_fupd g ∘ h =
           betree_params_min_flush_size_fupd (f ∘ g) ∘ h) ∧
        (∀g f.
           betree_params_split_size_fupd f ∘
           betree_params_split_size_fupd g =
           betree_params_split_size_fupd (f ∘ g)) ∧
        ∀h g f.
          betree_params_split_size_fupd f ∘
          betree_params_split_size_fupd g ∘ h =
          betree_params_split_size_fupd (f ∘ g) ∘ h
   
   [betree_params_t_induction]  Theorem
      
      ⊢ ∀P. (∀u u0. P (betree_params_t u u0)) ⇒ ∀b. P b
   
   [betree_params_t_literal_11]  Theorem
      
      ⊢ ∀u01 u1 u02 u2.
          <|betree_params_min_flush_size := u01;
            betree_params_split_size := u1|> =
          <|betree_params_min_flush_size := u02;
            betree_params_split_size := u2|> ⇔ u01 = u02 ∧ u1 = u2
   
   [betree_params_t_literal_nchotomy]  Theorem
      
      ⊢ ∀b. ∃u0 u.
          b =
          <|betree_params_min_flush_size := u0;
            betree_params_split_size := u|>
   
   [betree_params_t_nchotomy]  Theorem
      
      ⊢ ∀bb. ∃u u0. bb = betree_params_t u u0
   
   [betree_params_t_updates_eq_literal]  Theorem
      
      ⊢ ∀b u0 u.
          b with
          <|betree_params_min_flush_size := u0;
            betree_params_split_size := u|> =
          <|betree_params_min_flush_size := u0;
            betree_params_split_size := u|>
   
   [betree_upsert_fun_state_t_11]  Theorem
      
      ⊢ (∀a a'.
           BetreeUpsertFunStateAdd a = BetreeUpsertFunStateAdd a' ⇔ a = a') ∧
        ∀a a'.
          BetreeUpsertFunStateSub a = BetreeUpsertFunStateSub a' ⇔ a = a'
   
   [betree_upsert_fun_state_t_Axiom]  Theorem
      
      ⊢ ∀f0 f1. ∃fn.
          (∀a. fn (BetreeUpsertFunStateAdd a) = f0 a) ∧
          ∀a. fn (BetreeUpsertFunStateSub a) = f1 a
   
   [betree_upsert_fun_state_t_case_cong]  Theorem
      
      ⊢ ∀M M' f f1.
          M = M' ∧ (∀a. M' = BetreeUpsertFunStateAdd a ⇒ f a = f' a) ∧
          (∀a. M' = BetreeUpsertFunStateSub a ⇒ f1 a = f1' a) ⇒
          betree_upsert_fun_state_t_CASE M f f1 =
          betree_upsert_fun_state_t_CASE M' f' f1'
   
   [betree_upsert_fun_state_t_case_eq]  Theorem
      
      ⊢ betree_upsert_fun_state_t_CASE x f f1 = v ⇔
        (∃u. x = BetreeUpsertFunStateAdd u ∧ f u = v) ∨
        ∃u. x = BetreeUpsertFunStateSub u ∧ f1 u = v
   
   [betree_upsert_fun_state_t_distinct]  Theorem
      
      ⊢ ∀a' a. BetreeUpsertFunStateAdd a ≠ BetreeUpsertFunStateSub a'
   
   [betree_upsert_fun_state_t_induction]  Theorem
      
      ⊢ ∀P. (∀u. P (BetreeUpsertFunStateAdd u)) ∧
            (∀u. P (BetreeUpsertFunStateSub u)) ⇒
            ∀b. P b
   
   [betree_upsert_fun_state_t_nchotomy]  Theorem
      
      ⊢ ∀bb.
          (∃u. bb = BetreeUpsertFunStateAdd u) ∨
          ∃u. bb = BetreeUpsertFunStateSub u
   
   [datatype_betree_be_tree_t]  Theorem
      
      ⊢ DATATYPE
          (record betree_be_tree_t betree_be_tree_params
             betree_be_tree_node_id_cnt betree_be_tree_root)
   
   [datatype_betree_internal_t]  Theorem
      
      ⊢ DATATYPE
          (record betree_internal_t betree_internal_id
             betree_internal_pivot betree_internal_left
             betree_internal_right ∧
           betree_node_t BetreeNodeInternal BetreeNodeLeaf)
   
   [datatype_betree_leaf_t]  Theorem
      
      ⊢ DATATYPE (record betree_leaf_t betree_leaf_id betree_leaf_size)
   
   [datatype_betree_list_t]  Theorem
      
      ⊢ DATATYPE (betree_list_t BetreeListCons BetreeListNil)
   
   [datatype_betree_message_t]  Theorem
      
      ⊢ DATATYPE
          (betree_message_t BetreeMessageInsert BetreeMessageDelete
             BetreeMessageUpsert)
   
   [datatype_betree_node_id_counter_t]  Theorem
      
      ⊢ DATATYPE
          (record betree_node_id_counter_t
             betree_node_id_counter_next_node_id)
   
   [datatype_betree_params_t]  Theorem
      
      ⊢ DATATYPE
          (record betree_params_t betree_params_min_flush_size
             betree_params_split_size)
   
   [datatype_betree_upsert_fun_state_t]  Theorem
      
      ⊢ DATATYPE
          (betree_upsert_fun_state_t BetreeUpsertFunStateAdd
             BetreeUpsertFunStateSub)
   
   
*)
end
