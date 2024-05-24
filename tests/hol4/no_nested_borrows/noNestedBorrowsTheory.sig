signature noNestedBorrowsTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val add_test_fwd_def : thm
    val cast_test_fwd_def : thm
    val choose_back_def : thm
    val choose_fwd_def : thm
    val choose_test_fwd_def : thm
    val copy_int_fwd_def : thm
    val div_test1_fwd_def : thm
    val div_test_fwd_def : thm
    val empty_enum_t_BIJ : thm
    val empty_enum_t_CASE : thm
    val empty_enum_t_TY_DEF : thm
    val empty_enum_t_size_def : thm
    val enum_t_BIJ : thm
    val enum_t_CASE : thm
    val enum_t_TY_DEF : thm
    val enum_t_size_def : thm
    val get_max_fwd_def : thm
    val id_mut_pair1_back_def : thm
    val id_mut_pair1_fwd_def : thm
    val id_mut_pair2_back_def : thm
    val id_mut_pair2_fwd_def : thm
    val id_mut_pair3_back'a_def : thm
    val id_mut_pair3_back'b_def : thm
    val id_mut_pair3_fwd_def : thm
    val id_mut_pair4_back'a_def : thm
    val id_mut_pair4_back'b_def : thm
    val id_mut_pair4_fwd_def : thm
    val is_cons_fwd_def : thm
    val list_length_fwd_def : thm
    val list_nth_mut_back_def : thm
    val list_nth_mut_fwd_def : thm
    val list_nth_shared_fwd_def : thm
    val list_rev_aux_fwd_def : thm
    val list_rev_fwd_back_def : thm
    val list_t_TY_DEF : thm
    val list_t_case_def : thm
    val list_t_size_def : thm
    val neg_test_fwd_def : thm
    val new_pair1_fwd_def : thm
    val new_tuple1_fwd_def : thm
    val new_tuple2_fwd_def : thm
    val new_tuple3_fwd_def : thm
    val node_elem_t_TY_DEF : thm
    val node_elem_t_case_def : thm
    val one_t_TY_DEF : thm
    val one_t_case_def : thm
    val one_t_size_def : thm
    val pair_t_TY_DEF : thm
    val pair_t_case_def : thm
    val pair_t_pair_x : thm
    val pair_t_pair_x_fupd : thm
    val pair_t_pair_y : thm
    val pair_t_pair_y_fupd : thm
    val pair_t_size_def : thm
    val refs_test1_fwd_def : thm
    val refs_test2_fwd_def : thm
    val rem_test_fwd_def : thm
    val split_list_fwd_def : thm
    val struct_with_pair_t_TY_DEF : thm
    val struct_with_pair_t_case_def : thm
    val struct_with_pair_t_size_def : thm
    val struct_with_pair_t_struct_with_pair_p : thm
    val struct_with_pair_t_struct_with_pair_p_fupd : thm
    val struct_with_tuple_t_TY_DEF : thm
    val struct_with_tuple_t_case_def : thm
    val struct_with_tuple_t_size_def : thm
    val struct_with_tuple_t_struct_with_tuple_p : thm
    val struct_with_tuple_t_struct_with_tuple_p_fupd : thm
    val subs_test_fwd_def : thm
    val sum_t_TY_DEF : thm
    val sum_t_case_def : thm
    val sum_t_size_def : thm
    val test2_fwd_def : thm
    val test3_fwd_def : thm
    val test_box1_fwd_def : thm
    val test_char_fwd_def : thm
    val test_constants_fwd_def : thm
    val test_copy_int_fwd_def : thm
    val test_is_cons_fwd_def : thm
    val test_list1_fwd_def : thm
    val test_list_functions_fwd_def : thm
    val test_mem_replace_fwd_back_def : thm
    val test_neg1_fwd_def : thm
    val test_panic_fwd_def : thm
    val test_shared_borrow_bool1_fwd_def : thm
    val test_shared_borrow_bool2_fwd_def : thm
    val test_shared_borrow_enum1_fwd_def : thm
    val test_shared_borrow_enum2_fwd_def : thm
    val test_split_list_fwd_def : thm
    val test_unreachable_fwd_def : thm
    val test_weird_borrows1_fwd_def : thm
    val tree_t_TY_DEF : thm
    val tree_t_case_def : thm
    val tree_t_size_def : thm
  
  (*  Theorems  *)
    val EXISTS_pair_t : thm
    val EXISTS_struct_with_pair_t : thm
    val EXISTS_struct_with_tuple_t : thm
    val FORALL_pair_t : thm
    val FORALL_struct_with_pair_t : thm
    val FORALL_struct_with_tuple_t : thm
    val datatype_empty_enum_t : thm
    val datatype_enum_t : thm
    val datatype_list_t : thm
    val datatype_one_t : thm
    val datatype_pair_t : thm
    val datatype_struct_with_pair_t : thm
    val datatype_struct_with_tuple_t : thm
    val datatype_sum_t : thm
    val datatype_tree_t : thm
    val empty_enum_t2num_11 : thm
    val empty_enum_t2num_ONTO : thm
    val empty_enum_t2num_num2empty_enum_t : thm
    val empty_enum_t2num_thm : thm
    val empty_enum_t_Axiom : thm
    val empty_enum_t_EQ_empty_enum_t : thm
    val empty_enum_t_case_cong : thm
    val empty_enum_t_case_def : thm
    val empty_enum_t_case_eq : thm
    val empty_enum_t_induction : thm
    val empty_enum_t_nchotomy : thm
    val enum_t2num_11 : thm
    val enum_t2num_ONTO : thm
    val enum_t2num_num2enum_t : thm
    val enum_t2num_thm : thm
    val enum_t_Axiom : thm
    val enum_t_EQ_enum_t : thm
    val enum_t_case_cong : thm
    val enum_t_case_def : thm
    val enum_t_case_eq : thm
    val enum_t_distinct : thm
    val enum_t_induction : thm
    val enum_t_nchotomy : thm
    val list_t_11 : thm
    val list_t_Axiom : thm
    val list_t_case_cong : thm
    val list_t_case_eq : thm
    val list_t_distinct : thm
    val list_t_induction : thm
    val list_t_nchotomy : thm
    val node_elem_t_11 : thm
    val node_elem_t_Axiom : thm
    val node_elem_t_case_cong : thm
    val node_elem_t_case_eq : thm
    val node_elem_t_distinct : thm
    val node_elem_t_induction : thm
    val node_elem_t_nchotomy : thm
    val num2empty_enum_t_11 : thm
    val num2empty_enum_t_ONTO : thm
    val num2empty_enum_t_empty_enum_t2num : thm
    val num2empty_enum_t_thm : thm
    val num2enum_t_11 : thm
    val num2enum_t_ONTO : thm
    val num2enum_t_enum_t2num : thm
    val num2enum_t_thm : thm
    val one_t_11 : thm
    val one_t_Axiom : thm
    val one_t_case_cong : thm
    val one_t_case_eq : thm
    val one_t_induction : thm
    val one_t_nchotomy : thm
    val pair_t_11 : thm
    val pair_t_Axiom : thm
    val pair_t_accessors : thm
    val pair_t_accfupds : thm
    val pair_t_case_cong : thm
    val pair_t_case_eq : thm
    val pair_t_component_equality : thm
    val pair_t_fn_updates : thm
    val pair_t_fupdcanon : thm
    val pair_t_fupdcanon_comp : thm
    val pair_t_fupdfupds : thm
    val pair_t_fupdfupds_comp : thm
    val pair_t_induction : thm
    val pair_t_literal_11 : thm
    val pair_t_literal_nchotomy : thm
    val pair_t_nchotomy : thm
    val pair_t_updates_eq_literal : thm
    val struct_with_pair_t_11 : thm
    val struct_with_pair_t_Axiom : thm
    val struct_with_pair_t_accessors : thm
    val struct_with_pair_t_accfupds : thm
    val struct_with_pair_t_case_cong : thm
    val struct_with_pair_t_case_eq : thm
    val struct_with_pair_t_component_equality : thm
    val struct_with_pair_t_fn_updates : thm
    val struct_with_pair_t_fupdfupds : thm
    val struct_with_pair_t_fupdfupds_comp : thm
    val struct_with_pair_t_induction : thm
    val struct_with_pair_t_literal_11 : thm
    val struct_with_pair_t_literal_nchotomy : thm
    val struct_with_pair_t_nchotomy : thm
    val struct_with_pair_t_updates_eq_literal : thm
    val struct_with_tuple_t_11 : thm
    val struct_with_tuple_t_Axiom : thm
    val struct_with_tuple_t_accessors : thm
    val struct_with_tuple_t_accfupds : thm
    val struct_with_tuple_t_case_cong : thm
    val struct_with_tuple_t_case_eq : thm
    val struct_with_tuple_t_component_equality : thm
    val struct_with_tuple_t_fn_updates : thm
    val struct_with_tuple_t_fupdfupds : thm
    val struct_with_tuple_t_fupdfupds_comp : thm
    val struct_with_tuple_t_induction : thm
    val struct_with_tuple_t_literal_11 : thm
    val struct_with_tuple_t_literal_nchotomy : thm
    val struct_with_tuple_t_nchotomy : thm
    val struct_with_tuple_t_updates_eq_literal : thm
    val sum_t_11 : thm
    val sum_t_Axiom : thm
    val sum_t_case_cong : thm
    val sum_t_case_eq : thm
    val sum_t_distinct : thm
    val sum_t_induction : thm
    val sum_t_nchotomy : thm
    val tree_t_11 : thm
    val tree_t_Axiom : thm
    val tree_t_case_cong : thm
    val tree_t_case_eq : thm
    val tree_t_distinct : thm
    val tree_t_induction : thm
    val tree_t_nchotomy : thm
  
  val noNestedBorrows_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [divDef] Parent theory of "noNestedBorrows"
   
   [add_test_fwd_def]  Definition
      
      ⊢ ∀x y. add_test_fwd x y = u32_add x y
   
   [cast_test_fwd_def]  Definition
      
      ⊢ ∀x. cast_test_fwd x = mk_i32 (u32_to_int x)
   
   [choose_back_def]  Definition
      
      ⊢ ∀b x y ret.
          choose_back b x y ret =
          if b then Return (ret,y) else Return (x,ret)
   
   [choose_fwd_def]  Definition
      
      ⊢ ∀b x y. choose_fwd b x y = if b then Return x else Return y
   
   [choose_test_fwd_def]  Definition
      
      ⊢ choose_test_fwd =
        do
          z <- choose_fwd T (int_to_i32 0) (int_to_i32 0);
          z0 <- i32_add z (int_to_i32 1);
          if z0 ≠ int_to_i32 1 then Fail Failure
          else
            do
              (x,y) <- choose_back T (int_to_i32 0) (int_to_i32 0) z0;
              if x ≠ int_to_i32 1 then Fail Failure
              else if y ≠ int_to_i32 0 then Fail Failure
              else Return ()
            od
        od
   
   [copy_int_fwd_def]  Definition
      
      ⊢ ∀x. copy_int_fwd x = Return x
   
   [div_test1_fwd_def]  Definition
      
      ⊢ ∀x. div_test1_fwd x = u32_div x (int_to_u32 2)
   
   [div_test_fwd_def]  Definition
      
      ⊢ ∀x y. div_test_fwd x y = u32_div x y
   
   [empty_enum_t_BIJ]  Definition
      
      ⊢ (∀a. num2empty_enum_t (empty_enum_t2num a) = a) ∧
        ∀r. (λn. n < 1) r ⇔ empty_enum_t2num (num2empty_enum_t r) = r
   
   [empty_enum_t_CASE]  Definition
      
      ⊢ ∀x v0.
          (case x of EmptyEnumEmpty => v0) = (λm. v0) (empty_enum_t2num x)
   
   [empty_enum_t_TY_DEF]  Definition
      
      ⊢ ∃rep. TYPE_DEFINITION (λn. n < 1) rep
   
   [empty_enum_t_size_def]  Definition
      
      ⊢ ∀x. empty_enum_t_size x = 0
   
   [enum_t_BIJ]  Definition
      
      ⊢ (∀a. num2enum_t (enum_t2num a) = a) ∧
        ∀r. (λn. n < 2) r ⇔ enum_t2num (num2enum_t r) = r
   
   [enum_t_CASE]  Definition
      
      ⊢ ∀x v0 v1.
          (case x of EnumVariant1 => v0 | EnumVariant2 => v1) =
          (λm. if m = 0 then v0 else v1) (enum_t2num x)
   
   [enum_t_TY_DEF]  Definition
      
      ⊢ ∃rep. TYPE_DEFINITION (λn. n < 2) rep
   
   [enum_t_size_def]  Definition
      
      ⊢ ∀x. enum_t_size x = 0
   
   [get_max_fwd_def]  Definition
      
      ⊢ ∀x y. get_max_fwd x y = if u32_ge x y then Return x else Return y
   
   [id_mut_pair1_back_def]  Definition
      
      ⊢ ∀x y ret.
          id_mut_pair1_back x y ret = (let (t,t0) = ret in Return (t,t0))
   
   [id_mut_pair1_fwd_def]  Definition
      
      ⊢ ∀x y. id_mut_pair1_fwd x y = Return (x,y)
   
   [id_mut_pair2_back_def]  Definition
      
      ⊢ ∀p ret.
          id_mut_pair2_back p ret = (let (t,t0) = ret in Return (t,t0))
   
   [id_mut_pair2_fwd_def]  Definition
      
      ⊢ ∀p. id_mut_pair2_fwd p = (let (t,t0) = p in Return (t,t0))
   
   [id_mut_pair3_back'a_def]  Definition
      
      ⊢ ∀x y ret. id_mut_pair3_back'a x y ret = Return ret
   
   [id_mut_pair3_back'b_def]  Definition
      
      ⊢ ∀x y ret. id_mut_pair3_back'b x y ret = Return ret
   
   [id_mut_pair3_fwd_def]  Definition
      
      ⊢ ∀x y. id_mut_pair3_fwd x y = Return (x,y)
   
   [id_mut_pair4_back'a_def]  Definition
      
      ⊢ ∀p ret. id_mut_pair4_back'a p ret = Return ret
   
   [id_mut_pair4_back'b_def]  Definition
      
      ⊢ ∀p ret. id_mut_pair4_back'b p ret = Return ret
   
   [id_mut_pair4_fwd_def]  Definition
      
      ⊢ ∀p. id_mut_pair4_fwd p = (let (t,t0) = p in Return (t,t0))
   
   [is_cons_fwd_def]  Definition
      
      ⊢ ∀l. is_cons_fwd l =
            case l of ListCons t l0 => Return T | ListNil => Return F
   
   [list_length_fwd_def]  Definition
      
      ⊢ ∀l. list_length_fwd l =
            case l of
              ListCons t l1 =>
                do i <- list_length_fwd l1; u32_add (int_to_u32 1) i od
            | ListNil => Return (int_to_u32 0)
   
   [list_nth_mut_back_def]  Definition
      
      ⊢ ∀l i ret.
          list_nth_mut_back l i ret =
          case l of
            ListCons x tl =>
              if i = int_to_u32 0 then Return (ListCons ret tl)
              else
                do
                  i0 <- u32_sub i (int_to_u32 1);
                  tl0 <- list_nth_mut_back tl i0 ret;
                  Return (ListCons x tl0)
                od
          | ListNil => Fail Failure
   
   [list_nth_mut_fwd_def]  Definition
      
      ⊢ ∀l i.
          list_nth_mut_fwd l i =
          case l of
            ListCons x tl =>
              if i = int_to_u32 0 then Return x
              else
                do
                  i0 <- u32_sub i (int_to_u32 1);
                  list_nth_mut_fwd tl i0
                od
          | ListNil => Fail Failure
   
   [list_nth_shared_fwd_def]  Definition
      
      ⊢ ∀l i.
          list_nth_shared_fwd l i =
          case l of
            ListCons x tl =>
              if i = int_to_u32 0 then Return x
              else
                do
                  i0 <- u32_sub i (int_to_u32 1);
                  list_nth_shared_fwd tl i0
                od
          | ListNil => Fail Failure
   
   [list_rev_aux_fwd_def]  Definition
      
      ⊢ ∀li lo.
          list_rev_aux_fwd li lo =
          case li of
            ListCons hd tl => list_rev_aux_fwd tl (ListCons hd lo)
          | ListNil => Return lo
   
   [list_rev_fwd_back_def]  Definition
      
      ⊢ ∀l. list_rev_fwd_back l =
            (let
               li = mem_replace_fwd l ListNil
             in
               list_rev_aux_fwd li ListNil)
   
   [list_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('list_t').
                   (∀a0'.
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR 0 a0
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))
                           a0 a1 ∧ $var$('list_t') a1) ∨
                      a0' =
                      ind_type$CONSTR (SUC 0) ARB (λn. ind_type$BOTTOM) ⇒
                      $var$('list_t') a0') ⇒
                   $var$('list_t') a0') rep
   
   [list_t_case_def]  Definition
      
      ⊢ (∀a0 a1 f v. list_t_CASE (ListCons a0 a1) f v = f a0 a1) ∧
        ∀f v. list_t_CASE ListNil f v = v
   
   [list_t_size_def]  Definition
      
      ⊢ (∀f a0 a1.
           list_t_size f (ListCons a0 a1) = 1 + (f a0 + list_t_size f a1)) ∧
        ∀f. list_t_size f ListNil = 0
   
   [neg_test_fwd_def]  Definition
      
      ⊢ ∀x. neg_test_fwd x = i32_neg x
   
   [new_pair1_fwd_def]  Definition
      
      ⊢ new_pair1_fwd =
        Return
          <|struct_with_pair_p :=
              <|pair_x := int_to_u32 1; pair_y := int_to_u32 2|> |>
   
   [new_tuple1_fwd_def]  Definition
      
      ⊢ new_tuple1_fwd =
        Return <|struct_with_tuple_p := (int_to_u32 1,int_to_u32 2)|>
   
   [new_tuple2_fwd_def]  Definition
      
      ⊢ new_tuple2_fwd =
        Return <|struct_with_tuple_p := (int_to_i16 1,int_to_i16 2)|>
   
   [new_tuple3_fwd_def]  Definition
      
      ⊢ new_tuple3_fwd =
        Return <|struct_with_tuple_p := (int_to_u64 1,int_to_i64 2)|>
   
   [node_elem_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa1'.
                 ∀ $var$('tree_t') $var$('node_elem_t').
                   (∀a0'.
                      (∃a. a0' =
                           (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                             a) ∨
                      (∃a0 a1 a2.
                         a0' =
                         (λa0 a1 a2.
                              ind_type$CONSTR (SUC 0) a0
                                (ind_type$FCONS a1
                                   (ind_type$FCONS a2 (λn. ind_type$BOTTOM))))
                           a0 a1 a2 ∧ $var$('node_elem_t') a1 ∧
                         $var$('tree_t') a2) ⇒
                      $var$('tree_t') a0') ∧
                   (∀a1'.
                      (∃a0 a1.
                         a1' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC 0)) ARB
                                (ind_type$FCONS a0
                                   (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                           a0 a1 ∧ $var$('tree_t') a0 ∧
                         $var$('node_elem_t') a1) ∨
                      a1' =
                      ind_type$CONSTR (SUC (SUC (SUC 0))) ARB
                        (λn. ind_type$BOTTOM) ⇒
                      $var$('node_elem_t') a1') ⇒
                   $var$('node_elem_t') a1') rep
   
   [node_elem_t_case_def]  Definition
      
      ⊢ (∀a0 a1 f v. node_elem_t_CASE (NodeElemCons a0 a1) f v = f a0 a1) ∧
        ∀f v. node_elem_t_CASE NodeElemNil f v = v
   
   [one_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0.
                 ∀ $var$('one_t').
                   (∀a0.
                      (∃a. a0 =
                           (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                             a) ⇒
                      $var$('one_t') a0) ⇒
                   $var$('one_t') a0) rep
   
   [one_t_case_def]  Definition
      
      ⊢ ∀a f. one_t_CASE (OneOne a) f = f a
   
   [one_t_size_def]  Definition
      
      ⊢ ∀f a. one_t_size f (OneOne a) = 1 + f a
   
   [pair_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('pair_t').
                   (∀a0'.
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR 0 (a0,a1)
                                (λn. ind_type$BOTTOM)) a0 a1) ⇒
                      $var$('pair_t') a0') ⇒
                   $var$('pair_t') a0') rep
   
   [pair_t_case_def]  Definition
      
      ⊢ ∀a0 a1 f. pair_t_CASE (pair_t a0 a1) f = f a0 a1
   
   [pair_t_pair_x]  Definition
      
      ⊢ ∀t t0. (pair_t t t0).pair_x = t
   
   [pair_t_pair_x_fupd]  Definition
      
      ⊢ ∀f t t0. pair_t t t0 with pair_x updated_by f = pair_t (f t) t0
   
   [pair_t_pair_y]  Definition
      
      ⊢ ∀t t0. (pair_t t t0).pair_y = t0
   
   [pair_t_pair_y_fupd]  Definition
      
      ⊢ ∀f t t0. pair_t t t0 with pair_y updated_by f = pair_t t (f t0)
   
   [pair_t_size_def]  Definition
      
      ⊢ ∀f f1 a0 a1. pair_t_size f f1 (pair_t a0 a1) = 1 + (f a0 + f1 a1)
   
   [refs_test1_fwd_def]  Definition
      
      ⊢ refs_test1_fwd =
        if int_to_i32 1 ≠ int_to_i32 1 then Fail Failure else Return ()
   
   [refs_test2_fwd_def]  Definition
      
      ⊢ refs_test2_fwd =
        if int_to_i32 2 ≠ int_to_i32 2 then Fail Failure
        else if int_to_i32 0 ≠ int_to_i32 0 then Fail Failure
        else if int_to_i32 2 ≠ int_to_i32 2 then Fail Failure
        else if int_to_i32 2 ≠ int_to_i32 2 then Fail Failure
        else Return ()
   
   [rem_test_fwd_def]  Definition
      
      ⊢ ∀x y. rem_test_fwd x y = u32_rem x y
   
   [split_list_fwd_def]  Definition
      
      ⊢ ∀l. split_list_fwd l =
            case l of
              ListCons hd tl => Return (hd,tl)
            | ListNil => Fail Failure
   
   [struct_with_pair_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0.
                 ∀ $var$('struct_with_pair_t').
                   (∀a0.
                      (∃a. a0 =
                           (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                             a) ⇒
                      $var$('struct_with_pair_t') a0) ⇒
                   $var$('struct_with_pair_t') a0) rep
   
   [struct_with_pair_t_case_def]  Definition
      
      ⊢ ∀a f. struct_with_pair_t_CASE (struct_with_pair_t a) f = f a
   
   [struct_with_pair_t_size_def]  Definition
      
      ⊢ ∀f f1 a.
          struct_with_pair_t_size f f1 (struct_with_pair_t a) =
          1 + pair_t_size f f1 a
   
   [struct_with_pair_t_struct_with_pair_p]  Definition
      
      ⊢ ∀p. (struct_with_pair_t p).struct_with_pair_p = p
   
   [struct_with_pair_t_struct_with_pair_p_fupd]  Definition
      
      ⊢ ∀f p.
          struct_with_pair_t p with struct_with_pair_p updated_by f =
          struct_with_pair_t (f p)
   
   [struct_with_tuple_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0.
                 ∀ $var$('struct_with_tuple_t').
                   (∀a0.
                      (∃a. a0 =
                           (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                             a) ⇒
                      $var$('struct_with_tuple_t') a0) ⇒
                   $var$('struct_with_tuple_t') a0) rep
   
   [struct_with_tuple_t_case_def]  Definition
      
      ⊢ ∀a f. struct_with_tuple_t_CASE (struct_with_tuple_t a) f = f a
   
   [struct_with_tuple_t_size_def]  Definition
      
      ⊢ ∀f f1 a.
          struct_with_tuple_t_size f f1 (struct_with_tuple_t a) =
          1 + pair_size f f1 a
   
   [struct_with_tuple_t_struct_with_tuple_p]  Definition
      
      ⊢ ∀p. (struct_with_tuple_t p).struct_with_tuple_p = p
   
   [struct_with_tuple_t_struct_with_tuple_p_fupd]  Definition
      
      ⊢ ∀f p.
          struct_with_tuple_t p with struct_with_tuple_p updated_by f =
          struct_with_tuple_t (f p)
   
   [subs_test_fwd_def]  Definition
      
      ⊢ ∀x y. subs_test_fwd x y = u32_sub x y
   
   [sum_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0.
                 ∀ $var$('sum_t').
                   (∀a0.
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR 0 (a,ARB)
                                  (λn. ind_type$BOTTOM)) a) ∨
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR (SUC 0) (ARB,a)
                                  (λn. ind_type$BOTTOM)) a) ⇒
                      $var$('sum_t') a0) ⇒
                   $var$('sum_t') a0) rep
   
   [sum_t_case_def]  Definition
      
      ⊢ (∀a f f1. sum_t_CASE (SumLeft a) f f1 = f a) ∧
        ∀a f f1. sum_t_CASE (SumRight a) f f1 = f1 a
   
   [sum_t_size_def]  Definition
      
      ⊢ (∀f f1 a. sum_t_size f f1 (SumLeft a) = 1 + f a) ∧
        ∀f f1 a. sum_t_size f f1 (SumRight a) = 1 + f1 a
   
   [test2_fwd_def]  Definition
      
      ⊢ test2_fwd =
        monad_ignore_bind (u32_add (int_to_u32 23) (int_to_u32 44))
          (Return ())
   
   [test3_fwd_def]  Definition
      
      ⊢ test3_fwd =
        do
          x <- get_max_fwd (int_to_u32 4) (int_to_u32 3);
          y <- get_max_fwd (int_to_u32 10) (int_to_u32 11);
          z <- u32_add x y;
          if z ≠ int_to_u32 15 then Fail Failure else Return ()
        od
   
   [test_box1_fwd_def]  Definition
      
      ⊢ test_box1_fwd =
        (let
           b = int_to_i32 1;
           x = b
         in
           if x ≠ int_to_i32 1 then Fail Failure else Return ())
   
   [test_char_fwd_def]  Definition
      
      ⊢ test_char_fwd = Return #"a"
   
   [test_constants_fwd_def]  Definition
      
      ⊢ test_constants_fwd =
        do
          swt <- new_tuple1_fwd;
          (i,_) <<- swt.struct_with_tuple_p;
          if i ≠ int_to_u32 1 then Fail Failure
          else
            do
              swt0 <- new_tuple2_fwd;
              (i0,_) <<- swt0.struct_with_tuple_p;
              if i0 ≠ int_to_i16 1 then Fail Failure
              else
                do
                  swt1 <- new_tuple3_fwd;
                  (i1,_) <<- swt1.struct_with_tuple_p;
                  if i1 ≠ int_to_u64 1 then Fail Failure
                  else
                    do
                      swp <- new_pair1_fwd;
                      if swp.struct_with_pair_p.pair_x ≠ int_to_u32 1 then
                        Fail Failure
                      else Return ()
                    od
                od
            od
        od
   
   [test_copy_int_fwd_def]  Definition
      
      ⊢ test_copy_int_fwd =
        do
          y <- copy_int_fwd (int_to_i32 0);
          if int_to_i32 0 ≠ y then Fail Failure else Return ()
        od
   
   [test_is_cons_fwd_def]  Definition
      
      ⊢ test_is_cons_fwd =
        (let
           l = ListNil
         in
           do
             b <- is_cons_fwd (ListCons (int_to_i32 0) l);
             if ¬b then Fail Failure else Return ()
           od)
   
   [test_list1_fwd_def]  Definition
      
      ⊢ test_list1_fwd = Return ()
   
   [test_list_functions_fwd_def]  Definition
      
      ⊢ test_list_functions_fwd =
        (let
           l = ListNil;
           l0 = ListCons (int_to_i32 2) l;
           l1 = ListCons (int_to_i32 1) l0
         in
           do
             i <- list_length_fwd (ListCons (int_to_i32 0) l1);
             if i ≠ int_to_u32 3 then Fail Failure
             else
               do
                 i0 <-
                   list_nth_shared_fwd (ListCons (int_to_i32 0) l1)
                     (int_to_u32 0);
                 if i0 ≠ int_to_i32 0 then Fail Failure
                 else
                   do
                     i1 <-
                       list_nth_shared_fwd (ListCons (int_to_i32 0) l1)
                         (int_to_u32 1);
                     if i1 ≠ int_to_i32 1 then Fail Failure
                     else
                       do
                         i2 <-
                           list_nth_shared_fwd (ListCons (int_to_i32 0) l1)
                             (int_to_u32 2);
                         if i2 ≠ int_to_i32 2 then Fail Failure
                         else
                           do
                             ls <-
                               list_nth_mut_back
                                 (ListCons (int_to_i32 0) l1)
                                 (int_to_u32 1) (int_to_i32 3);
                             i3 <- list_nth_shared_fwd ls (int_to_u32 0);
                             if i3 ≠ int_to_i32 0 then Fail Failure
                             else
                               do
                                 i4 <-
                                   list_nth_shared_fwd ls (int_to_u32 1);
                                 if i4 ≠ int_to_i32 3 then Fail Failure
                                 else
                                   do
                                     i5 <-
                                       list_nth_shared_fwd ls
                                         (int_to_u32 2);
                                     if i5 ≠ int_to_i32 2 then Fail Failure
                                     else Return ()
                                   od
                               od
                           od
                       od
                   od
               od
           od)
   
   [test_mem_replace_fwd_back_def]  Definition
      
      ⊢ ∀px.
          test_mem_replace_fwd_back px =
          (let
             y = mem_replace_fwd px (int_to_u32 1)
           in
             if y ≠ int_to_u32 0 then Fail Failure
             else Return (int_to_u32 2))
   
   [test_neg1_fwd_def]  Definition
      
      ⊢ test_neg1_fwd =
        do
          y <- i32_neg (int_to_i32 3);
          if y ≠ int_to_i32 (-3) then Fail Failure else Return ()
        od
   
   [test_panic_fwd_def]  Definition
      
      ⊢ ∀b. test_panic_fwd b = if b then Fail Failure else Return ()
   
   [test_shared_borrow_bool1_fwd_def]  Definition
      
      ⊢ ∀b. test_shared_borrow_bool1_fwd b =
            if b then Return (int_to_u32 0) else Return (int_to_u32 1)
   
   [test_shared_borrow_bool2_fwd_def]  Definition
      
      ⊢ test_shared_borrow_bool2_fwd = Return (int_to_u32 0)
   
   [test_shared_borrow_enum1_fwd_def]  Definition
      
      ⊢ ∀l. test_shared_borrow_enum1_fwd l =
            case l of
              ListCons i l0 => Return (int_to_u32 1)
            | ListNil => Return (int_to_u32 0)
   
   [test_shared_borrow_enum2_fwd_def]  Definition
      
      ⊢ test_shared_borrow_enum2_fwd = Return (int_to_u32 0)
   
   [test_split_list_fwd_def]  Definition
      
      ⊢ test_split_list_fwd =
        (let
           l = ListNil
         in
           do
             p <- split_list_fwd (ListCons (int_to_i32 0) l);
             (hd,_) <<- p;
             if hd ≠ int_to_i32 0 then Fail Failure else Return ()
           od)
   
   [test_unreachable_fwd_def]  Definition
      
      ⊢ ∀b. test_unreachable_fwd b = if b then Fail Failure else Return ()
   
   [test_weird_borrows1_fwd_def]  Definition
      
      ⊢ test_weird_borrows1_fwd = Return ()
   
   [tree_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('tree_t') $var$('node_elem_t').
                   (∀a0'.
                      (∃a. a0' =
                           (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                             a) ∨
                      (∃a0 a1 a2.
                         a0' =
                         (λa0 a1 a2.
                              ind_type$CONSTR (SUC 0) a0
                                (ind_type$FCONS a1
                                   (ind_type$FCONS a2 (λn. ind_type$BOTTOM))))
                           a0 a1 a2 ∧ $var$('node_elem_t') a1 ∧
                         $var$('tree_t') a2) ⇒
                      $var$('tree_t') a0') ∧
                   (∀a1'.
                      (∃a0 a1.
                         a1' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC 0)) ARB
                                (ind_type$FCONS a0
                                   (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                           a0 a1 ∧ $var$('tree_t') a0 ∧
                         $var$('node_elem_t') a1) ∨
                      a1' =
                      ind_type$CONSTR (SUC (SUC (SUC 0))) ARB
                        (λn. ind_type$BOTTOM) ⇒
                      $var$('node_elem_t') a1') ⇒
                   $var$('tree_t') a0') rep
   
   [tree_t_case_def]  Definition
      
      ⊢ (∀a f f1. tree_t_CASE (TreeLeaf a) f f1 = f a) ∧
        ∀a0 a1 a2 f f1. tree_t_CASE (TreeNode a0 a1 a2) f f1 = f1 a0 a1 a2
   
   [tree_t_size_def]  Definition
      
      ⊢ (∀f a. tree_t_size f (TreeLeaf a) = 1 + f a) ∧
        (∀f a0 a1 a2.
           tree_t_size f (TreeNode a0 a1 a2) =
           1 + (f a0 + (node_elem_t_size f a1 + tree_t_size f a2))) ∧
        (∀f a0 a1.
           node_elem_t_size f (NodeElemCons a0 a1) =
           1 + (tree_t_size f a0 + node_elem_t_size f a1)) ∧
        ∀f. node_elem_t_size f NodeElemNil = 0
   
   [EXISTS_pair_t]  Theorem
      
      ⊢ ∀P. (∃p. P p) ⇔ ∃t0 t. P <|pair_x := t0; pair_y := t|>
   
   [EXISTS_struct_with_pair_t]  Theorem
      
      ⊢ ∀P. (∃s. P s) ⇔ ∃p. P <|struct_with_pair_p := p|>
   
   [EXISTS_struct_with_tuple_t]  Theorem
      
      ⊢ ∀P. (∃s. P s) ⇔ ∃p. P <|struct_with_tuple_p := p|>
   
   [FORALL_pair_t]  Theorem
      
      ⊢ ∀P. (∀p. P p) ⇔ ∀t0 t. P <|pair_x := t0; pair_y := t|>
   
   [FORALL_struct_with_pair_t]  Theorem
      
      ⊢ ∀P. (∀s. P s) ⇔ ∀p. P <|struct_with_pair_p := p|>
   
   [FORALL_struct_with_tuple_t]  Theorem
      
      ⊢ ∀P. (∀s. P s) ⇔ ∀p. P <|struct_with_tuple_p := p|>
   
   [datatype_empty_enum_t]  Theorem
      
      ⊢ DATATYPE (empty_enum_t EmptyEnumEmpty)
   
   [datatype_enum_t]  Theorem
      
      ⊢ DATATYPE (enum_t EnumVariant1 EnumVariant2)
   
   [datatype_list_t]  Theorem
      
      ⊢ DATATYPE (list_t ListCons ListNil)
   
   [datatype_one_t]  Theorem
      
      ⊢ DATATYPE (one_t OneOne)
   
   [datatype_pair_t]  Theorem
      
      ⊢ DATATYPE (record pair_t pair_x pair_y)
   
   [datatype_struct_with_pair_t]  Theorem
      
      ⊢ DATATYPE (record struct_with_pair_t struct_with_pair_p)
   
   [datatype_struct_with_tuple_t]  Theorem
      
      ⊢ DATATYPE (record struct_with_tuple_t struct_with_tuple_p)
   
   [datatype_sum_t]  Theorem
      
      ⊢ DATATYPE (sum_t SumLeft SumRight)
   
   [datatype_tree_t]  Theorem
      
      ⊢ DATATYPE
          (tree_t TreeLeaf TreeNode ∧ node_elem_t NodeElemCons NodeElemNil)
   
   [empty_enum_t2num_11]  Theorem
      
      ⊢ ∀a a'. empty_enum_t2num a = empty_enum_t2num a' ⇔ a = a'
   
   [empty_enum_t2num_ONTO]  Theorem
      
      ⊢ ∀r. r < 1 ⇔ ∃a. r = empty_enum_t2num a
   
   [empty_enum_t2num_num2empty_enum_t]  Theorem
      
      ⊢ ∀r. r < 1 ⇔ empty_enum_t2num (num2empty_enum_t r) = r
   
   [empty_enum_t2num_thm]  Theorem
      
      ⊢ empty_enum_t2num EmptyEnumEmpty = 0
   
   [empty_enum_t_Axiom]  Theorem
      
      ⊢ ∀x0. ∃f. f EmptyEnumEmpty = x0
   
   [empty_enum_t_EQ_empty_enum_t]  Theorem
      
      ⊢ ∀a a'. a = a' ⇔ empty_enum_t2num a = empty_enum_t2num a'
   
   [empty_enum_t_case_cong]  Theorem
      
      ⊢ ∀M M' v0.
          M = M' ∧ (M' = EmptyEnumEmpty ⇒ v0 = v0') ⇒
          (case M of EmptyEnumEmpty => v0) =
          case M' of EmptyEnumEmpty => v0'
   
   [empty_enum_t_case_def]  Theorem
      
      ⊢ ∀v0. (case EmptyEnumEmpty of EmptyEnumEmpty => v0) = v0
   
   [empty_enum_t_case_eq]  Theorem
      
      ⊢ (case x of EmptyEnumEmpty => v0) = v ⇔ x = EmptyEnumEmpty ∧ v0 = v
   
   [empty_enum_t_induction]  Theorem
      
      ⊢ ∀P. P EmptyEnumEmpty ⇒ ∀a. P a
   
   [empty_enum_t_nchotomy]  Theorem
      
      ⊢ ∀a. a = EmptyEnumEmpty
   
   [enum_t2num_11]  Theorem
      
      ⊢ ∀a a'. enum_t2num a = enum_t2num a' ⇔ a = a'
   
   [enum_t2num_ONTO]  Theorem
      
      ⊢ ∀r. r < 2 ⇔ ∃a. r = enum_t2num a
   
   [enum_t2num_num2enum_t]  Theorem
      
      ⊢ ∀r. r < 2 ⇔ enum_t2num (num2enum_t r) = r
   
   [enum_t2num_thm]  Theorem
      
      ⊢ enum_t2num EnumVariant1 = 0 ∧ enum_t2num EnumVariant2 = 1
   
   [enum_t_Axiom]  Theorem
      
      ⊢ ∀x0 x1. ∃f. f EnumVariant1 = x0 ∧ f EnumVariant2 = x1
   
   [enum_t_EQ_enum_t]  Theorem
      
      ⊢ ∀a a'. a = a' ⇔ enum_t2num a = enum_t2num a'
   
   [enum_t_case_cong]  Theorem
      
      ⊢ ∀M M' v0 v1.
          M = M' ∧ (M' = EnumVariant1 ⇒ v0 = v0') ∧
          (M' = EnumVariant2 ⇒ v1 = v1') ⇒
          (case M of EnumVariant1 => v0 | EnumVariant2 => v1) =
          case M' of EnumVariant1 => v0' | EnumVariant2 => v1'
   
   [enum_t_case_def]  Theorem
      
      ⊢ (∀v0 v1.
           (case EnumVariant1 of EnumVariant1 => v0 | EnumVariant2 => v1) =
           v0) ∧
        ∀v0 v1.
          (case EnumVariant2 of EnumVariant1 => v0 | EnumVariant2 => v1) =
          v1
   
   [enum_t_case_eq]  Theorem
      
      ⊢ (case x of EnumVariant1 => v0 | EnumVariant2 => v1) = v ⇔
        x = EnumVariant1 ∧ v0 = v ∨ x = EnumVariant2 ∧ v1 = v
   
   [enum_t_distinct]  Theorem
      
      ⊢ EnumVariant1 ≠ EnumVariant2
   
   [enum_t_induction]  Theorem
      
      ⊢ ∀P. P EnumVariant1 ∧ P EnumVariant2 ⇒ ∀a. P a
   
   [enum_t_nchotomy]  Theorem
      
      ⊢ ∀a. a = EnumVariant1 ∨ a = EnumVariant2
   
   [list_t_11]  Theorem
      
      ⊢ ∀a0 a1 a0' a1'.
          ListCons a0 a1 = ListCons a0' a1' ⇔ a0 = a0' ∧ a1 = a1'
   
   [list_t_Axiom]  Theorem
      
      ⊢ ∀f0 f1. ∃fn.
          (∀a0 a1. fn (ListCons a0 a1) = f0 a0 a1 (fn a1)) ∧
          fn ListNil = f1
   
   [list_t_case_cong]  Theorem
      
      ⊢ ∀M M' f v.
          M = M' ∧ (∀a0 a1. M' = ListCons a0 a1 ⇒ f a0 a1 = f' a0 a1) ∧
          (M' = ListNil ⇒ v = v') ⇒
          list_t_CASE M f v = list_t_CASE M' f' v'
   
   [list_t_case_eq]  Theorem
      
      ⊢ list_t_CASE x f v = v' ⇔
        (∃t l. x = ListCons t l ∧ f t l = v') ∨ x = ListNil ∧ v = v'
   
   [list_t_distinct]  Theorem
      
      ⊢ ∀a1 a0. ListCons a0 a1 ≠ ListNil
   
   [list_t_induction]  Theorem
      
      ⊢ ∀P. (∀l. P l ⇒ ∀t. P (ListCons t l)) ∧ P ListNil ⇒ ∀l. P l
   
   [list_t_nchotomy]  Theorem
      
      ⊢ ∀ll. (∃t l. ll = ListCons t l) ∨ ll = ListNil
   
   [node_elem_t_11]  Theorem
      
      ⊢ ∀a0 a1 a0' a1'.
          NodeElemCons a0 a1 = NodeElemCons a0' a1' ⇔ a0 = a0' ∧ a1 = a1'
   
   [node_elem_t_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3. ∃fn0 fn1.
          (∀a. fn0 (TreeLeaf a) = f0 a) ∧
          (∀a0 a1 a2.
             fn0 (TreeNode a0 a1 a2) = f1 a0 a1 a2 (fn1 a1) (fn0 a2)) ∧
          (∀a0 a1. fn1 (NodeElemCons a0 a1) = f2 a0 a1 (fn0 a0) (fn1 a1)) ∧
          fn1 NodeElemNil = f3
   
   [node_elem_t_case_cong]  Theorem
      
      ⊢ ∀M M' f v.
          M = M' ∧ (∀a0 a1. M' = NodeElemCons a0 a1 ⇒ f a0 a1 = f' a0 a1) ∧
          (M' = NodeElemNil ⇒ v = v') ⇒
          node_elem_t_CASE M f v = node_elem_t_CASE M' f' v'
   
   [node_elem_t_case_eq]  Theorem
      
      ⊢ node_elem_t_CASE x f v = v' ⇔
        (∃t n. x = NodeElemCons t n ∧ f t n = v') ∨
        x = NodeElemNil ∧ v = v'
   
   [node_elem_t_distinct]  Theorem
      
      ⊢ ∀a1 a0. NodeElemCons a0 a1 ≠ NodeElemNil
   
   [node_elem_t_induction]  Theorem
      
      ⊢ ∀P0 P1.
          (∀t. P0 (TreeLeaf t)) ∧
          (∀n t. P1 n ∧ P0 t ⇒ ∀t0. P0 (TreeNode t0 n t)) ∧
          (∀t n. P0 t ∧ P1 n ⇒ P1 (NodeElemCons t n)) ∧ P1 NodeElemNil ⇒
          (∀t. P0 t) ∧ ∀n. P1 n
   
   [node_elem_t_nchotomy]  Theorem
      
      ⊢ ∀nn. (∃t n. nn = NodeElemCons t n) ∨ nn = NodeElemNil
   
   [num2empty_enum_t_11]  Theorem
      
      ⊢ ∀r r'.
          r < 1 ⇒
          r' < 1 ⇒
          (num2empty_enum_t r = num2empty_enum_t r' ⇔ r = r')
   
   [num2empty_enum_t_ONTO]  Theorem
      
      ⊢ ∀a. ∃r. a = num2empty_enum_t r ∧ r < 1
   
   [num2empty_enum_t_empty_enum_t2num]  Theorem
      
      ⊢ ∀a. num2empty_enum_t (empty_enum_t2num a) = a
   
   [num2empty_enum_t_thm]  Theorem
      
      ⊢ num2empty_enum_t 0 = EmptyEnumEmpty
   
   [num2enum_t_11]  Theorem
      
      ⊢ ∀r r'. r < 2 ⇒ r' < 2 ⇒ (num2enum_t r = num2enum_t r' ⇔ r = r')
   
   [num2enum_t_ONTO]  Theorem
      
      ⊢ ∀a. ∃r. a = num2enum_t r ∧ r < 2
   
   [num2enum_t_enum_t2num]  Theorem
      
      ⊢ ∀a. num2enum_t (enum_t2num a) = a
   
   [num2enum_t_thm]  Theorem
      
      ⊢ num2enum_t 0 = EnumVariant1 ∧ num2enum_t 1 = EnumVariant2
   
   [one_t_11]  Theorem
      
      ⊢ ∀a a'. OneOne a = OneOne a' ⇔ a = a'
   
   [one_t_Axiom]  Theorem
      
      ⊢ ∀f. ∃fn. ∀a. fn (OneOne a) = f a
   
   [one_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧ (∀a. M' = OneOne a ⇒ f a = f' a) ⇒
          one_t_CASE M f = one_t_CASE M' f'
   
   [one_t_case_eq]  Theorem
      
      ⊢ one_t_CASE x f = v ⇔ ∃t. x = OneOne t ∧ f t = v
   
   [one_t_induction]  Theorem
      
      ⊢ ∀P. (∀t. P (OneOne t)) ⇒ ∀ $o. P $o
   
   [one_t_nchotomy]  Theorem
      
      ⊢ ∀oo. ∃t. oo = OneOne t
   
   [pair_t_11]  Theorem
      
      ⊢ ∀a0 a1 a0' a1'. pair_t a0 a1 = pair_t a0' a1' ⇔ a0 = a0' ∧ a1 = a1'
   
   [pair_t_Axiom]  Theorem
      
      ⊢ ∀f. ∃fn. ∀a0 a1. fn (pair_t a0 a1) = f a0 a1
   
   [pair_t_accessors]  Theorem
      
      ⊢ (∀t t0. (pair_t t t0).pair_x = t) ∧
        ∀t t0. (pair_t t t0).pair_y = t0
   
   [pair_t_accfupds]  Theorem
      
      ⊢ (∀p f. (p with pair_y updated_by f).pair_x = p.pair_x) ∧
        (∀p f. (p with pair_x updated_by f).pair_y = p.pair_y) ∧
        (∀p f. (p with pair_x updated_by f).pair_x = f p.pair_x) ∧
        ∀p f. (p with pair_y updated_by f).pair_y = f p.pair_y
   
   [pair_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧ (∀a0 a1. M' = pair_t a0 a1 ⇒ f a0 a1 = f' a0 a1) ⇒
          pair_t_CASE M f = pair_t_CASE M' f'
   
   [pair_t_case_eq]  Theorem
      
      ⊢ pair_t_CASE x f = v ⇔ ∃t t0. x = pair_t t t0 ∧ f t t0 = v
   
   [pair_t_component_equality]  Theorem
      
      ⊢ ∀p1 p2. p1 = p2 ⇔ p1.pair_x = p2.pair_x ∧ p1.pair_y = p2.pair_y
   
   [pair_t_fn_updates]  Theorem
      
      ⊢ (∀f t t0. pair_t t t0 with pair_x updated_by f = pair_t (f t) t0) ∧
        ∀f t t0. pair_t t t0 with pair_y updated_by f = pair_t t (f t0)
   
   [pair_t_fupdcanon]  Theorem
      
      ⊢ ∀p g f.
          p with <|pair_y updated_by f; pair_x updated_by g|> =
          p with <|pair_x updated_by g; pair_y updated_by f|>
   
   [pair_t_fupdcanon_comp]  Theorem
      
      ⊢ (∀g f.
           pair_y_fupd f ∘ pair_x_fupd g = pair_x_fupd g ∘ pair_y_fupd f) ∧
        ∀h g f.
          pair_y_fupd f ∘ pair_x_fupd g ∘ h =
          pair_x_fupd g ∘ pair_y_fupd f ∘ h
   
   [pair_t_fupdfupds]  Theorem
      
      ⊢ (∀p g f.
           p with <|pair_x updated_by f; pair_x updated_by g|> =
           p with pair_x updated_by f ∘ g) ∧
        ∀p g f.
          p with <|pair_y updated_by f; pair_y updated_by g|> =
          p with pair_y updated_by f ∘ g
   
   [pair_t_fupdfupds_comp]  Theorem
      
      ⊢ ((∀g f. pair_x_fupd f ∘ pair_x_fupd g = pair_x_fupd (f ∘ g)) ∧
         ∀h g f.
           pair_x_fupd f ∘ pair_x_fupd g ∘ h = pair_x_fupd (f ∘ g) ∘ h) ∧
        (∀g f. pair_y_fupd f ∘ pair_y_fupd g = pair_y_fupd (f ∘ g)) ∧
        ∀h g f. pair_y_fupd f ∘ pair_y_fupd g ∘ h = pair_y_fupd (f ∘ g) ∘ h
   
   [pair_t_induction]  Theorem
      
      ⊢ ∀P. (∀t t0. P (pair_t t t0)) ⇒ ∀p. P p
   
   [pair_t_literal_11]  Theorem
      
      ⊢ ∀t01 t1 t02 t2.
          <|pair_x := t01; pair_y := t1|> = <|pair_x := t02; pair_y := t2|> ⇔
          t01 = t02 ∧ t1 = t2
   
   [pair_t_literal_nchotomy]  Theorem
      
      ⊢ ∀p. ∃t0 t. p = <|pair_x := t0; pair_y := t|>
   
   [pair_t_nchotomy]  Theorem
      
      ⊢ ∀pp. ∃t t0. pp = pair_t t t0
   
   [pair_t_updates_eq_literal]  Theorem
      
      ⊢ ∀p t0 t.
          p with <|pair_x := t0; pair_y := t|> =
          <|pair_x := t0; pair_y := t|>
   
   [struct_with_pair_t_11]  Theorem
      
      ⊢ ∀a a'. struct_with_pair_t a = struct_with_pair_t a' ⇔ a = a'
   
   [struct_with_pair_t_Axiom]  Theorem
      
      ⊢ ∀f. ∃fn. ∀a. fn (struct_with_pair_t a) = f a
   
   [struct_with_pair_t_accessors]  Theorem
      
      ⊢ ∀p. (struct_with_pair_t p).struct_with_pair_p = p
   
   [struct_with_pair_t_accfupds]  Theorem
      
      ⊢ ∀s f.
          (s with struct_with_pair_p updated_by f).struct_with_pair_p =
          f s.struct_with_pair_p
   
   [struct_with_pair_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧ (∀a. M' = struct_with_pair_t a ⇒ f a = f' a) ⇒
          struct_with_pair_t_CASE M f = struct_with_pair_t_CASE M' f'
   
   [struct_with_pair_t_case_eq]  Theorem
      
      ⊢ struct_with_pair_t_CASE x f = v ⇔
        ∃p. x = struct_with_pair_t p ∧ f p = v
   
   [struct_with_pair_t_component_equality]  Theorem
      
      ⊢ ∀s1 s2. s1 = s2 ⇔ s1.struct_with_pair_p = s2.struct_with_pair_p
   
   [struct_with_pair_t_fn_updates]  Theorem
      
      ⊢ ∀f p.
          struct_with_pair_t p with struct_with_pair_p updated_by f =
          struct_with_pair_t (f p)
   
   [struct_with_pair_t_fupdfupds]  Theorem
      
      ⊢ ∀s g f.
          s with
          <|struct_with_pair_p updated_by f;
            struct_with_pair_p updated_by g|> =
          s with struct_with_pair_p updated_by f ∘ g
   
   [struct_with_pair_t_fupdfupds_comp]  Theorem
      
      ⊢ (∀g f.
           struct_with_pair_p_fupd f ∘ struct_with_pair_p_fupd g =
           struct_with_pair_p_fupd (f ∘ g)) ∧
        ∀h g f.
          struct_with_pair_p_fupd f ∘ struct_with_pair_p_fupd g ∘ h =
          struct_with_pair_p_fupd (f ∘ g) ∘ h
   
   [struct_with_pair_t_induction]  Theorem
      
      ⊢ ∀P. (∀p. P (struct_with_pair_t p)) ⇒ ∀s. P s
   
   [struct_with_pair_t_literal_11]  Theorem
      
      ⊢ ∀p1 p2.
          <|struct_with_pair_p := p1|> = <|struct_with_pair_p := p2|> ⇔
          p1 = p2
   
   [struct_with_pair_t_literal_nchotomy]  Theorem
      
      ⊢ ∀s. ∃p. s = <|struct_with_pair_p := p|>
   
   [struct_with_pair_t_nchotomy]  Theorem
      
      ⊢ ∀ss. ∃p. ss = struct_with_pair_t p
   
   [struct_with_pair_t_updates_eq_literal]  Theorem
      
      ⊢ ∀s p. s with struct_with_pair_p := p = <|struct_with_pair_p := p|>
   
   [struct_with_tuple_t_11]  Theorem
      
      ⊢ ∀a a'. struct_with_tuple_t a = struct_with_tuple_t a' ⇔ a = a'
   
   [struct_with_tuple_t_Axiom]  Theorem
      
      ⊢ ∀f. ∃fn. ∀a. fn (struct_with_tuple_t a) = f a
   
   [struct_with_tuple_t_accessors]  Theorem
      
      ⊢ ∀p. (struct_with_tuple_t p).struct_with_tuple_p = p
   
   [struct_with_tuple_t_accfupds]  Theorem
      
      ⊢ ∀s f.
          (s with struct_with_tuple_p updated_by f).struct_with_tuple_p =
          f s.struct_with_tuple_p
   
   [struct_with_tuple_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧ (∀a. M' = struct_with_tuple_t a ⇒ f a = f' a) ⇒
          struct_with_tuple_t_CASE M f = struct_with_tuple_t_CASE M' f'
   
   [struct_with_tuple_t_case_eq]  Theorem
      
      ⊢ struct_with_tuple_t_CASE x f = v ⇔
        ∃p. x = struct_with_tuple_t p ∧ f p = v
   
   [struct_with_tuple_t_component_equality]  Theorem
      
      ⊢ ∀s1 s2. s1 = s2 ⇔ s1.struct_with_tuple_p = s2.struct_with_tuple_p
   
   [struct_with_tuple_t_fn_updates]  Theorem
      
      ⊢ ∀f p.
          struct_with_tuple_t p with struct_with_tuple_p updated_by f =
          struct_with_tuple_t (f p)
   
   [struct_with_tuple_t_fupdfupds]  Theorem
      
      ⊢ ∀s g f.
          s with
          <|struct_with_tuple_p updated_by f;
            struct_with_tuple_p updated_by g|> =
          s with struct_with_tuple_p updated_by f ∘ g
   
   [struct_with_tuple_t_fupdfupds_comp]  Theorem
      
      ⊢ (∀g f.
           struct_with_tuple_p_fupd f ∘ struct_with_tuple_p_fupd g =
           struct_with_tuple_p_fupd (f ∘ g)) ∧
        ∀h g f.
          struct_with_tuple_p_fupd f ∘ struct_with_tuple_p_fupd g ∘ h =
          struct_with_tuple_p_fupd (f ∘ g) ∘ h
   
   [struct_with_tuple_t_induction]  Theorem
      
      ⊢ ∀P. (∀p. P (struct_with_tuple_t p)) ⇒ ∀s. P s
   
   [struct_with_tuple_t_literal_11]  Theorem
      
      ⊢ ∀p1 p2.
          <|struct_with_tuple_p := p1|> = <|struct_with_tuple_p := p2|> ⇔
          p1 = p2
   
   [struct_with_tuple_t_literal_nchotomy]  Theorem
      
      ⊢ ∀s. ∃p. s = <|struct_with_tuple_p := p|>
   
   [struct_with_tuple_t_nchotomy]  Theorem
      
      ⊢ ∀ss. ∃p. ss = struct_with_tuple_t p
   
   [struct_with_tuple_t_updates_eq_literal]  Theorem
      
      ⊢ ∀s p.
          s with struct_with_tuple_p := p = <|struct_with_tuple_p := p|>
   
   [sum_t_11]  Theorem
      
      ⊢ (∀a a'. SumLeft a = SumLeft a' ⇔ a = a') ∧
        ∀a a'. SumRight a = SumRight a' ⇔ a = a'
   
   [sum_t_Axiom]  Theorem
      
      ⊢ ∀f0 f1. ∃fn.
          (∀a. fn (SumLeft a) = f0 a) ∧ ∀a. fn (SumRight a) = f1 a
   
   [sum_t_case_cong]  Theorem
      
      ⊢ ∀M M' f f1.
          M = M' ∧ (∀a. M' = SumLeft a ⇒ f a = f' a) ∧
          (∀a. M' = SumRight a ⇒ f1 a = f1' a) ⇒
          sum_t_CASE M f f1 = sum_t_CASE M' f' f1'
   
   [sum_t_case_eq]  Theorem
      
      ⊢ sum_t_CASE x f f1 = v ⇔
        (∃t. x = SumLeft t ∧ f t = v) ∨ ∃t. x = SumRight t ∧ f1 t = v
   
   [sum_t_distinct]  Theorem
      
      ⊢ ∀a' a. SumLeft a ≠ SumRight a'
   
   [sum_t_induction]  Theorem
      
      ⊢ ∀P. (∀t. P (SumLeft t)) ∧ (∀t. P (SumRight t)) ⇒ ∀s. P s
   
   [sum_t_nchotomy]  Theorem
      
      ⊢ ∀ss. (∃t. ss = SumLeft t) ∨ ∃t. ss = SumRight t
   
   [tree_t_11]  Theorem
      
      ⊢ (∀a a'. TreeLeaf a = TreeLeaf a' ⇔ a = a') ∧
        ∀a0 a1 a2 a0' a1' a2'.
          TreeNode a0 a1 a2 = TreeNode a0' a1' a2' ⇔
          a0 = a0' ∧ a1 = a1' ∧ a2 = a2'
   
   [tree_t_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3. ∃fn0 fn1.
          (∀a. fn0 (TreeLeaf a) = f0 a) ∧
          (∀a0 a1 a2.
             fn0 (TreeNode a0 a1 a2) = f1 a0 a1 a2 (fn1 a1) (fn0 a2)) ∧
          (∀a0 a1. fn1 (NodeElemCons a0 a1) = f2 a0 a1 (fn0 a0) (fn1 a1)) ∧
          fn1 NodeElemNil = f3
   
   [tree_t_case_cong]  Theorem
      
      ⊢ ∀M M' f f1.
          M = M' ∧ (∀a. M' = TreeLeaf a ⇒ f a = f' a) ∧
          (∀a0 a1 a2. M' = TreeNode a0 a1 a2 ⇒ f1 a0 a1 a2 = f1' a0 a1 a2) ⇒
          tree_t_CASE M f f1 = tree_t_CASE M' f' f1'
   
   [tree_t_case_eq]  Theorem
      
      ⊢ tree_t_CASE x f f1 = v ⇔
        (∃t. x = TreeLeaf t ∧ f t = v) ∨
        ∃t0 n t. x = TreeNode t0 n t ∧ f1 t0 n t = v
   
   [tree_t_distinct]  Theorem
      
      ⊢ ∀a2 a1 a0 a. TreeLeaf a ≠ TreeNode a0 a1 a2
   
   [tree_t_induction]  Theorem
      
      ⊢ ∀P0 P1.
          (∀t. P0 (TreeLeaf t)) ∧
          (∀n t. P1 n ∧ P0 t ⇒ ∀t0. P0 (TreeNode t0 n t)) ∧
          (∀t n. P0 t ∧ P1 n ⇒ P1 (NodeElemCons t n)) ∧ P1 NodeElemNil ⇒
          (∀t. P0 t) ∧ ∀n. P1 n
   
   [tree_t_nchotomy]  Theorem
      
      ⊢ ∀tt. (∃t. tt = TreeLeaf t) ∨ ∃t0 n t. tt = TreeNode t0 n t
   
   
*)
end
