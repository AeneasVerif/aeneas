signature TestTheory =
sig
  type thm = Thm.thm
  
  (*  Axioms  *)
    val VEC_TO_LIST_BOUNDS : thm
    val i32_to_int_bounds : thm
    val insert_def : thm
    val int_to_i32_id : thm
    val int_to_u32_id : thm
    val u32_to_int_bounds : thm
  
  (*  Definitions  *)
    val distinct_keys_def : thm
    val error_BIJ : thm
    val error_CASE : thm
    val error_TY_DEF : thm
    val error_size_def : thm
    val i32_add_def : thm
    val i32_max_def : thm
    val i32_min_def : thm
    val int1_def : thm
    val int2_def : thm
    val is_loop_def : thm
    val is_true_def : thm
    val list_t_TY_DEF : thm
    val list_t_case_def : thm
    val list_t_size_def : thm
    val list_t_v_def : thm
    val lookup_def : thm
    val mk_i32_def : thm
    val mk_u32_def : thm
    val nth_expand_def : thm
    val nth_fuel_P_def : thm
    val result_TY_DEF : thm
    val result_case_def : thm
    val result_size_def : thm
    val st_ex_bind_def : thm
    val st_ex_return_def : thm
    val test1_def : thm
    val test2_TY_DEF : thm
    val test2_case_def : thm
    val test2_size_def : thm
    val test_TY_DEF : thm
    val test_case_def : thm
    val test_monad2_def : thm
    val test_monad3_def : thm
    val test_monad_def : thm
    val test_size_def : thm
    val u32_add_def : thm
    val u32_max_def : thm
    val u32_sub_def : thm
    val usize_max_def : thm
    val vec_len_def : thm
  
  (*  Theorems  *)
    val I32_ADD_EQ : thm
    val INT_OF_NUM_INJ : thm
    val INT_THM1 : thm
    val INT_THM2 : thm
    val MK_I32_SUCCESS : thm
    val MK_U32_SUCCESS : thm
    val NAT_THM1 : thm
    val NAT_THM2 : thm
    val NUM_SUB_1_EQ : thm
    val NUM_SUB_1_EQ1 : thm
    val NUM_SUB_EQ : thm
    val U32_ADD_EQ : thm
    val U32_SUB_EQ : thm
    val VEC_TO_LIST_INT_BOUNDS : thm
    val datatype_error : thm
    val datatype_list_t : thm
    val datatype_result : thm
    val datatype_test : thm
    val datatype_test2 : thm
    val error2num_11 : thm
    val error2num_ONTO : thm
    val error2num_num2error : thm
    val error2num_thm : thm
    val error_Axiom : thm
    val error_EQ_error : thm
    val error_case_cong : thm
    val error_case_def : thm
    val error_case_eq : thm
    val error_induction : thm
    val error_nchotomy : thm
    val insert_lem : thm
    val list_nth_mut_loop_loop_fwd_def : thm
    val list_nth_mut_loop_loop_fwd_ind : thm
    val list_t_11 : thm
    val list_t_Axiom : thm
    val list_t_case_cong : thm
    val list_t_case_eq : thm
    val list_t_distinct : thm
    val list_t_induction : thm
    val list_t_nchotomy : thm
    val lookup_raw_def : thm
    val lookup_raw_ind : thm
    val nth_def : thm
    val nth_def_loop : thm
    val nth_def_terminates : thm
    val nth_fuel_P_mono : thm
    val nth_fuel_def : thm
    val nth_fuel_ind : thm
    val nth_fuel_least_fail_mono : thm
    val nth_fuel_least_success_mono : thm
    val nth_fuel_mono : thm
    val num2error_11 : thm
    val num2error_ONTO : thm
    val num2error_error2num : thm
    val num2error_thm : thm
    val result_11 : thm
    val result_Axiom : thm
    val result_case_cong : thm
    val result_case_eq : thm
    val result_distinct : thm
    val result_induction : thm
    val result_nchotomy : thm
    val test2_11 : thm
    val test2_Axiom : thm
    val test2_case_cong : thm
    val test2_case_eq : thm
    val test2_distinct : thm
    val test2_induction : thm
    val test2_nchotomy : thm
    val test_11 : thm
    val test_Axiom : thm
    val test_case_cong : thm
    val test_case_eq : thm
    val test_distinct : thm
    val test_induction : thm
    val test_nchotomy : thm
  
  val Test_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Omega] Parent theory of "Test"
   
   [int_arith] Parent theory of "Test"
   
   [words] Parent theory of "Test"
   
   [insert_def]  Axiom
      
      [oracles: ] [axioms: insert_def] []
      ⊢ insert key value ls =
        case ls of
          ListCons (ckey,cvalue) tl =>
            if ckey = key then Return (ListCons (ckey,value) tl)
            else
              do
                tl0 <- insert key value tl;
                Return (ListCons (ckey,cvalue) tl0)
              od
        | ListNil => Return (ListCons (key,value) ListNil)
   
   [u32_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: u32_to_int_bounds] []
      ⊢ ∀n. 0 ≤ u32_to_int n ∧ u32_to_int n ≤ u32_max
   
   [i32_to_int_bounds]  Axiom
      
      [oracles: ] [axioms: i32_to_int_bounds] []
      ⊢ ∀n. i32_min ≤ i32_to_int n ∧ i32_to_int n ≤ i32_max
   
   [int_to_u32_id]  Axiom
      
      [oracles: ] [axioms: int_to_u32_id] []
      ⊢ ∀n. 0 ≤ n ∧ n ≤ u32_max ⇒ u32_to_int (int_to_u32 n) = n
   
   [int_to_i32_id]  Axiom
      
      [oracles: ] [axioms: int_to_i32_id] []
      ⊢ ∀n. i32_min ≤ n ∧ n ≤ i32_max ⇒ i32_to_int (int_to_i32 n) = n
   
   [VEC_TO_LIST_BOUNDS]  Axiom
      
      [oracles: ] [axioms: VEC_TO_LIST_BOUNDS] []
      ⊢ ∀v. (let l = LENGTH (vec_to_list v) in 0 ≤ l ∧ l ≤ 4294967295)
   
   [distinct_keys_def]  Definition
      
      ⊢ ∀ls.
          distinct_keys ls ⇔
          ∀i j.
            i < LENGTH ls ⇒
            j < LENGTH ls ⇒
            FST (EL i ls) = FST (EL j ls) ⇒
            i = j
   
   [error_BIJ]  Definition
      
      ⊢ (∀a. num2error (error2num a) = a) ∧
        ∀r. (λn. n < 1) r ⇔ error2num (num2error r) = r
   
   [error_CASE]  Definition
      
      ⊢ ∀x v0. (case x of Failure => v0) = (λm. v0) (error2num x)
   
   [error_TY_DEF]  Definition
      
      ⊢ ∃rep. TYPE_DEFINITION (λn. n < 1) rep
   
   [error_size_def]  Definition
      
      ⊢ ∀x. error_size x = 0
   
   [i32_add_def]  Definition
      
      ⊢ ∀x y. i32_add x y = mk_i32 (i32_to_int x + i32_to_int y)
   
   [i32_max_def]  Definition
      
      ⊢ i32_max = 2147483647
   
   [i32_min_def]  Definition
      
      ⊢ i32_min = -2147483648
   
   [int1_def]  Definition
      
      ⊢ int1 = 32
   
   [int2_def]  Definition
      
      ⊢ int2 = -32
   
   [is_loop_def]  Definition
      
      ⊢ ∀r. is_loop r ⇔ case r of Return v2 => F | Fail v3 => F | Loop => T
   
   [is_true_def]  Definition
      
      ⊢ ∀x. is_true x = if x then Return () else Fail Failure
   
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
   
   [list_t_v_def]  Definition
      
      ⊢ list_t_v ListNil = [] ∧
        ∀x tl. list_t_v (ListCons x tl) = x::list_t_v tl
   
   [lookup_def]  Definition
      
      ⊢ ∀key ls. lookup key ls = lookup_raw key (list_t_v ls)
   
   [mk_i32_def]  Definition
      
      ⊢ ∀n. mk_i32 n =
            if i32_min ≤ n ∧ n ≤ i32_max then Return (int_to_i32 n)
            else Fail Failure
   
   [mk_u32_def]  Definition
      
      ⊢ ∀n. mk_u32 n =
            if 0 ≤ n ∧ n ≤ u32_max then Return (int_to_u32 n)
            else Fail Failure
   
   [nth_expand_def]  Definition
      
      ⊢ ∀nth ls i.
          nth_expand nth ls i =
          case ls of
            ListCons x tl =>
              if u32_to_int i = 0 then Return x
              else do i0 <- u32_sub i (int_to_u32 1); nth tl i0 od
          | ListNil => Fail Failure
   
   [nth_fuel_P_def]  Definition
      
      ⊢ ∀ls i n. nth_fuel_P ls i n ⇔ ¬is_loop (nth_fuel n ls i)
   
   [result_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0.
                 ∀ $var$('result').
                   (∀a0.
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR 0 (a,ARB)
                                  (λn. ind_type$BOTTOM)) a) ∨
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR (SUC 0) (ARB,a)
                                  (λn. ind_type$BOTTOM)) a) ∨
                      a0 =
                      ind_type$CONSTR (SUC (SUC 0)) (ARB,ARB)
                        (λn. ind_type$BOTTOM) ⇒
                      $var$('result') a0) ⇒
                   $var$('result') a0) rep
   
   [result_case_def]  Definition
      
      ⊢ (∀a f f1 v. result_CASE (Return a) f f1 v = f a) ∧
        (∀a f f1 v. result_CASE (Fail a) f f1 v = f1 a) ∧
        ∀f f1 v. result_CASE Loop f f1 v = v
   
   [result_size_def]  Definition
      
      ⊢ (∀f a. result_size f (Return a) = 1 + f a) ∧
        (∀f a. result_size f (Fail a) = 1 + error_size a) ∧
        ∀f. result_size f Loop = 0
   
   [st_ex_bind_def]  Definition
      
      ⊢ ∀x f.
          monad_bind x f =
          case x of Return y => f y | Fail e => Fail e | Loop => Loop
   
   [st_ex_return_def]  Definition
      
      ⊢ ∀x. st_ex_return x = Return x
   
   [test1_def]  Definition
      
      ⊢ ∀x. test1 x = Return x
   
   [test2_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0.
                 ∀ $var$('test2').
                   (∀a0.
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR 0 (a,ARB)
                                  (λn. ind_type$BOTTOM)) a) ∨
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR (SUC 0) (ARB,a)
                                  (λn. ind_type$BOTTOM)) a) ⇒
                      $var$('test2') a0) ⇒
                   $var$('test2') a0) rep
   
   [test2_case_def]  Definition
      
      ⊢ (∀a f f1. test2_CASE (Variant1_2 a) f f1 = f a) ∧
        ∀a f f1. test2_CASE (Variant2_2 a) f f1 = f1 a
   
   [test2_size_def]  Definition
      
      ⊢ (∀f f1 a. test2_size f f1 (Variant1_2 a) = 1 + f a) ∧
        ∀f f1 a. test2_size f f1 (Variant2_2 a) = 1 + f1 a
   
   [test_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0.
                 ∀ $var$('test').
                   (∀a0.
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR 0 (a,ARB)
                                  (λn. ind_type$BOTTOM)) a) ∨
                      (∃a. a0 =
                           (λa.
                                ind_type$CONSTR (SUC 0) (ARB,a)
                                  (λn. ind_type$BOTTOM)) a) ⇒
                      $var$('test') a0) ⇒
                   $var$('test') a0) rep
   
   [test_case_def]  Definition
      
      ⊢ (∀a f f1. test_CASE (Variant1 a) f f1 = f a) ∧
        ∀a f f1. test_CASE (Variant2 a) f f1 = f1 a
   
   [test_monad2_def]  Definition
      
      ⊢ test_monad2 = do x <- Return T; Return x od
   
   [test_monad3_def]  Definition
      
      ⊢ ∀x. test_monad3 x = monad_ignore_bind (is_true x) (Return x)
   
   [test_monad_def]  Definition
      
      ⊢ ∀v. test_monad v = do x <- Return v; Return x od
   
   [test_size_def]  Definition
      
      ⊢ (∀f f1 a. test_size f f1 (Variant1 a) = 1 + f1 a) ∧
        ∀f f1 a. test_size f f1 (Variant2 a) = 1 + f a
   
   [u32_add_def]  Definition
      
      ⊢ ∀x y. u32_add x y = mk_u32 (u32_to_int x + u32_to_int y)
   
   [u32_max_def]  Definition
      
      ⊢ u32_max = 4294967295
   
   [u32_sub_def]  Definition
      
      ⊢ ∀x y. u32_sub x y = mk_u32 (u32_to_int x − u32_to_int y)
   
   [usize_max_def]  Definition
      
      ⊢ usize_max = 4294967295
   
   [vec_len_def]  Definition
      
      ⊢ ∀v. vec_len v = int_to_u32 (&LENGTH (vec_to_list v))
   
   [I32_ADD_EQ]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_i32_id] []
      ⊢ ∀x y.
          i32_min ≤ i32_to_int x + i32_to_int y ⇒
          i32_to_int x + i32_to_int y ≤ i32_max ⇒
          ∃z. i32_add x y = Return z ∧
              i32_to_int z = i32_to_int x + i32_to_int y
   
   [INT_OF_NUM_INJ]  Theorem
      
      ⊢ ∀n m. &n = &m ⇒ n = m
   
   [INT_THM1]  Theorem
      
      ⊢ ∀x y. x > 0 ⇒ y > 0 ⇒ x + y > 0
   
   [INT_THM2]  Theorem
      
      ⊢ ∀x. T
   
   [MK_I32_SUCCESS]  Theorem
      
      ⊢ ∀n. i32_min ≤ n ∧ n ≤ i32_max ⇒ mk_i32 n = Return (int_to_i32 n)
   
   [MK_U32_SUCCESS]  Theorem
      
      ⊢ ∀n. 0 ≤ n ∧ n ≤ u32_max ⇒ mk_u32 n = Return (int_to_u32 n)
   
   [NAT_THM1]  Theorem
      
      ⊢ ∀n. n < n + 1
   
   [NAT_THM2]  Theorem
      
      ⊢ ∀n. n < n + 1
   
   [NUM_SUB_1_EQ]  Theorem
      
      ⊢ ∀x y. x = y − 1 ⇒ 0 ≤ x ⇒ Num y = SUC (Num x)
   
   [NUM_SUB_1_EQ1]  Theorem
      
      ⊢ ∀i. 0 ≤ i − 1 ⇒ Num i = SUC (Num (i − 1))
   
   [NUM_SUB_EQ]  Theorem
      
      ⊢ ∀x y z. x = y − z ⇒ 0 ≤ x ⇒ 0 ≤ z ⇒ Num y = Num z + Num x
   
   [U32_ADD_EQ]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_u32_id, u32_to_int_bounds] []
      ⊢ ∀x y.
          u32_to_int x + u32_to_int y ≤ u32_max ⇒
          ∃z. u32_add x y = Return z ∧
              u32_to_int z = u32_to_int x + u32_to_int y
   
   [U32_SUB_EQ]  Theorem
      
      [oracles: DISK_THM] [axioms: int_to_u32_id, u32_to_int_bounds] []
      ⊢ ∀x y.
          0 ≤ u32_to_int x − u32_to_int y ⇒
          ∃z. u32_sub x y = Return z ∧
              u32_to_int z = u32_to_int x − u32_to_int y
   
   [VEC_TO_LIST_INT_BOUNDS]  Theorem
      
      [oracles: DISK_THM] [axioms: VEC_TO_LIST_BOUNDS] []
      ⊢ ∀v. (let l = &LENGTH (vec_to_list v) in 0 ≤ l ∧ l ≤ u32_max)
   
   [datatype_error]  Theorem
      
      ⊢ DATATYPE (error Failure)
   
   [datatype_list_t]  Theorem
      
      ⊢ DATATYPE (list_t ListCons ListNil)
   
   [datatype_result]  Theorem
      
      ⊢ DATATYPE (result Return Fail Loop)
   
   [datatype_test]  Theorem
      
      ⊢ DATATYPE (test Variant1 Variant2)
   
   [datatype_test2]  Theorem
      
      ⊢ DATATYPE (test2 Variant1_2 Variant2_2)
   
   [error2num_11]  Theorem
      
      ⊢ ∀a a'. error2num a = error2num a' ⇔ a = a'
   
   [error2num_ONTO]  Theorem
      
      ⊢ ∀r. r < 1 ⇔ ∃a. r = error2num a
   
   [error2num_num2error]  Theorem
      
      ⊢ ∀r. r < 1 ⇔ error2num (num2error r) = r
   
   [error2num_thm]  Theorem
      
      ⊢ error2num Failure = 0
   
   [error_Axiom]  Theorem
      
      ⊢ ∀x0. ∃f. f Failure = x0
   
   [error_EQ_error]  Theorem
      
      ⊢ ∀a a'. a = a' ⇔ error2num a = error2num a'
   
   [error_case_cong]  Theorem
      
      ⊢ ∀M M' v0.
          M = M' ∧ (M' = Failure ⇒ v0 = v0') ⇒
          (case M of Failure => v0) = case M' of Failure => v0'
   
   [error_case_def]  Theorem
      
      ⊢ ∀v0. (case Failure of Failure => v0) = v0
   
   [error_case_eq]  Theorem
      
      ⊢ (case x of Failure => v0) = v ⇔ x = Failure ∧ v0 = v
   
   [error_induction]  Theorem
      
      ⊢ ∀P. P Failure ⇒ ∀a. P a
   
   [error_nchotomy]  Theorem
      
      ⊢ ∀a. a = Failure
   
   [insert_lem]  Theorem
      
      [oracles: DISK_THM] [axioms: u32_to_int_bounds, insert_def] []
      ⊢ ∀ls key value.
          distinct_keys (list_t_v ls) ⇒
          case insert key value ls of
            Return ls1 =>
              lookup key ls1 = SOME value ∧
              ∀k. k ≠ key ⇒ lookup k ls = lookup k ls1
          | Fail v1 => F
          | Loop => F
   
   [list_nth_mut_loop_loop_fwd_def]  Theorem
      
      ⊢ ∀ls i.
          list_nth_mut_loop_loop_fwd ls i =
          case ls of
            ListCons x tl =>
              if u32_to_int i = 0 then Return x
              else
                do
                  i0 <- u32_sub i (int_to_u32 1);
                  list_nth_mut_loop_loop_fwd tl i0
                od
          | ListNil => Fail Failure
   
   [list_nth_mut_loop_loop_fwd_ind]  Theorem
      
      ⊢ ∀P. (∀ls i.
               (∀x tl i0. ls = ListCons x tl ∧ u32_to_int i ≠ 0 ⇒ P tl i0) ⇒
               P ls i) ⇒
            ∀v v1. P v v1
   
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
   
   [lookup_raw_def]  Theorem
      
      ⊢ (∀key. lookup_raw key [] = NONE) ∧
        ∀v ls key k.
          lookup_raw key ((k,v)::ls) =
          if k = key then SOME v else lookup_raw key ls
   
   [lookup_raw_ind]  Theorem
      
      ⊢ ∀P. (∀key. P key []) ∧
            (∀key k v ls. (k ≠ key ⇒ P key ls) ⇒ P key ((k,v)::ls)) ⇒
            ∀v v1. P v v1
   
   [nth_def]  Theorem
      
      ⊢ ∀ls i.
          nth ls i =
          case ls of
            ListCons x tl =>
              if u32_to_int i = 0 then Return x
              else do i0 <- u32_sub i (int_to_u32 1); nth tl i0 od
          | ListNil => Fail Failure
   
   [nth_def_loop]  Theorem
      
      ⊢ ∀ls i. (∀n. ¬nth_fuel_P ls i n) ⇒ nth ls i = nth_expand nth ls i
   
   [nth_def_terminates]  Theorem
      
      ⊢ ∀ls i. (∃n. nth_fuel_P ls i n) ⇒ nth ls i = nth_expand nth ls i
   
   [nth_fuel_P_mono]  Theorem
      
      ⊢ ∀n m ls i.
          n ≤ m ⇒ nth_fuel_P ls i n ⇒ nth_fuel n ls i = nth_fuel m ls i
   
   [nth_fuel_def]  Theorem
      
      ⊢ ∀n ls i.
          nth_fuel n ls i =
          case n of
            0 => Loop
          | SUC n' =>
            case ls of
              ListCons x tl =>
                if u32_to_int i = 0 then Return x
                else
                  do i0 <- u32_sub i (int_to_u32 1); nth_fuel n' tl i0 od
            | ListNil => Fail Failure
   
   [nth_fuel_ind]  Theorem
      
      ⊢ ∀P. (∀n ls i.
               (∀n' x tl i0.
                  n = SUC n' ∧ ls = ListCons x tl ∧ u32_to_int i ≠ 0 ⇒
                  P n' tl i0) ⇒
               P n ls i) ⇒
            ∀v v1 v2. P v v1 v2
   
   [nth_fuel_least_fail_mono]  Theorem
      
      ⊢ ∀n ls i. n < $LEAST (nth_fuel_P ls i) ⇒ nth_fuel n ls i = Loop
   
   [nth_fuel_least_success_mono]  Theorem
      
      ⊢ ∀n ls i.
          $LEAST (nth_fuel_P ls i) ≤ n ⇒
          nth_fuel n ls i = nth_fuel ($LEAST (nth_fuel_P ls i)) ls i
   
   [nth_fuel_mono]  Theorem
      
      ⊢ ∀n m ls i.
          n ≤ m ⇒
          if is_loop (nth_fuel n ls i) then T
          else nth_fuel n ls i = nth_fuel m ls i
   
   [num2error_11]  Theorem
      
      ⊢ ∀r r'. r < 1 ⇒ r' < 1 ⇒ (num2error r = num2error r' ⇔ r = r')
   
   [num2error_ONTO]  Theorem
      
      ⊢ ∀a. ∃r. a = num2error r ∧ r < 1
   
   [num2error_error2num]  Theorem
      
      ⊢ ∀a. num2error (error2num a) = a
   
   [num2error_thm]  Theorem
      
      ⊢ num2error 0 = Failure
   
   [result_11]  Theorem
      
      ⊢ (∀a a'. Return a = Return a' ⇔ a = a') ∧
        ∀a a'. Fail a = Fail a' ⇔ a = a'
   
   [result_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2. ∃fn.
          (∀a. fn (Return a) = f0 a) ∧ (∀a. fn (Fail a) = f1 a) ∧
          fn Loop = f2
   
   [result_case_cong]  Theorem
      
      ⊢ ∀M M' f f1 v.
          M = M' ∧ (∀a. M' = Return a ⇒ f a = f' a) ∧
          (∀a. M' = Fail a ⇒ f1 a = f1' a) ∧ (M' = Loop ⇒ v = v') ⇒
          result_CASE M f f1 v = result_CASE M' f' f1' v'
   
   [result_case_eq]  Theorem
      
      ⊢ result_CASE x f f1 v = v' ⇔
        (∃a. x = Return a ∧ f a = v') ∨ (∃e. x = Fail e ∧ f1 e = v') ∨
        x = Loop ∧ v = v'
   
   [result_distinct]  Theorem
      
      ⊢ (∀a' a. Return a ≠ Fail a') ∧ (∀a. Return a ≠ Loop) ∧
        ∀a. Fail a ≠ Loop
   
   [result_induction]  Theorem
      
      ⊢ ∀P. (∀a. P (Return a)) ∧ (∀e. P (Fail e)) ∧ P Loop ⇒ ∀r. P r
   
   [result_nchotomy]  Theorem
      
      ⊢ ∀rr. (∃a. rr = Return a) ∨ (∃e. rr = Fail e) ∨ rr = Loop
   
   [test2_11]  Theorem
      
      ⊢ (∀a a'. Variant1_2 a = Variant1_2 a' ⇔ a = a') ∧
        ∀a a'. Variant2_2 a = Variant2_2 a' ⇔ a = a'
   
   [test2_Axiom]  Theorem
      
      ⊢ ∀f0 f1. ∃fn.
          (∀a. fn (Variant1_2 a) = f0 a) ∧ ∀a. fn (Variant2_2 a) = f1 a
   
   [test2_case_cong]  Theorem
      
      ⊢ ∀M M' f f1.
          M = M' ∧ (∀a. M' = Variant1_2 a ⇒ f a = f' a) ∧
          (∀a. M' = Variant2_2 a ⇒ f1 a = f1' a) ⇒
          test2_CASE M f f1 = test2_CASE M' f' f1'
   
   [test2_case_eq]  Theorem
      
      ⊢ test2_CASE x f f1 = v ⇔
        (∃T'. x = Variant1_2 T' ∧ f T' = v) ∨
        ∃T'. x = Variant2_2 T' ∧ f1 T' = v
   
   [test2_distinct]  Theorem
      
      ⊢ ∀a' a. Variant1_2 a ≠ Variant2_2 a'
   
   [test2_induction]  Theorem
      
      ⊢ ∀P. (∀T. P (Variant1_2 T)) ∧ (∀T. P (Variant2_2 T)) ⇒ ∀t. P t
   
   [test2_nchotomy]  Theorem
      
      ⊢ ∀tt. (∃T. tt = Variant1_2 T) ∨ ∃T. tt = Variant2_2 T
   
   [test_11]  Theorem
      
      ⊢ (∀a a'. Variant1 a = Variant1 a' ⇔ a = a') ∧
        ∀a a'. Variant2 a = Variant2 a' ⇔ a = a'
   
   [test_Axiom]  Theorem
      
      ⊢ ∀f0 f1. ∃fn.
          (∀a. fn (Variant1 a) = f0 a) ∧ ∀a. fn (Variant2 a) = f1 a
   
   [test_case_cong]  Theorem
      
      ⊢ ∀M M' f f1.
          M = M' ∧ (∀a. M' = Variant1 a ⇒ f a = f' a) ∧
          (∀a. M' = Variant2 a ⇒ f1 a = f1' a) ⇒
          test_CASE M f f1 = test_CASE M' f' f1'
   
   [test_case_eq]  Theorem
      
      ⊢ test_CASE x f f1 = v ⇔
        (∃b. x = Variant1 b ∧ f b = v) ∨ ∃a. x = Variant2 a ∧ f1 a = v
   
   [test_distinct]  Theorem
      
      ⊢ ∀a' a. Variant1 a ≠ Variant2 a'
   
   [test_induction]  Theorem
      
      ⊢ ∀P. (∀b. P (Variant1 b)) ∧ (∀a. P (Variant2 a)) ⇒ ∀t. P t
   
   [test_nchotomy]  Theorem
      
      ⊢ ∀tt. (∃b. tt = Variant1 b) ∨ ∃a. tt = Variant2 a
   
   
*)
end
