signature paperTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val call_choose_fwd_def : thm
    val choose_back_def : thm
    val choose_fwd_def : thm
    val list_nth_mut_back_def : thm
    val list_nth_mut_fwd_def : thm
    val list_t_TY_DEF : thm
    val list_t_case_def : thm
    val list_t_size_def : thm
    val ref_incr_fwd_back_def : thm
    val sum_fwd_def : thm
    val test_choose_fwd_def : thm
    val test_incr_fwd_def : thm
    val test_nth_fwd_def : thm
  
  (*  Theorems  *)
    val datatype_list_t : thm
    val list_t_11 : thm
    val list_t_Axiom : thm
    val list_t_case_cong : thm
    val list_t_case_eq : thm
    val list_t_distinct : thm
    val list_t_induction : thm
    val list_t_nchotomy : thm
  
  val paper_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [divDef] Parent theory of "paper"
   
   [call_choose_fwd_def]  Definition
      
      ⊢ ∀p. call_choose_fwd p =
            (let
               (px,py) = p
             in
               do
                 pz <- choose_fwd T px py;
                 pz0 <- u32_add pz (int_to_u32 1);
                 (px0,_) <- choose_back T px py pz0;
                 Return px0
               od)
   
   [choose_back_def]  Definition
      
      ⊢ ∀b x y ret.
          choose_back b x y ret =
          if b then Return (ret,y) else Return (x,ret)
   
   [choose_fwd_def]  Definition
      
      ⊢ ∀b x y. choose_fwd b x y = if b then Return x else Return y
   
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
   
   [ref_incr_fwd_back_def]  Definition
      
      ⊢ ∀x. ref_incr_fwd_back x = i32_add x (int_to_i32 1)
   
   [sum_fwd_def]  Definition
      
      ⊢ ∀l. sum_fwd l =
            case l of
              ListCons x tl => do i <- sum_fwd tl; i32_add x i od
            | ListNil => Return (int_to_i32 0)
   
   [test_choose_fwd_def]  Definition
      
      ⊢ test_choose_fwd =
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
   
   [test_incr_fwd_def]  Definition
      
      ⊢ test_incr_fwd =
        do
          x <- ref_incr_fwd_back (int_to_i32 0);
          if x ≠ int_to_i32 1 then Fail Failure else Return ()
        od
   
   [test_nth_fwd_def]  Definition
      
      ⊢ test_nth_fwd =
        (let
           l = ListNil;
           l0 = ListCons (int_to_i32 3) l;
           l1 = ListCons (int_to_i32 2) l0
         in
           do
             x <-
               list_nth_mut_fwd (ListCons (int_to_i32 1) l1) (int_to_u32 2);
             x0 <- i32_add x (int_to_i32 1);
             l2 <-
               list_nth_mut_back (ListCons (int_to_i32 1) l1)
                 (int_to_u32 2) x0;
             i <- sum_fwd l2;
             if i ≠ int_to_i32 7 then Fail Failure else Return ()
           od)
   
   [datatype_list_t]  Theorem
      
      ⊢ DATATYPE (list_t ListCons ListNil)
   
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
   
   
*)
end
