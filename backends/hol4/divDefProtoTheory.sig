signature divDefProtoTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val fix_def : thm
    val fix_fuel_P_def : thm
    val fix_fuel_def : thm
    val is_valid_fp_body_def : thm
    val list_t_TY_DEF : thm
    val list_t_case_def : thm
    val list_t_size_def : thm
    val nth_body_def : thm
  
  (*  Theorems  *)
    val datatype_list_t : thm
    val fix_fixed_diverges : thm
    val fix_fixed_eq : thm
    val fix_fixed_terminates : thm
    val fix_fixed_termination_rec_case : thm
    val fix_fuel_compute : thm
    val fix_fuel_mono : thm
    val fix_fuel_mono_least : thm
    val is_valid_suffice : thm
    val list_t_11 : thm
    val list_t_Axiom : thm
    val list_t_case_cong : thm
    val list_t_case_eq : thm
    val list_t_distinct : thm
    val list_t_induction : thm
    val list_t_nchotomy : thm
    val nth_body_is_valid : thm
    val nth_def : thm
  
  val divDefProto_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [primitives] Parent theory of "divDefProto"
   
   [fix_def]  Definition
      
      ⊢ ∀f x.
          fix f x =
          if ∃n. fix_fuel_P f x n then
            fix_fuel ($LEAST (fix_fuel_P f x)) f x
          else Diverge
   
   [fix_fuel_P_def]  Definition
      
      ⊢ ∀f x n. fix_fuel_P f x n ⇔ ¬is_diverge (fix_fuel n f x)
   
   [fix_fuel_def]  Definition
      
      ⊢ (∀f x. fix_fuel 0 f x = Diverge) ∧
        ∀n f x. fix_fuel (SUC n) f x = f (fix_fuel n f) x
   
   [is_valid_fp_body_def]  Definition
      
      ⊢ ∀f. is_valid_fp_body f ⇔
            ∀x. (∀g h. f g x = f h x) ∨ ∃y. ∀g. f g x = g y
   
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
   
   [nth_body_def]  Definition
      
      ⊢ ∀f x.
          nth_body f x =
          (let
             (ls,i) = x
           in
             case ls of
               ListCons x tl =>
                 if u32_to_int i = 0 then Return x
                 else do i0 <- u32_sub i (int_to_u32 1); f (tl,i0) od
             | ListNil => Fail Failure)
   
   [datatype_list_t]  Theorem
      
      ⊢ DATATYPE (list_t ListCons ListNil)
   
   [fix_fixed_diverges]  Theorem
      
      ⊢ ∀f. is_valid_fp_body f ⇒
            ∀x. ¬(∃n. fix_fuel_P f x n) ⇒ fix f x = f (fix f) x
   
   [fix_fixed_eq]  Theorem
      
      ⊢ ∀f. is_valid_fp_body f ⇒ ∀x. fix f x = f (fix f) x
   
   [fix_fixed_terminates]  Theorem
      
      ⊢ ∀f. is_valid_fp_body f ⇒
            ∀x n. fix_fuel_P f x n ⇒ fix f x = f (fix f) x
   
   [fix_fixed_termination_rec_case]  Theorem
      
      ⊢ ∀x y n m.
          is_valid_fp_body f ⇒
          (∀g. f g x = g y) ⇒
          fix_fuel_P f x n ⇒
          fix_fuel_P f y m ⇒
          fix_fuel ($LEAST (fix_fuel_P f x)) f x =
          fix_fuel ($LEAST (fix_fuel_P f y)) f y
   
   [fix_fuel_compute]  Theorem
      
      ⊢ (∀f x. fix_fuel 0 f x = Diverge) ∧
        (∀n f x.
           fix_fuel (NUMERAL (BIT1 n)) f x =
           f (fix_fuel (NUMERAL (BIT1 n) − 1) f) x) ∧
        ∀n f x.
          fix_fuel (NUMERAL (BIT2 n)) f x =
          f (fix_fuel (NUMERAL (BIT1 n)) f) x
   
   [fix_fuel_mono]  Theorem
      
      ⊢ ∀f. is_valid_fp_body f ⇒
            ∀n x.
              fix_fuel_P f x n ⇒
              ∀m. n ≤ m ⇒ fix_fuel n f x = fix_fuel m f x
   
   [fix_fuel_mono_least]  Theorem
      
      ⊢ ∀f. is_valid_fp_body f ⇒
            ∀n x.
              fix_fuel_P f x n ⇒
              fix_fuel n f x = fix_fuel ($LEAST (fix_fuel_P f x)) f x
   
   [is_valid_suffice]  Theorem
      
      ⊢ ∃y. ∀g. g x = g y
   
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
   
   [nth_body_is_valid]  Theorem
      
      ⊢ is_valid_fp_body nth_body
   
   [nth_def]  Theorem
      
      ⊢ ∀ls i.
          nth ls i =
          case ls of
            ListCons x tl =>
              if u32_to_int i = 0 then Return x
              else do i0 <- u32_sub i (int_to_u32 1); nth tl i0 od
          | ListNil => Fail Failure
   
   
*)
end
