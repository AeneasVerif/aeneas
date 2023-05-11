signature divDefProto2Theory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val even_odd_body_def : thm
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
    val even_def : thm
    val even_odd_body_is_valid : thm
    val even_odd_body_is_valid_aux : thm
    val fix_fixed_diverges : thm
    val fix_fixed_eq : thm
    val fix_fixed_terminates : thm
    val fix_fuel_P_least : thm
    val fix_fuel_compute : thm
    val fix_fuel_eq_fix : thm
    val fix_fuel_mono : thm
    val fix_fuel_mono_aux : thm
    val fix_fuel_mono_least : thm
    val fix_fuel_not_diverge_eq_fix : thm
    val fix_fuel_not_diverge_eq_fix_aux : thm
    val fix_not_diverge_implies_fix_fuel : thm
    val fix_not_diverge_implies_fix_fuel_aux : thm
    val is_valid_fp_body_compute : thm
    val list_t_11 : thm
    val list_t_Axiom : thm
    val list_t_case_cong : thm
    val list_t_case_eq : thm
    val list_t_distinct : thm
    val list_t_induction : thm
    val list_t_nchotomy : thm
    val nth_body_is_valid : thm
    val nth_body_is_valid_aux : thm
    val nth_def : thm
    val odd_def : thm
  
  val divDefProto2_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [primitives] Parent theory of "divDefProto2"
   
   [even_odd_body_def]  Definition
      
      ⊢ ∀f x.
          even_odd_body f x =
          case x of
            INL 0 => Return (INR (INR T))
          | INL i =>
            (case f (INR (INL (i − 1))) of
               Return (INL v) => Fail Failure
             | Return (INR (INL v2)) => Fail Failure
             | Return (INR (INR b)) => Return (INR (INR b))
             | Fail e => Fail e
             | Diverge => Diverge)
          | INR (INL 0) => Return (INR (INR F))
          | INR (INL i) =>
            (case f (INL (i − 1)) of
               Return (INL v) => Fail Failure
             | Return (INR (INL v2)) => Fail Failure
             | Return (INR (INR b)) => Return (INR (INR b))
             | Fail e => Fail e
             | Diverge => Diverge)
          | INR (INR v5) => Fail Failure
   
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
      
      ⊢ (∀f. is_valid_fp_body 0 f ⇔ F) ∧
        ∀n f.
          is_valid_fp_body (SUC n) f ⇔
          ∀x. (∀g h. f g x = f h x) ∨
              ∃h y.
                is_valid_fp_body n h ∧ ∀g. f g x = do z <- g y; h g z od
   
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
          case x of
            INL x =>
              (let
                 (ls,i) = x
               in
                 case ls of
                   ListCons x tl =>
                     if u32_to_int i = 0 then Return (INR x)
                     else
                       do
                         i0 <- u32_sub i (int_to_u32 1);
                         r <- f (INL (tl,i0));
                         case r of
                           INL v => Fail Failure
                         | INR i1 => Return (INR i1)
                       od
                 | ListNil => Fail Failure)
          | INR v2 => Fail Failure
   
   [datatype_list_t]  Theorem
      
      ⊢ DATATYPE (list_t ListCons ListNil)
   
   [even_def]  Theorem
      
      ⊢ ∀i. even i = if i = 0 then Return T else odd (i − 1)
   
   [even_odd_body_is_valid]  Theorem
      
      ⊢ is_valid_fp_body (SUC (SUC 0)) even_odd_body
   
   [even_odd_body_is_valid_aux]  Theorem
      
      ⊢ is_valid_fp_body (SUC (SUC n)) even_odd_body
   
   [fix_fixed_diverges]  Theorem
      
      ⊢ ∀N f.
          is_valid_fp_body N f ⇒
          ∀x. ¬(∃n. fix_fuel_P f x n) ⇒ fix f x = f (fix f) x
   
   [fix_fixed_eq]  Theorem
      
      ⊢ ∀N f. is_valid_fp_body N f ⇒ ∀x. fix f x = f (fix f) x
   
   [fix_fixed_terminates]  Theorem
      
      ⊢ ∀N f.
          is_valid_fp_body N f ⇒
          ∀x n. fix_fuel_P f x n ⇒ fix f x = f (fix f) x
   
   [fix_fuel_P_least]  Theorem
      
      ⊢ ∀f n x.
          fix_fuel n f x ≠ Diverge ⇒
          fix_fuel_P f x ($LEAST (fix_fuel_P f x))
   
   [fix_fuel_compute]  Theorem
      
      ⊢ (∀f x. fix_fuel 0 f x = Diverge) ∧
        (∀n f x.
           fix_fuel (NUMERAL (BIT1 n)) f x =
           f (fix_fuel (NUMERAL (BIT1 n) − 1) f) x) ∧
        ∀n f x.
          fix_fuel (NUMERAL (BIT2 n)) f x =
          f (fix_fuel (NUMERAL (BIT1 n)) f) x
   
   [fix_fuel_eq_fix]  Theorem
      
      ⊢ ∀N f.
          is_valid_fp_body N f ⇒
          ∀n x. fix_fuel_P f x n ⇒ fix_fuel n f x = fix f x
   
   [fix_fuel_mono]  Theorem
      
      ⊢ ∀N f.
          is_valid_fp_body N f ⇒
          ∀n x.
            fix_fuel_P f x n ⇒ ∀m. n ≤ m ⇒ fix_fuel n f x = fix_fuel m f x
   
   [fix_fuel_mono_aux]  Theorem
      
      ⊢ ∀n N M g f.
          is_valid_fp_body M f ⇒
          is_valid_fp_body N g ⇒
          ∀x. ¬is_diverge (g (fix_fuel n f) x) ⇒
              ∀m. n ≤ m ⇒ g (fix_fuel n f) x = g (fix_fuel m f) x
   
   [fix_fuel_mono_least]  Theorem
      
      ⊢ ∀N f.
          is_valid_fp_body N f ⇒
          ∀n x.
            fix_fuel_P f x n ⇒
            fix_fuel n f x = fix_fuel ($LEAST (fix_fuel_P f x)) f x
   
   [fix_fuel_not_diverge_eq_fix]  Theorem
      
      ⊢ ∀N f.
          is_valid_fp_body N f ⇒
          ∀n x.
            f (fix_fuel n f) x ≠ Diverge ⇒ f (fix f) x = f (fix_fuel n f) x
   
   [fix_fuel_not_diverge_eq_fix_aux]  Theorem
      
      ⊢ ∀N M g f.
          is_valid_fp_body M f ⇒
          is_valid_fp_body N g ⇒
          ∀n x.
            g (fix_fuel n f) x ≠ Diverge ⇒ g (fix f) x = g (fix_fuel n f) x
   
   [fix_not_diverge_implies_fix_fuel]  Theorem
      
      ⊢ ∀N f.
          is_valid_fp_body N f ⇒
          ∀x. f (fix f) x ≠ Diverge ⇒ ∃n. f (fix f) x = f (fix_fuel n f) x
   
   [fix_not_diverge_implies_fix_fuel_aux]  Theorem
      
      ⊢ ∀N M g f.
          is_valid_fp_body M f ⇒
          is_valid_fp_body N g ⇒
          ∀x. g (fix f) x ≠ Diverge ⇒
              ∃n. g (fix f) x = g (fix_fuel n f) x ∧
                  ∀m. n ≤ m ⇒ g (fix_fuel m f) x = g (fix_fuel n f) x
   
   [is_valid_fp_body_compute]  Theorem
      
      ⊢ (∀f. is_valid_fp_body 0 f ⇔ F) ∧
        (∀n f.
           is_valid_fp_body (NUMERAL (BIT1 n)) f ⇔
           ∀x. (∀g h. f g x = f h x) ∨
               ∃h y.
                 is_valid_fp_body (NUMERAL (BIT1 n) − 1) h ∧
                 ∀g. f g x = do z <- g y; h g z od) ∧
        ∀n f.
          is_valid_fp_body (NUMERAL (BIT2 n)) f ⇔
          ∀x. (∀g h. f g x = f h x) ∨
              ∃h y.
                is_valid_fp_body (NUMERAL (BIT1 n)) h ∧
                ∀g. f g x = do z <- g y; h g z od
   
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
      
      ⊢ is_valid_fp_body (SUC (SUC 0)) nth_body
   
   [nth_body_is_valid_aux]  Theorem
      
      ⊢ is_valid_fp_body (SUC (SUC n)) nth_body
   
   [nth_def]  Theorem
      
      ⊢ ∀ls i.
          nth ls i =
          case ls of
            ListCons x tl =>
              if u32_to_int i = 0 then Return x
              else do i0 <- u32_sub i (int_to_u32 1); nth tl i0 od
          | ListNil => Fail Failure
   
   [odd_def]  Theorem
      
      ⊢ ∀i. odd i = if i = 0 then Return F else even (i − 1)
   
   
*)
end
