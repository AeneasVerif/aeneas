signature divDefTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val fix_def : thm
    val fix_exec_def : thm
    val fix_fuel_P_def : thm
    val fix_fuel_def : thm
    val fix_nexec_def : thm
    val is_valid_fp_body_def : thm
  
  (*  Theorems  *)
    val case_result_switch_eq : thm
    val fix_exec_fixed_eq : thm
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
    val fix_nexec_eq_fix : thm
    val fix_not_diverge_implies_fix_fuel : thm
    val fix_not_diverge_implies_fix_fuel_aux : thm
    val is_valid_fp_body_compute : thm
  
  val divDef_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [primitives] Parent theory of "divDef"
   
   [fix_def]  Definition
      
      ⊢ ∀f x.
          fix f x =
          if ∃n. fix_fuel_P f x n then
            fix_fuel ($LEAST (fix_fuel_P f x)) f x
          else Diverge
   
   [fix_exec_def]  Definition
      
      ⊢ fix_exec = fix_nexec 1000000
   
   [fix_fuel_P_def]  Definition
      
      ⊢ ∀f x n. fix_fuel_P f x n ⇔ ¬is_diverge (fix_fuel n f x)
   
   [fix_fuel_def]  Definition
      
      ⊢ (∀f x. fix_fuel 0 f x = Diverge) ∧
        ∀n f x. fix_fuel (SUC n) f x = f (fix_fuel n f) x
   
   [fix_nexec_def]  Definition
      
      ⊢ ∀n f x.
          fix_nexec n f x =
          if fix_fuel_P f x n then fix_fuel n f x else fix f x
   
   [is_valid_fp_body_def]  Definition
      
      ⊢ (∀f. is_valid_fp_body 0 f ⇔ F) ∧
        ∀n f.
          is_valid_fp_body (SUC n) f ⇔
          ∀x. (∀g h. f g x = f h x) ∨
              ∃h y.
                is_valid_fp_body n h ∧ ∀g. f g x = do z <- g y; h g z od
   
   [case_result_switch_eq]  Theorem
      
      ⊢ (case
           case x of
             Return y => f y
           | Fail e => Fail e
           | Diverge => Diverge
         of
           Return y => g y
         | Fail e => Fail e
         | Diverge => Diverge) =
        case x of
          Return y =>
            (case f y of
               Return y => g y
             | Fail e => Fail e
             | Diverge => Diverge)
        | Fail e => Fail e
        | Diverge => Diverge
   
   [fix_exec_fixed_eq]  Theorem
      
      ⊢ ∀N f. is_valid_fp_body N f ⇒ ∀x. fix_exec f x = f (fix_exec f) x
   
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
   
   [fix_nexec_eq_fix]  Theorem
      
      ⊢ ∀N f n. is_valid_fp_body N f ⇒ fix_nexec n f = fix f
   
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
   
   
*)
end
