signature primitivesArithTheory =
sig
  type thm = Thm.thm
  
  (*  Theorems  *)
    val add_sub_same_eq : thm
    val ge_eq_le : thm
    val gt_eq_lt : thm
    val int_add : thm
    val int_induction : thm
    val int_induction_ideal : thm
    val int_of_num_id : thm
    val int_of_num_inj : thm
    val le_eq_ge : thm
    val lt_eq_gt : thm
    val not_ge_eq_lt : thm
    val not_gt_eq_le : thm
    val not_le_eq_gt : thm
    val not_lt_eq_ge : thm
    val num_sub_1_eq : thm
    val num_sub_eq : thm
    val pos_div_pos_is_pos : thm
    val pos_div_pos_le : thm
    val pos_div_pos_le_init : thm
    val pos_mod_pos_is_pos : thm
    val pos_mod_pos_le_init : thm
    val pos_mul_pos_is_pos : thm
  
  val primitivesArith_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Omega] Parent theory of "primitivesArith"
   
   [int_arith] Parent theory of "primitivesArith"
   
   [add_sub_same_eq]  Theorem
      
      ⊢ ∀i j. i + j − j = i
   
   [ge_eq_le]  Theorem
      
      ⊢ ∀x y. x ≥ y ⇔ y ≤ x
   
   [gt_eq_lt]  Theorem
      
      ⊢ ∀x y. x > y ⇔ y < x
   
   [int_add]  Theorem
      
      ⊢ ∀m n. &(m + n) = &m + &n
   
   [int_induction]  Theorem
      
      ⊢ ∀P. (∀i. i < 0 ⇒ P i) ∧ P 0 ∧ (∀i. P i ⇒ P (i + 1)) ⇒ ∀i. P i
   
   [int_induction_ideal]  Theorem
      
      ⊢ ∀P. P 0 ∧ (∀i. 0 ≤ i ∧ P i ⇒ P (i + 1)) ⇒ ∀i. 0 ≤ i ⇒ P i
   
   [int_of_num_id]  Theorem
      
      ⊢ ∀i. 0 ≤ i ⇒ &Num i = i
   
   [int_of_num_inj]  Theorem
      
      ⊢ ∀n m. &n = &m ⇒ n = m
   
   [le_eq_ge]  Theorem
      
      ⊢ ∀x y. x ≤ y ⇔ y ≥ x
   
   [lt_eq_gt]  Theorem
      
      ⊢ ∀x y. x < y ⇔ y > x
   
   [not_ge_eq_lt]  Theorem
      
      ⊢ ∀x y. ¬(x ≥ y) ⇔ x < y
   
   [not_gt_eq_le]  Theorem
      
      ⊢ ∀x y. ¬(x > y) ⇔ x ≤ y
   
   [not_le_eq_gt]  Theorem
      
      ⊢ ∀x y. ¬(x ≤ y) ⇔ x > y
   
   [not_lt_eq_ge]  Theorem
      
      ⊢ ∀x y. ¬(x < y) ⇔ x ≥ y
   
   [num_sub_1_eq]  Theorem
      
      ⊢ ∀x y. x = y − 1 ⇒ 0 ≤ x ⇒ Num y = SUC (Num x)
   
   [num_sub_eq]  Theorem
      
      ⊢ ∀x y z. x = y − z ⇒ 0 ≤ x ⇒ 0 ≤ z ⇒ Num y = Num z + Num x
   
   [pos_div_pos_is_pos]  Theorem
      
      ⊢ ∀x y. 0 ≤ x ⇒ 0 < y ⇒ 0 ≤ x / y
   
   [pos_div_pos_le]  Theorem
      
      ⊢ ∀x y d. 0 ≤ x ⇒ 0 ≤ y ⇒ 0 < d ⇒ x ≤ y ⇒ x / d ≤ y / d
   
   [pos_div_pos_le_init]  Theorem
      
      ⊢ ∀x y. 0 ≤ x ⇒ 0 < y ⇒ x / y ≤ x
   
   [pos_mod_pos_is_pos]  Theorem
      
      ⊢ ∀x y. 0 ≤ x ⇒ 0 < y ⇒ 0 ≤ x % y
   
   [pos_mod_pos_le_init]  Theorem
      
      ⊢ ∀x y. 0 ≤ x ⇒ 0 < y ⇒ x % y ≤ x
   
   [pos_mul_pos_is_pos]  Theorem
      
      ⊢ ∀x y. 0 ≤ x ⇒ 0 ≤ y ⇒ 0 ≤ x * y
   
   
*)
end
