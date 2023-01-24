signature primitivesArithTheory =
sig
  type thm = Thm.thm
  
  (*  Theorems  *)
    val GE_EQ_LE : thm
    val GT_EQ_LT : thm
    val INT_OF_NUM_INJ : thm
    val LE_EQ_GE : thm
    val LT_EQ_GT : thm
    val NOT_GE_EQ_LT : thm
    val NOT_GT_EQ_LE : thm
    val NOT_LE_EQ_GT : thm
    val NOT_LT_EQ_GE : thm
    val NUM_SUB_1_EQ : thm
    val NUM_SUB_EQ : thm
    val POS_DIV_POS_IS_POS : thm
    val POS_DIV_POS_LE : thm
    val POS_DIV_POS_LE_INIT : thm
    val POS_MOD_POS_IS_POS : thm
    val POS_MOD_POS_LE_INIT : thm
    val POS_MUL_POS_IS_POS : thm
  
  val primitivesArith_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [Omega] Parent theory of "primitivesArith"
   
   [int_arith] Parent theory of "primitivesArith"
   
   [GE_EQ_LE]  Theorem
      
      ⊢ ∀x y. x ≥ y ⇔ y ≤ x
   
   [GT_EQ_LT]  Theorem
      
      ⊢ ∀x y. x > y ⇔ y < x
   
   [INT_OF_NUM_INJ]  Theorem
      
      ⊢ ∀n m. &n = &m ⇒ n = m
   
   [LE_EQ_GE]  Theorem
      
      ⊢ ∀x y. x ≤ y ⇔ y ≥ x
   
   [LT_EQ_GT]  Theorem
      
      ⊢ ∀x y. x < y ⇔ y > x
   
   [NOT_GE_EQ_LT]  Theorem
      
      ⊢ ∀x y. ¬(x ≥ y) ⇔ x < y
   
   [NOT_GT_EQ_LE]  Theorem
      
      ⊢ ∀x y. ¬(x > y) ⇔ x ≤ y
   
   [NOT_LE_EQ_GT]  Theorem
      
      ⊢ ∀x y. ¬(x ≤ y) ⇔ x > y
   
   [NOT_LT_EQ_GE]  Theorem
      
      ⊢ ∀x y. ¬(x < y) ⇔ x ≥ y
   
   [NUM_SUB_1_EQ]  Theorem
      
      ⊢ ∀x y. x = y − 1 ⇒ 0 ≤ x ⇒ Num y = SUC (Num x)
   
   [NUM_SUB_EQ]  Theorem
      
      ⊢ ∀x y z. x = y − z ⇒ 0 ≤ x ⇒ 0 ≤ z ⇒ Num y = Num z + Num x
   
   [POS_DIV_POS_IS_POS]  Theorem
      
      ⊢ ∀x y. 0 ≤ x ⇒ 0 < y ⇒ 0 ≤ x / y
   
   [POS_DIV_POS_LE]  Theorem
      
      ⊢ ∀x y d. 0 ≤ x ⇒ 0 ≤ y ⇒ 0 < d ⇒ x ≤ y ⇒ x / d ≤ y / d
   
   [POS_DIV_POS_LE_INIT]  Theorem
      
      ⊢ ∀x y. 0 ≤ x ⇒ 0 < y ⇒ x / y ≤ x
   
   [POS_MOD_POS_IS_POS]  Theorem
      
      ⊢ ∀x y. 0 ≤ x ⇒ 0 < y ⇒ 0 ≤ x % y
   
   [POS_MOD_POS_LE_INIT]  Theorem
      
      ⊢ ∀x y. 0 ≤ x ⇒ 0 < y ⇒ x % y ≤ x
   
   [POS_MUL_POS_IS_POS]  Theorem
      
      ⊢ ∀x y. 0 ≤ x ⇒ 0 ≤ y ⇒ 0 ≤ x * y
   
   
*)
end
