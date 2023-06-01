signature ilistTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val drop_def : thm
    val index_def : thm
    val len_def : thm
    val update_def : thm
  
  (*  Theorems  *)
    val append_len_eq : thm
    val drop_eq : thm
    val drop_more_than_length : thm
    val index_eq : thm
    val index_eq_EL : thm
    val len_append : thm
    val len_eq_LENGTH : thm
    val len_pos : thm
    val update_eq : thm
  
  val ilist_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [primitivesArith] Parent theory of "ilist"
   
   [drop_def]  Definition
      
      ⊢ (∀i. drop i [] = []) ∧
        ∀i x ls.
          drop i (x::ls) =
          if i < 0 then x::ls else if i = 0 then x::ls else drop (i − 1) ls
   
   [index_def]  Definition
      
      ⊢ ∀i x ls.
          index i (x::ls) =
          if i = 0 then x else if 0 < i then index (i − 1) ls else ARB
   
   [len_def]  Definition
      
      ⊢ len [] = 0 ∧ ∀x ls. len (x::ls) = 1 + len ls
   
   [update_def]  Definition
      
      ⊢ (∀i y. update [] i y = []) ∧
        ∀x ls i y.
          update (x::ls) i y =
          if i = 0 then y::ls
          else if 0 < i then x::update ls (i − 1) y
          else x::ls
   
   [append_len_eq]  Theorem
      
      ⊢ (∀l1 l2 l1' l2'.
           len l1 = len l1' ⇒ (l1 ⧺ l2 = l1' ⧺ l2' ⇔ l1 = l1' ∧ l2 = l2')) ∧
        ∀l1 l2 l1' l2'.
          len l2 = len l2' ⇒ (l1 ⧺ l2 = l1' ⧺ l2' ⇔ l1 = l1' ∧ l2 = l2')
   
   [drop_eq]  Theorem
      
      ⊢ (∀i. drop i [] = []) ∧ (∀ls. drop 0 ls = ls) ∧
        ∀i x ls.
          drop i (x::ls) =
          if 0 < i ∨ 0 ≤ i ∧ i ≠ 0 then drop (i − 1) ls else x::ls
   
   [drop_more_than_length]  Theorem
      
      ⊢ ∀ls i. len ls ≤ i ⇒ drop i ls = []
   
   [index_eq]  Theorem
      
      ⊢ (∀x ls. index 0 (x::ls) = x) ∧
        ∀i x ls.
          index i (x::ls) =
          if 0 < i ∨ 0 ≤ i ∧ i ≠ 0 then index (i − 1) ls
          else if i = 0 then x
          else ARB
   
   [index_eq_EL]  Theorem
      
      ⊢ ∀i ls. 0 ≤ i ⇒ i < len ls ⇒ index i ls = EL (Num i) ls
   
   [len_append]  Theorem
      
      ⊢ ∀l1 l2. len (l1 ⧺ l2) = len l1 + len l2
   
   [len_eq_LENGTH]  Theorem
      
      ⊢ ∀ls. len ls = &LENGTH ls
   
   [len_pos]  Theorem
      
      ⊢ ∀ls. 0 ≤ len ls
   
   [update_eq]  Theorem
      
      ⊢ (∀i y. update [] i y = []) ∧
        (∀x ls y. update (x::ls) 0 y = y::ls) ∧
        ∀x ls i y.
          update (x::ls) i y =
          if 0 < i ∨ 0 ≤ i ∧ i ≠ 0 then x::update ls (i − 1) y
          else if i < 0 then x::ls
          else y::ls
   
   
*)
end
