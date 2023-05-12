signature divDefExampleTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val even_odd_body_def : thm
    val list_t_TY_DEF : thm
    val list_t_case_def : thm
    val list_t_size_def : thm
    val nth_body_def : thm
  
  (*  Theorems  *)
    val datatype_list_t : thm
    val even_def : thm
    val even_odd_body_is_valid : thm
    val even_odd_body_is_valid_aux : thm
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
  
  val divDefExample_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [divDef] Parent theory of "divDefExample"
   
   [even_odd_body_def]  Definition
      
      ⊢ ∀f x.
          even_odd_body f x =
          case x of
            INL 0 => Return (INR (INL T))
          | INL i =>
            (case f (INR (INR (INL (i − 1)))) of
               Return (INL v) => Fail Failure
             | Return (INR (INL v2)) => Fail Failure
             | Return (INR (INR (INL v4))) => Fail Failure
             | Return (INR (INR (INR b))) => Return (INR (INL b))
             | Fail e => Fail e
             | Diverge => Diverge)
          | INR (INL v8) => Fail Failure
          | INR (INR (INL 0)) => Return (INR (INR (INR F)))
          | INR (INR (INL i')) =>
            (case f (INL (i' − 1)) of
               Return (INL v) => Fail Failure
             | Return (INR (INL b)) => Return (INR (INR (INR b)))
             | Return (INR (INR v3)) => Fail Failure
             | Fail e => Fail e
             | Diverge => Diverge)
          | INR (INR (INR v11)) => Fail Failure
   
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
                         x <-
                           case f (INL (tl,i0)) of
                             Return (INL v) => Fail Failure
                           | Return (INR x) => Return x
                           | Fail e => Fail e
                           | Diverge => Diverge;
                         Return (INR x)
                       od
                 | ListNil => Fail Failure)
          | INR v3 => Fail Failure
   
   [datatype_list_t]  Theorem
      
      ⊢ DATATYPE (list_t ListCons ListNil)
   
   [even_def]  Theorem
      
      ⊢ ∀i. even i = if i = 0 then Return T else odd (i − 1)
   
   [even_odd_body_is_valid]  Theorem
      
      ⊢ is_valid_fp_body (SUC (SUC 0)) even_odd_body
   
   [even_odd_body_is_valid_aux]  Theorem
      
      ⊢ is_valid_fp_body (SUC (SUC n)) even_odd_body
   
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
