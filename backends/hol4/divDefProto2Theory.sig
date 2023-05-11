signature divDefProto2Theory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val fix_def : thm
    val fix_fuel_P_def : thm
    val fix_fuel_def : thm
    val ftree_TY_DEF : thm
    val ftree_case_def : thm
    val ftree_size_def : thm
    val is_valid_fp_body_def : thm
  
  (*  Theorems  *)
    val datatype_ftree : thm
    val eval_ftree_compute : thm
    val eval_ftree_def : thm
    val eval_ftree_ind : thm
    val fix_fuel_compute : thm
    val ftree_11 : thm
    val ftree_Axiom : thm
    val ftree_case_cong : thm
    val ftree_case_eq : thm
    val ftree_distinct : thm
    val ftree_induction : thm
    val ftree_nchotomy : thm
    val ftree_size_eq : thm
  
  val divDefProto2_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [primitives] Parent theory of "divDefProto2"
   
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
   
   [ftree_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('ftree') $var$('@temp @ind_typedivDefProto20prod')
                     $var$('@temp @ind_typedivDefProto21list').
                   (∀a0'.
                      (∃a. a0' =
                           (λa.
                                ind_type$CONSTR 0 (ARB,ARB)
                                  (ind_type$FCONS a (λn. ind_type$BOTTOM)))
                             a ∧
                           $var$('@temp @ind_typedivDefProto20prod') a) ∨
                      (∃a. a0' =
                           (λa.
                                ind_type$CONSTR (SUC 0) (a,ARB)
                                  (λn. ind_type$BOTTOM)) a) ⇒
                      $var$('ftree') a0') ∧
                   (∀a1'.
                      (∃a0 a1.
                         a1' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC 0)) (ARB,a0)
                                (ind_type$FCONS a1 (λn. ind_type$BOTTOM)))
                           a0 a1 ∧
                         $var$('@temp @ind_typedivDefProto21list') a1) ⇒
                      $var$('@temp @ind_typedivDefProto20prod') a1') ∧
                   (∀a2.
                      a2 =
                      ind_type$CONSTR (SUC (SUC (SUC 0))) (ARB,ARB)
                        (λn. ind_type$BOTTOM) ∨
                      (∃a0 a1.
                         a2 =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC (SUC (SUC 0))))
                                (ARB,ARB)
                                (ind_type$FCONS a0
                                   (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                           a0 a1 ∧ $var$('ftree') a0 ∧
                         $var$('@temp @ind_typedivDefProto21list') a1) ⇒
                      $var$('@temp @ind_typedivDefProto21list') a2) ⇒
                   $var$('ftree') a0') rep
   
   [ftree_case_def]  Definition
      
      ⊢ (∀a f f1. ftree_CASE (Rec a) f f1 = f a) ∧
        ∀a f f1. ftree_CASE (NRec a) f f1 = f1 a
   
   [ftree_size_def]  Definition
      
      ⊢ (∀f a. ftree_size f (Rec a) = 1 + ftree1_size f a) ∧
        (∀f a. ftree_size f (NRec a) = 1) ∧
        (∀f a0 a1. ftree1_size f (a0,a1) = 1 + ftree2_size f a1) ∧
        (∀f. ftree2_size f [] = 0) ∧
        ∀f a0 a1.
          ftree2_size f (a0::a1) = 1 + (ftree_size f a0 + ftree2_size f a1)
   
   [is_valid_fp_body_def]  Definition
      
      ⊢ ∀f. is_valid_fp_body f ⇔ ∀x. ∃n ft. ∀g. f g x = eval_ftree n g ft
   
   [datatype_ftree]  Theorem
      
      ⊢ DATATYPE (ftree Rec NRec)
   
   [eval_ftree_compute]  Theorem
      
      ⊢ (∀x g fs. eval_ftree 0 g (fs,x) = Diverge) ∧
        (∀x n g fs.
           eval_ftree (NUMERAL (BIT1 n)) g (fs,x) =
           case x of
             INL r => r
           | INR (y,i) =>
             case g y of
               Return z =>
                 (let
                    f = EL i fs
                  in
                    eval_ftree (NUMERAL (BIT1 n) − 1) g (fs,f z))
             | Fail e => Fail e
             | Diverge => Diverge) ∧
        ∀x n g fs.
          eval_ftree (NUMERAL (BIT2 n)) g (fs,x) =
          case x of
            INL r => r
          | INR (y,i) =>
            case g y of
              Return z =>
                (let
                   f = EL i fs
                 in
                   eval_ftree (NUMERAL (BIT1 n)) g (fs,f z))
            | Fail e => Fail e
            | Diverge => Diverge
   
   [eval_ftree_def]  Theorem
      
      ⊢ (∀x g fs. eval_ftree 0 g (fs,x) = Diverge) ∧
        ∀x n g fs.
          eval_ftree (SUC n) g (fs,x) =
          case x of
            INL r => r
          | INR (y,i) =>
            case g y of
              Return z => (let f = EL i fs in eval_ftree n g (fs,f z))
            | Fail e => Fail e
            | Diverge => Diverge
   
   [eval_ftree_ind]  Theorem
      
      ⊢ ∀P. (∀g fs x. P 0 g (fs,x)) ∧
            (∀n g fs x.
               (∀v1 y i z f.
                  x = INR v1 ∧ v1 = (y,i) ∧ g y = Return z ∧ f = EL i fs ⇒
                  P n g (fs,f z)) ⇒
               P (SUC n) g (fs,x)) ⇒
            ∀v v1 v2 v3. P v v1 (v2,v3)
   
   [fix_fuel_compute]  Theorem
      
      ⊢ (∀f x. fix_fuel 0 f x = Diverge) ∧
        (∀n f x.
           fix_fuel (NUMERAL (BIT1 n)) f x =
           f (fix_fuel (NUMERAL (BIT1 n) − 1) f) x) ∧
        ∀n f x.
          fix_fuel (NUMERAL (BIT2 n)) f x =
          f (fix_fuel (NUMERAL (BIT1 n)) f) x
   
   [ftree_11]  Theorem
      
      ⊢ (∀a a'. Rec a = Rec a' ⇔ a = a') ∧ ∀a a'. NRec a = NRec a' ⇔ a = a'
   
   [ftree_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3 f4. ∃fn0 fn1 fn2.
          (∀a. fn0 (Rec a) = f0 a (fn1 a)) ∧ (∀a. fn0 (NRec a) = f1 a) ∧
          (∀a0 a1. fn1 (a0,a1) = f2 a0 a1 (fn2 a1)) ∧ fn2 [] = f3 ∧
          ∀a0 a1. fn2 (a0::a1) = f4 a0 a1 (fn0 a0) (fn2 a1)
   
   [ftree_case_cong]  Theorem
      
      ⊢ ∀M M' f f1.
          M = M' ∧ (∀a. M' = Rec a ⇒ f a = f' a) ∧
          (∀a. M' = NRec a ⇒ f1 a = f1' a) ⇒
          ftree_CASE M f f1 = ftree_CASE M' f' f1'
   
   [ftree_case_eq]  Theorem
      
      ⊢ ftree_CASE x f f1 = v ⇔
        (∃p. x = Rec p ∧ f p = v) ∨ ∃f'. x = NRec f' ∧ f1 f' = v
   
   [ftree_distinct]  Theorem
      
      ⊢ ∀a' a. Rec a ≠ NRec a'
   
   [ftree_induction]  Theorem
      
      ⊢ ∀P0 P1 P2.
          (∀p. P1 p ⇒ P0 (Rec p)) ∧ (∀f. P0 (NRec f)) ∧
          (∀l. P2 l ⇒ ∀f. P1 (f,l)) ∧ P2 [] ∧
          (∀f l. P0 f ∧ P2 l ⇒ P2 (f::l)) ⇒
          (∀f. P0 f) ∧ (∀p. P1 p) ∧ ∀l. P2 l
   
   [ftree_nchotomy]  Theorem
      
      ⊢ ∀ff. (∃p. ff = Rec p) ∨ ∃f. ff = NRec f
   
   [ftree_size_eq]  Theorem
      
      ⊢ ftree1_size f = pair_size (λv. 0) (list_size (ftree_size f)) ∧
        ftree2_size f = list_size (ftree_size f)
   
   
*)
end
