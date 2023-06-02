signature divDefNoFixLibTestTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val even___E_def : thm
    val even___P_def : thm
    val even___fuel0_UNION_extract0_def : thm
    val even___fuel0_UNION_extract1_def : thm
    val even___fuel0_UNION_primitive_def : thm
    val even___fuel_UNION_extract0_def : thm
    val even___fuel_UNION_extract1_def : thm
    val even___fuel_UNION_primitive_def : thm
    val even_def : thm
    val list_t_TY_DEF : thm
    val list_t_case_def : thm
    val list_t_size_def : thm
    val nth_mut_fwd___E_def : thm
    val nth_mut_fwd___P_def : thm
    val nth_mut_fwd_def : thm
    val odd___E_def : thm
    val odd___P_def : thm
    val odd_def : thm
  
  (*  Theorems  *)
    val datatype_list_t : thm
    val even___fuel0_def : thm
    val even___fuel0_ind : thm
    val even___fuel_def : thm
    val even___fuel_ind : thm
    val list_t_11 : thm
    val list_t_Axiom : thm
    val list_t_case_cong : thm
    val list_t_case_eq : thm
    val list_t_distinct : thm
    val list_t_induction : thm
    val list_t_nchotomy : thm
    val nth_mut_fwd___fuel0_def : thm
    val nth_mut_fwd___fuel0_ind : thm
    val nth_mut_fwd___fuel_def : thm
    val nth_mut_fwd___fuel_ind : thm
  
  val divDefNoFixLibTest_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [primitives] Parent theory of "divDefNoFixLibTest"
   
   [even___E_def]  Definition
      
      ⊢ ∀even odd i.
          even___E even odd i =
          if i = 0 then do b <- Return T; Return b od
          else do b <- odd (i − 1); Return b od
   
   [even___P_def]  Definition
      
      ⊢ ∀i $var$($n).
          even___P i $var$($n) ⇔ ¬is_diverge (even___fuel0 $var$($n) i)
   
   [even___fuel0_UNION_extract0_def]  Definition
      
      ⊢ ∀x x0. even___fuel0 x x0 = even___fuel0_UNION (INL (x,x0))
   
   [even___fuel0_UNION_extract1_def]  Definition
      
      ⊢ ∀x x0. odd___fuel0 x x0 = even___fuel0_UNION (INR (x,x0))
   
   [even___fuel0_UNION_primitive_def]  Definition
      
      ⊢ even___fuel0_UNION =
        WFREC
          (@R. WF R ∧
               (∀i $var$($n) $var$($m).
                  $var$($n) = SUC $var$($m) ∧ i ≠ 0 ⇒
                  R (INR ($var$($m),i − 1)) (INL ($var$($n),i))) ∧
               ∀i $var$($n) $var$($m).
                 $var$($n) = SUC $var$($m) ∧ i ≠ 0 ⇒
                 R (INL ($var$($m),i − 1)) (INR ($var$($n),i)))
          (λeven___fuel0_UNION a.
               case a of
                 INL ($var$($n),i) =>
                   I
                     (case $var$($n) of
                        0 => Diverge
                      | SUC $var$($m) =>
                        if i = 0 then do b <- Return T; Return b od
                        else
                          do
                            b <- even___fuel0_UNION (INR ($var$($m),i − 1));
                            Return b
                          od)
               | INR ($var$($n'),i') =>
                 I
                   (case $var$($n') of
                      0 => Diverge
                    | SUC $var$($m) =>
                      if i' = 0 then do b <- Return F; Return b od
                      else
                        do
                          b <- even___fuel0_UNION (INL ($var$($m),i' − 1));
                          Return b
                        od))
   
   [even___fuel_UNION_extract0_def]  Definition
      
      ⊢ ∀x x0. even___fuel x x0 = even___fuel_UNION (INL (x,x0))
   
   [even___fuel_UNION_extract1_def]  Definition
      
      ⊢ ∀x x0. odd___fuel x x0 = even___fuel_UNION (INR (x,x0))
   
   [even___fuel_UNION_primitive_def]  Definition
      
      ⊢ even___fuel_UNION =
        WFREC
          (@R. WF R ∧
               (∀i $var$($n) $var$($m).
                  $var$($n) = SUC $var$($m) ∧ i ≠ 0 ⇒
                  R (INR ($var$($m),i − 1)) (INL ($var$($n),i))) ∧
               ∀i $var$($n) $var$($m).
                 $var$($n) = SUC $var$($m) ∧ i ≠ 0 ⇒
                 R (INL ($var$($m),i − 1)) (INR ($var$($n),i)))
          (λeven___fuel_UNION a.
               case a of
                 INL ($var$($n),i) =>
                   I
                     (case $var$($n) of
                        0 => Diverge
                      | SUC $var$($m) =>
                        if i = 0 then Return T
                        else even___fuel_UNION (INR ($var$($m),i − 1)))
               | INR ($var$($n'),i') =>
                 I
                   (case $var$($n') of
                      0 => Diverge
                    | SUC $var$($m) =>
                      if i' = 0 then Return F
                      else even___fuel_UNION (INL ($var$($m),i' − 1))))
   
   [even_def]  Definition
      
      ⊢ ∀i. even i =
            if ∃ $var$($n). even___P i $var$($n) then
              even___fuel0 ($LEAST (even___P i)) i
            else Diverge
   
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
   
   [nth_mut_fwd___E_def]  Definition
      
      ⊢ ∀nth_mut_fwd ls i.
          nth_mut_fwd___E nth_mut_fwd ls i =
          case ls of
            ListCons x tl =>
              if u32_to_int i = 0 then Return x
              else
                do
                  i0 <- u32_sub i (int_to_u32 1);
                  x <- nth_mut_fwd tl i0;
                  Return x
                od
          | ListNil => Fail Failure
   
   [nth_mut_fwd___P_def]  Definition
      
      ⊢ ∀ls i $var$($n).
          nth_mut_fwd___P ls i $var$($n) ⇔
          ¬is_diverge (nth_mut_fwd___fuel0 $var$($n) ls i)
   
   [nth_mut_fwd_def]  Definition
      
      ⊢ ∀ls i.
          nth_mut_fwd ls i =
          if ∃ $var$($n). nth_mut_fwd___P ls i $var$($n) then
            nth_mut_fwd___fuel0 ($LEAST (nth_mut_fwd___P ls i)) ls i
          else Diverge
   
   [odd___E_def]  Definition
      
      ⊢ ∀even odd i.
          odd___E even odd i =
          if i = 0 then do b <- Return F; Return b od
          else do b <- even (i − 1); Return b od
   
   [odd___P_def]  Definition
      
      ⊢ ∀i $var$($n).
          odd___P i $var$($n) ⇔ ¬is_diverge (odd___fuel0 $var$($n) i)
   
   [odd_def]  Definition
      
      ⊢ ∀i. odd i =
            if ∃ $var$($n). odd___P i $var$($n) then
              odd___fuel0 ($LEAST (odd___P i)) i
            else Diverge
   
   [datatype_list_t]  Theorem
      
      ⊢ DATATYPE (list_t ListCons ListNil)
   
   [even___fuel0_def]  Theorem
      
      ⊢ (∀i $var$($n).
           even___fuel0 $var$($n) i =
           case $var$($n) of
             0 => Diverge
           | SUC $var$($m) =>
             if i = 0 then do b <- Return T; Return b od
             else do b <- odd___fuel0 $var$($m) (i − 1); Return b od) ∧
        ∀i $var$($n).
          odd___fuel0 $var$($n) i =
          case $var$($n) of
            0 => Diverge
          | SUC $var$($m) =>
            if i = 0 then do b <- Return F; Return b od
            else do b <- even___fuel0 $var$($m) (i − 1); Return b od
   
   [even___fuel0_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀ $var$($n) i.
             (∀ $var$($m).
                $var$($n) = SUC $var$($m) ∧ i ≠ 0 ⇒ P1 $var$($m) (i − 1)) ⇒
             P0 $var$($n) i) ∧
          (∀ $var$($n) i.
             (∀ $var$($m).
                $var$($n) = SUC $var$($m) ∧ i ≠ 0 ⇒ P0 $var$($m) (i − 1)) ⇒
             P1 $var$($n) i) ⇒
          (∀v0 v1. P0 v0 v1) ∧ ∀v0 v1. P1 v0 v1
   
   [even___fuel_def]  Theorem
      
      ⊢ (∀i $var$($n).
           even___fuel $var$($n) i =
           case $var$($n) of
             0 => Diverge
           | SUC $var$($m) =>
             if i = 0 then Return T else odd___fuel $var$($m) (i − 1)) ∧
        ∀i $var$($n).
          odd___fuel $var$($n) i =
          case $var$($n) of
            0 => Diverge
          | SUC $var$($m) =>
            if i = 0 then Return F else even___fuel $var$($m) (i − 1)
   
   [even___fuel_ind]  Theorem
      
      ⊢ ∀P0 P1.
          (∀ $var$($n) i.
             (∀ $var$($m).
                $var$($n) = SUC $var$($m) ∧ i ≠ 0 ⇒ P1 $var$($m) (i − 1)) ⇒
             P0 $var$($n) i) ∧
          (∀ $var$($n) i.
             (∀ $var$($m).
                $var$($n) = SUC $var$($m) ∧ i ≠ 0 ⇒ P0 $var$($m) (i − 1)) ⇒
             P1 $var$($n) i) ⇒
          (∀v0 v1. P0 v0 v1) ∧ ∀v0 v1. P1 v0 v1
   
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
   
   [nth_mut_fwd___fuel0_def]  Theorem
      
      ⊢ ∀ls i $var$($n).
          nth_mut_fwd___fuel0 $var$($n) ls i =
          case $var$($n) of
            0 => Diverge
          | SUC $var$($m) =>
            case ls of
              ListCons x tl =>
                if u32_to_int i = 0 then Return x
                else
                  do
                    i0 <- u32_sub i (int_to_u32 1);
                    x <- nth_mut_fwd___fuel0 $var$($m) tl i0;
                    Return x
                  od
            | ListNil => Fail Failure
   
   [nth_mut_fwd___fuel0_ind]  Theorem
      
      ⊢ ∀P. (∀ $var$($n) ls i.
               (∀ $var$($m) x tl i0.
                  $var$($n) = SUC $var$($m) ∧ ls = ListCons x tl ∧
                  u32_to_int i ≠ 0 ⇒
                  P $var$($m) tl i0) ⇒
               P $var$($n) ls i) ⇒
            ∀v v1 v2. P v v1 v2
   
   [nth_mut_fwd___fuel_def]  Theorem
      
      ⊢ ∀ls i $var$($n).
          nth_mut_fwd___fuel $var$($n) ls i =
          case $var$($n) of
            0 => Diverge
          | SUC $var$($m) =>
            case ls of
              ListCons x tl =>
                if u32_to_int i = 0 then Return x
                else
                  do
                    i0 <- u32_sub i (int_to_u32 1);
                    nth_mut_fwd___fuel $var$($m) tl i0
                  od
            | ListNil => Fail Failure
   
   [nth_mut_fwd___fuel_ind]  Theorem
      
      ⊢ ∀P. (∀ $var$($n) ls i.
               (∀ $var$($m) x tl i0.
                  $var$($n) = SUC $var$($m) ∧ ls = ListCons x tl ∧
                  u32_to_int i ≠ 0 ⇒
                  P $var$($m) tl i0) ⇒
               P $var$($n) ls i) ⇒
            ∀v v1 v2. P v v1 v2
   
   
*)
end
