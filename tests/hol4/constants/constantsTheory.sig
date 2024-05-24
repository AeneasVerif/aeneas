signature constantsTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val add_fwd_def : thm
    val get_z1_fwd_def : thm
    val get_z1_z1_body_def : thm
    val get_z1_z1_c_def : thm
    val get_z2_fwd_def : thm
    val incr_fwd_def : thm
    val mk_pair0_fwd_def : thm
    val mk_pair1_fwd_def : thm
    val p0_body_def : thm
    val p0_c_def : thm
    val p1_body_def : thm
    val p1_c_def : thm
    val p2_body_def : thm
    val p2_c_def : thm
    val p3_body_def : thm
    val p3_c_def : thm
    val pair_t_TY_DEF : thm
    val pair_t_case_def : thm
    val pair_t_pair_x : thm
    val pair_t_pair_x_fupd : thm
    val pair_t_pair_y : thm
    val pair_t_pair_y_fupd : thm
    val pair_t_size_def : thm
    val q1_body_def : thm
    val q1_c_def : thm
    val q2_body_def : thm
    val q2_c_def : thm
    val q3_body_def : thm
    val q3_c_def : thm
    val s1_body_def : thm
    val s1_c_def : thm
    val s2_body_def : thm
    val s2_c_def : thm
    val s3_body_def : thm
    val s3_c_def : thm
    val s4_body_def : thm
    val s4_c_def : thm
    val unwrap_y_fwd_def : thm
    val wrap_new_fwd_def : thm
    val wrap_t_TY_DEF : thm
    val wrap_t_case_def : thm
    val wrap_t_size_def : thm
    val wrap_t_wrap_val : thm
    val wrap_t_wrap_val_fupd : thm
    val x0_body_def : thm
    val x0_c_def : thm
    val x1_body_def : thm
    val x1_c_def : thm
    val x2_body_def : thm
    val x2_c_def : thm
    val x3_body_def : thm
    val x3_c_def : thm
    val y_body_def : thm
    val y_c_def : thm
    val yval_body_def : thm
    val yval_c_def : thm
  
  (*  Theorems  *)
    val EXISTS_pair_t : thm
    val EXISTS_wrap_t : thm
    val FORALL_pair_t : thm
    val FORALL_wrap_t : thm
    val datatype_pair_t : thm
    val datatype_wrap_t : thm
    val pair_t_11 : thm
    val pair_t_Axiom : thm
    val pair_t_accessors : thm
    val pair_t_accfupds : thm
    val pair_t_case_cong : thm
    val pair_t_case_eq : thm
    val pair_t_component_equality : thm
    val pair_t_fn_updates : thm
    val pair_t_fupdcanon : thm
    val pair_t_fupdcanon_comp : thm
    val pair_t_fupdfupds : thm
    val pair_t_fupdfupds_comp : thm
    val pair_t_induction : thm
    val pair_t_literal_11 : thm
    val pair_t_literal_nchotomy : thm
    val pair_t_nchotomy : thm
    val pair_t_updates_eq_literal : thm
    val wrap_t_11 : thm
    val wrap_t_Axiom : thm
    val wrap_t_accessors : thm
    val wrap_t_accfupds : thm
    val wrap_t_case_cong : thm
    val wrap_t_case_eq : thm
    val wrap_t_component_equality : thm
    val wrap_t_fn_updates : thm
    val wrap_t_fupdfupds : thm
    val wrap_t_fupdfupds_comp : thm
    val wrap_t_induction : thm
    val wrap_t_literal_11 : thm
    val wrap_t_literal_nchotomy : thm
    val wrap_t_nchotomy : thm
    val wrap_t_updates_eq_literal : thm
  
  val constants_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [divDef] Parent theory of "constants"
   
   [add_fwd_def]  Definition
      
      ⊢ ∀a b. add_fwd a b = i32_add a b
   
   [get_z1_fwd_def]  Definition
      
      ⊢ get_z1_fwd = Return get_z1_z1_c
   
   [get_z1_z1_body_def]  Definition
      
      ⊢ get_z1_z1_body = Return (int_to_i32 3)
   
   [get_z1_z1_c_def]  Definition
      
      ⊢ get_z1_z1_c = get_return_value get_z1_z1_body
   
   [get_z2_fwd_def]  Definition
      
      ⊢ get_z2_fwd =
        do i <- get_z1_fwd; i0 <- add_fwd i q3_c; add_fwd q1_c i0 od
   
   [incr_fwd_def]  Definition
      
      ⊢ ∀n. incr_fwd n = u32_add n (int_to_u32 1)
   
   [mk_pair0_fwd_def]  Definition
      
      ⊢ ∀x y. mk_pair0_fwd x y = Return (x,y)
   
   [mk_pair1_fwd_def]  Definition
      
      ⊢ ∀x y. mk_pair1_fwd x y = Return <|pair_x := x; pair_y := y|>
   
   [p0_body_def]  Definition
      
      ⊢ p0_body = mk_pair0_fwd (int_to_u32 0) (int_to_u32 1)
   
   [p0_c_def]  Definition
      
      ⊢ p0_c = get_return_value p0_body
   
   [p1_body_def]  Definition
      
      ⊢ p1_body = mk_pair1_fwd (int_to_u32 0) (int_to_u32 1)
   
   [p1_c_def]  Definition
      
      ⊢ p1_c = get_return_value p1_body
   
   [p2_body_def]  Definition
      
      ⊢ p2_body = Return (int_to_u32 0,int_to_u32 1)
   
   [p2_c_def]  Definition
      
      ⊢ p2_c = get_return_value p2_body
   
   [p3_body_def]  Definition
      
      ⊢ p3_body = Return <|pair_x := int_to_u32 0; pair_y := int_to_u32 1|>
   
   [p3_c_def]  Definition
      
      ⊢ p3_c = get_return_value p3_body
   
   [pair_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('pair_t').
                   (∀a0'.
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR 0 (a0,a1)
                                (λn. ind_type$BOTTOM)) a0 a1) ⇒
                      $var$('pair_t') a0') ⇒
                   $var$('pair_t') a0') rep
   
   [pair_t_case_def]  Definition
      
      ⊢ ∀a0 a1 f. pair_t_CASE (pair_t a0 a1) f = f a0 a1
   
   [pair_t_pair_x]  Definition
      
      ⊢ ∀t t0. (pair_t t t0).pair_x = t
   
   [pair_t_pair_x_fupd]  Definition
      
      ⊢ ∀f t t0. pair_t t t0 with pair_x updated_by f = pair_t (f t) t0
   
   [pair_t_pair_y]  Definition
      
      ⊢ ∀t t0. (pair_t t t0).pair_y = t0
   
   [pair_t_pair_y_fupd]  Definition
      
      ⊢ ∀f t t0. pair_t t t0 with pair_y updated_by f = pair_t t (f t0)
   
   [pair_t_size_def]  Definition
      
      ⊢ ∀f f1 a0 a1. pair_t_size f f1 (pair_t a0 a1) = 1 + (f a0 + f1 a1)
   
   [q1_body_def]  Definition
      
      ⊢ q1_body = Return (int_to_i32 5)
   
   [q1_c_def]  Definition
      
      ⊢ q1_c = get_return_value q1_body
   
   [q2_body_def]  Definition
      
      ⊢ q2_body = Return q1_c
   
   [q2_c_def]  Definition
      
      ⊢ q2_c = get_return_value q2_body
   
   [q3_body_def]  Definition
      
      ⊢ q3_body = add_fwd q2_c (int_to_i32 3)
   
   [q3_c_def]  Definition
      
      ⊢ q3_c = get_return_value q3_body
   
   [s1_body_def]  Definition
      
      ⊢ s1_body = Return (int_to_u32 6)
   
   [s1_c_def]  Definition
      
      ⊢ s1_c = get_return_value s1_body
   
   [s2_body_def]  Definition
      
      ⊢ s2_body = incr_fwd s1_c
   
   [s2_c_def]  Definition
      
      ⊢ s2_c = get_return_value s2_body
   
   [s3_body_def]  Definition
      
      ⊢ s3_body = Return p3_c
   
   [s3_c_def]  Definition
      
      ⊢ s3_c = get_return_value s3_body
   
   [s4_body_def]  Definition
      
      ⊢ s4_body = mk_pair1_fwd (int_to_u32 7) (int_to_u32 8)
   
   [s4_c_def]  Definition
      
      ⊢ s4_c = get_return_value s4_body
   
   [unwrap_y_fwd_def]  Definition
      
      ⊢ unwrap_y_fwd = Return y_c.wrap_val
   
   [wrap_new_fwd_def]  Definition
      
      ⊢ ∀val. wrap_new_fwd val = Return <|wrap_val := val|>
   
   [wrap_t_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0.
                 ∀ $var$('wrap_t').
                   (∀a0.
                      (∃a. a0 =
                           (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                             a) ⇒
                      $var$('wrap_t') a0) ⇒
                   $var$('wrap_t') a0) rep
   
   [wrap_t_case_def]  Definition
      
      ⊢ ∀a f. wrap_t_CASE (wrap_t a) f = f a
   
   [wrap_t_size_def]  Definition
      
      ⊢ ∀f a. wrap_t_size f (wrap_t a) = 1 + f a
   
   [wrap_t_wrap_val]  Definition
      
      ⊢ ∀t. (wrap_t t).wrap_val = t
   
   [wrap_t_wrap_val_fupd]  Definition
      
      ⊢ ∀f t. wrap_t t with wrap_val updated_by f = wrap_t (f t)
   
   [x0_body_def]  Definition
      
      ⊢ x0_body = Return (int_to_u32 0)
   
   [x0_c_def]  Definition
      
      ⊢ x0_c = get_return_value x0_body
   
   [x1_body_def]  Definition
      
      ⊢ x1_body = Return core_u32_max
   
   [x1_c_def]  Definition
      
      ⊢ x1_c = get_return_value x1_body
   
   [x2_body_def]  Definition
      
      ⊢ x2_body = Return (int_to_u32 3)
   
   [x2_c_def]  Definition
      
      ⊢ x2_c = get_return_value x2_body
   
   [x3_body_def]  Definition
      
      ⊢ x3_body = incr_fwd (int_to_u32 32)
   
   [x3_c_def]  Definition
      
      ⊢ x3_c = get_return_value x3_body
   
   [y_body_def]  Definition
      
      ⊢ y_body = wrap_new_fwd (int_to_i32 2)
   
   [y_c_def]  Definition
      
      ⊢ y_c = get_return_value y_body
   
   [yval_body_def]  Definition
      
      ⊢ yval_body = unwrap_y_fwd
   
   [yval_c_def]  Definition
      
      ⊢ yval_c = get_return_value yval_body
   
   [EXISTS_pair_t]  Theorem
      
      ⊢ ∀P. (∃p. P p) ⇔ ∃t0 t. P <|pair_x := t0; pair_y := t|>
   
   [EXISTS_wrap_t]  Theorem
      
      ⊢ ∀P. (∃w. P w) ⇔ ∃u. P <|wrap_val := u|>
   
   [FORALL_pair_t]  Theorem
      
      ⊢ ∀P. (∀p. P p) ⇔ ∀t0 t. P <|pair_x := t0; pair_y := t|>
   
   [FORALL_wrap_t]  Theorem
      
      ⊢ ∀P. (∀w. P w) ⇔ ∀u. P <|wrap_val := u|>
   
   [datatype_pair_t]  Theorem
      
      ⊢ DATATYPE (record pair_t pair_x pair_y)
   
   [datatype_wrap_t]  Theorem
      
      ⊢ DATATYPE (record wrap_t wrap_val)
   
   [pair_t_11]  Theorem
      
      ⊢ ∀a0 a1 a0' a1'. pair_t a0 a1 = pair_t a0' a1' ⇔ a0 = a0' ∧ a1 = a1'
   
   [pair_t_Axiom]  Theorem
      
      ⊢ ∀f. ∃fn. ∀a0 a1. fn (pair_t a0 a1) = f a0 a1
   
   [pair_t_accessors]  Theorem
      
      ⊢ (∀t t0. (pair_t t t0).pair_x = t) ∧
        ∀t t0. (pair_t t t0).pair_y = t0
   
   [pair_t_accfupds]  Theorem
      
      ⊢ (∀p f. (p with pair_y updated_by f).pair_x = p.pair_x) ∧
        (∀p f. (p with pair_x updated_by f).pair_y = p.pair_y) ∧
        (∀p f. (p with pair_x updated_by f).pair_x = f p.pair_x) ∧
        ∀p f. (p with pair_y updated_by f).pair_y = f p.pair_y
   
   [pair_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧ (∀a0 a1. M' = pair_t a0 a1 ⇒ f a0 a1 = f' a0 a1) ⇒
          pair_t_CASE M f = pair_t_CASE M' f'
   
   [pair_t_case_eq]  Theorem
      
      ⊢ pair_t_CASE x f = v ⇔ ∃t t0. x = pair_t t t0 ∧ f t t0 = v
   
   [pair_t_component_equality]  Theorem
      
      ⊢ ∀p1 p2. p1 = p2 ⇔ p1.pair_x = p2.pair_x ∧ p1.pair_y = p2.pair_y
   
   [pair_t_fn_updates]  Theorem
      
      ⊢ (∀f t t0. pair_t t t0 with pair_x updated_by f = pair_t (f t) t0) ∧
        ∀f t t0. pair_t t t0 with pair_y updated_by f = pair_t t (f t0)
   
   [pair_t_fupdcanon]  Theorem
      
      ⊢ ∀p g f.
          p with <|pair_y updated_by f; pair_x updated_by g|> =
          p with <|pair_x updated_by g; pair_y updated_by f|>
   
   [pair_t_fupdcanon_comp]  Theorem
      
      ⊢ (∀g f.
           pair_y_fupd f ∘ pair_x_fupd g = pair_x_fupd g ∘ pair_y_fupd f) ∧
        ∀h g f.
          pair_y_fupd f ∘ pair_x_fupd g ∘ h =
          pair_x_fupd g ∘ pair_y_fupd f ∘ h
   
   [pair_t_fupdfupds]  Theorem
      
      ⊢ (∀p g f.
           p with <|pair_x updated_by f; pair_x updated_by g|> =
           p with pair_x updated_by f ∘ g) ∧
        ∀p g f.
          p with <|pair_y updated_by f; pair_y updated_by g|> =
          p with pair_y updated_by f ∘ g
   
   [pair_t_fupdfupds_comp]  Theorem
      
      ⊢ ((∀g f. pair_x_fupd f ∘ pair_x_fupd g = pair_x_fupd (f ∘ g)) ∧
         ∀h g f.
           pair_x_fupd f ∘ pair_x_fupd g ∘ h = pair_x_fupd (f ∘ g) ∘ h) ∧
        (∀g f. pair_y_fupd f ∘ pair_y_fupd g = pair_y_fupd (f ∘ g)) ∧
        ∀h g f. pair_y_fupd f ∘ pair_y_fupd g ∘ h = pair_y_fupd (f ∘ g) ∘ h
   
   [pair_t_induction]  Theorem
      
      ⊢ ∀P. (∀t t0. P (pair_t t t0)) ⇒ ∀p. P p
   
   [pair_t_literal_11]  Theorem
      
      ⊢ ∀t01 t1 t02 t2.
          <|pair_x := t01; pair_y := t1|> = <|pair_x := t02; pair_y := t2|> ⇔
          t01 = t02 ∧ t1 = t2
   
   [pair_t_literal_nchotomy]  Theorem
      
      ⊢ ∀p. ∃t0 t. p = <|pair_x := t0; pair_y := t|>
   
   [pair_t_nchotomy]  Theorem
      
      ⊢ ∀pp. ∃t t0. pp = pair_t t t0
   
   [pair_t_updates_eq_literal]  Theorem
      
      ⊢ ∀p t0 t.
          p with <|pair_x := t0; pair_y := t|> =
          <|pair_x := t0; pair_y := t|>
   
   [wrap_t_11]  Theorem
      
      ⊢ ∀a a'. wrap_t a = wrap_t a' ⇔ a = a'
   
   [wrap_t_Axiom]  Theorem
      
      ⊢ ∀f. ∃fn. ∀a. fn (wrap_t a) = f a
   
   [wrap_t_accessors]  Theorem
      
      ⊢ ∀t. (wrap_t t).wrap_val = t
   
   [wrap_t_accfupds]  Theorem
      
      ⊢ ∀w f. (w with wrap_val updated_by f).wrap_val = f w.wrap_val
   
   [wrap_t_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧ (∀a. M' = wrap_t a ⇒ f a = f' a) ⇒
          wrap_t_CASE M f = wrap_t_CASE M' f'
   
   [wrap_t_case_eq]  Theorem
      
      ⊢ wrap_t_CASE x f = v ⇔ ∃t. x = wrap_t t ∧ f t = v
   
   [wrap_t_component_equality]  Theorem
      
      ⊢ ∀w1 w2. w1 = w2 ⇔ w1.wrap_val = w2.wrap_val
   
   [wrap_t_fn_updates]  Theorem
      
      ⊢ ∀f t. wrap_t t with wrap_val updated_by f = wrap_t (f t)
   
   [wrap_t_fupdfupds]  Theorem
      
      ⊢ ∀w g f.
          w with <|wrap_val updated_by f; wrap_val updated_by g|> =
          w with wrap_val updated_by f ∘ g
   
   [wrap_t_fupdfupds_comp]  Theorem
      
      ⊢ (∀g f. wrap_val_fupd f ∘ wrap_val_fupd g = wrap_val_fupd (f ∘ g)) ∧
        ∀h g f.
          wrap_val_fupd f ∘ wrap_val_fupd g ∘ h = wrap_val_fupd (f ∘ g) ∘ h
   
   [wrap_t_induction]  Theorem
      
      ⊢ ∀P. (∀t. P (wrap_t t)) ⇒ ∀w. P w
   
   [wrap_t_literal_11]  Theorem
      
      ⊢ ∀u1 u2. <|wrap_val := u1|> = <|wrap_val := u2|> ⇔ u1 = u2
   
   [wrap_t_literal_nchotomy]  Theorem
      
      ⊢ ∀w. ∃u. w = <|wrap_val := u|>
   
   [wrap_t_nchotomy]  Theorem
      
      ⊢ ∀ww. ∃t. ww = wrap_t t
   
   [wrap_t_updates_eq_literal]  Theorem
      
      ⊢ ∀w u. w with wrap_val := u = <|wrap_val := u|>
   
   
*)
end
