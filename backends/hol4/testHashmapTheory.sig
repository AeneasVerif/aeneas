signature testHashmapTheory =
sig
  type thm = Thm.thm
  
  (*  Axioms  *)
    val insert_def : thm
  
  (*  Definitions  *)
    val distinct_keys_def : thm
    val list_t_TY_DEF : thm
    val list_t_case_def : thm
    val list_t_size_def : thm
    val list_t_v_def : thm
    val lookup_def : thm
  
  (*  Theorems  *)
    val datatype_list_t : thm
    val index_eq : thm
    val insert_lem : thm
    val list_t_11 : thm
    val list_t_Axiom : thm
    val list_t_case_cong : thm
    val list_t_case_eq : thm
    val list_t_distinct : thm
    val list_t_induction : thm
    val list_t_nchotomy : thm
    val lookup_raw_def : thm
    val lookup_raw_ind : thm
    val nth_mut_fwd_def : thm
    val nth_mut_fwd_ind : thm
    val nth_mut_fwd_spec : thm
  
  val testHashmap_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [primitives] Parent theory of "testHashmap"
   
   [insert_def]  Axiom
      
      [oracles: ] [axioms: insert_def] []
      ⊢ insert key value ls =
        case ls of
          ListCons (ckey,cvalue) tl =>
            if ckey = key then Return (ListCons (ckey,value) tl)
            else
              do
                tl0 <- insert key value tl;
                Return (ListCons (ckey,cvalue) tl0)
              od
        | ListNil => Return (ListCons (key,value) ListNil)
   
   [distinct_keys_def]  Definition
      
      ⊢ ∀ls.
          distinct_keys ls ⇔
          ∀i j.
            0 < i ⇒
            i < len ls ⇒
            0 < j ⇒
            j < len ls ⇒
            FST (index i ls) = FST (index j ls) ⇒
            i = j
   
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
   
   [list_t_v_def]  Definition
      
      ⊢ list_t_v ListNil = [] ∧
        ∀x tl. list_t_v (ListCons x tl) = x::list_t_v tl
   
   [lookup_def]  Definition
      
      ⊢ ∀key ls. lookup key ls = lookup_raw key (list_t_v ls)
   
   [datatype_list_t]  Theorem
      
      ⊢ DATATYPE (list_t ListCons ListNil)
   
   [index_eq]  Theorem
      
      ⊢ (∀x ls. index 0 (x::ls) = x) ∧
        ∀i x ls.
          index i (x::ls) =
          if 0 < i ∨ 0 ≤ i ∧ i ≠ 0 then index (i − 1) ls
          else if i = 0 then x
          else ARB
   
   [insert_lem]  Theorem
      
      [oracles: DISK_THM] [axioms: insert_def] []
      ⊢ ∀ls key value.
          distinct_keys (list_t_v ls) ⇒
          case insert key value ls of
            Return ls1 =>
              lookup key ls1 = SOME value ∧
              ∀k. k ≠ key ⇒ lookup k ls = lookup k ls1
          | Fail v1 => F
          | Loop => F
   
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
   
   [lookup_raw_def]  Theorem
      
      ⊢ (∀key. lookup_raw key [] = NONE) ∧
        ∀v ls key k.
          lookup_raw key ((k,v)::ls) =
          if k = key then SOME v else lookup_raw key ls
   
   [lookup_raw_ind]  Theorem
      
      ⊢ ∀P. (∀key. P key []) ∧
            (∀key k v ls. (k ≠ key ⇒ P key ls) ⇒ P key ((k,v)::ls)) ⇒
            ∀v v1. P v v1
   
   [nth_mut_fwd_def]  Theorem
      
      ⊢ ∀ls i.
          nth_mut_fwd ls i =
          case ls of
            ListCons x tl =>
              if u32_to_int i = 0 then Return x
              else do i0 <- u32_sub i (int_to_u32 1); nth_mut_fwd tl i0 od
          | ListNil => Fail Failure
   
   [nth_mut_fwd_ind]  Theorem
      
      ⊢ ∀P. (∀ls i.
               (∀x tl i0. ls = ListCons x tl ∧ u32_to_int i ≠ 0 ⇒ P tl i0) ⇒
               P ls i) ⇒
            ∀v v1. P v v1
   
   [nth_mut_fwd_spec]  Theorem
      
      ⊢ ∀ls i.
          u32_to_int i < len (list_t_v ls) ⇒
          case nth_mut_fwd ls i of
            Return x => x = index (u32_to_int i) (list_t_v ls)
          | Fail v1 => F
          | Loop => F
   
   
*)
end
