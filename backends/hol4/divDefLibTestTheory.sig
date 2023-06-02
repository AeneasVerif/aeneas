signature divDefLibTestTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val btree_TY_DEF : thm
    val btree_case_def : thm
    val btree_height_def : thm
    val btree_size_def : thm
    val even_def : thm
    val list_t_TY_DEF : thm
    val list_t_case_def : thm
    val list_t_size_def : thm
    val node_TY_DEF : thm
    val node_case_def : thm
    val nth0_def : thm
    val nth_def : thm
    val odd_def : thm
    val tree_TY_DEF : thm
    val tree_case_def : thm
    val tree_height_def : thm
    val tree_nodes_height_def : thm
    val tree_size_def : thm
  
  (*  Theorems  *)
    val btree_11 : thm
    val btree_Axiom : thm
    val btree_case_cong : thm
    val btree_case_eq : thm
    val btree_distinct : thm
    val btree_induction : thm
    val btree_nchotomy : thm
    val datatype_btree : thm
    val datatype_list_t : thm
    val datatype_tree : thm
    val list_t_11 : thm
    val list_t_Axiom : thm
    val list_t_case_cong : thm
    val list_t_case_eq : thm
    val list_t_distinct : thm
    val list_t_induction : thm
    val list_t_nchotomy : thm
    val node_11 : thm
    val node_Axiom : thm
    val node_case_cong : thm
    val node_case_eq : thm
    val node_induction : thm
    val node_nchotomy : thm
    val tree_11 : thm
    val tree_Axiom : thm
    val tree_case_cong : thm
    val tree_case_eq : thm
    val tree_distinct : thm
    val tree_induction : thm
    val tree_nchotomy : thm
  
  val divDefLibTest_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [divDef] Parent theory of "divDefLibTest"
   
   [btree_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('btree').
                   (∀a0'.
                      (∃a. a0' =
                           (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                             a) ∨
                      (∃a0 a1.
                         a0' =
                         (λa0 a1.
                              ind_type$CONSTR (SUC 0) ARB
                                (ind_type$FCONS a0
                                   (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                           a0 a1 ∧ $var$('btree') a0 ∧ $var$('btree') a1) ⇒
                      $var$('btree') a0') ⇒
                   $var$('btree') a0') rep
   
   [btree_case_def]  Definition
      
      ⊢ (∀a f f1. btree_CASE (BLeaf a) f f1 = f a) ∧
        ∀a0 a1 f f1. btree_CASE (BNode a0 a1) f f1 = f1 a0 a1
   
   [btree_height_def]  Definition
      
      ⊢ ∀tree.
          btree_height tree =
          case tree of
            BLeaf v => Return 1
          | BNode l r =>
            do
              hl <- btree_height l;
              hr <- btree_height r;
              Return (hl + hr)
            od
   
   [btree_size_def]  Definition
      
      ⊢ (∀f a. btree_size f (BLeaf a) = 1 + f a) ∧
        ∀f a0 a1.
          btree_size f (BNode a0 a1) =
          1 + (btree_size f a0 + btree_size f a1)
   
   [even_def]  Definition
      
      ⊢ ∀i. even i = if i = 0 then Return T else odd (i − 1)
   
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
   
   [node_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa1'.
                 ∀ $var$('tree') $var$('node')
                     $var$('@temp @ind_typedivDefLibTest8list').
                   (∀a0'.
                      (∃a. a0' =
                           (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                             a) ∨
                      (∃a. a0' =
                           (λa.
                                ind_type$CONSTR (SUC 0) ARB
                                  (ind_type$FCONS a (λn. ind_type$BOTTOM)))
                             a ∧ $var$('node') a) ⇒
                      $var$('tree') a0') ∧
                   (∀a1'.
                      (∃a. a1' =
                           (λa.
                                ind_type$CONSTR (SUC (SUC 0)) ARB
                                  (ind_type$FCONS a (λn. ind_type$BOTTOM)))
                             a ∧
                           $var$('@temp @ind_typedivDefLibTest8list') a) ⇒
                      $var$('node') a1') ∧
                   (∀a2.
                      a2 =
                      ind_type$CONSTR (SUC (SUC (SUC 0))) ARB
                        (λn. ind_type$BOTTOM) ∨
                      (∃a0 a1.
                         a2 =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC (SUC (SUC 0)))) ARB
                                (ind_type$FCONS a0
                                   (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                           a0 a1 ∧ $var$('tree') a0 ∧
                         $var$('@temp @ind_typedivDefLibTest8list') a1) ⇒
                      $var$('@temp @ind_typedivDefLibTest8list') a2) ⇒
                   $var$('node') a1') rep
   
   [node_case_def]  Definition
      
      ⊢ ∀a f. node_CASE (Node a) f = f a
   
   [nth0_def]  Definition
      
      ⊢ ∀ls i.
          nth0 ls i =
          case ls of
            ListCons x tl => if i = 0 then Return x else nth0 tl (i − 1)
          | ListNil => Fail Failure
   
   [nth_def]  Definition
      
      ⊢ ∀ls i.
          nth ls i =
          case ls of
            ListCons x tl =>
              if u32_to_int i = 0 then Return x
              else do i0 <- u32_sub i (int_to_u32 1); nth tl i0 od
          | ListNil => Fail Failure
   
   [odd_def]  Definition
      
      ⊢ ∀i. odd i = if i = 0 then Return F else even (i − 1)
   
   [tree_TY_DEF]  Definition
      
      ⊢ ∃rep.
          TYPE_DEFINITION
            (λa0'.
                 ∀ $var$('tree') $var$('node')
                     $var$('@temp @ind_typedivDefLibTest8list').
                   (∀a0'.
                      (∃a. a0' =
                           (λa. ind_type$CONSTR 0 a (λn. ind_type$BOTTOM))
                             a) ∨
                      (∃a. a0' =
                           (λa.
                                ind_type$CONSTR (SUC 0) ARB
                                  (ind_type$FCONS a (λn. ind_type$BOTTOM)))
                             a ∧ $var$('node') a) ⇒
                      $var$('tree') a0') ∧
                   (∀a1'.
                      (∃a. a1' =
                           (λa.
                                ind_type$CONSTR (SUC (SUC 0)) ARB
                                  (ind_type$FCONS a (λn. ind_type$BOTTOM)))
                             a ∧
                           $var$('@temp @ind_typedivDefLibTest8list') a) ⇒
                      $var$('node') a1') ∧
                   (∀a2.
                      a2 =
                      ind_type$CONSTR (SUC (SUC (SUC 0))) ARB
                        (λn. ind_type$BOTTOM) ∨
                      (∃a0 a1.
                         a2 =
                         (λa0 a1.
                              ind_type$CONSTR (SUC (SUC (SUC (SUC 0)))) ARB
                                (ind_type$FCONS a0
                                   (ind_type$FCONS a1 (λn. ind_type$BOTTOM))))
                           a0 a1 ∧ $var$('tree') a0 ∧
                         $var$('@temp @ind_typedivDefLibTest8list') a1) ⇒
                      $var$('@temp @ind_typedivDefLibTest8list') a2) ⇒
                   $var$('tree') a0') rep
   
   [tree_case_def]  Definition
      
      ⊢ (∀a f f1. tree_CASE (TLeaf a) f f1 = f a) ∧
        ∀a f f1. tree_CASE (TNode a) f f1 = f1 a
   
   [tree_height_def]  Definition
      
      ⊢ ∀tree.
          tree_height tree =
          case tree of
            TLeaf v => Return 1
          | TNode (Node ls) => tree_nodes_height ls
   
   [tree_nodes_height_def]  Definition
      
      ⊢ ∀ls.
          tree_nodes_height ls =
          case ls of
            [] => Return 0
          | t::tl =>
            do
              h1 <- tree_height t;
              h2 <- tree_nodes_height tl;
              Return (h1 + h2)
            od
   
   [tree_size_def]  Definition
      
      ⊢ (∀f a. tree_size f (TLeaf a) = 1 + f a) ∧
        (∀f a. tree_size f (TNode a) = 1 + node_size f a) ∧
        (∀f a. node_size f (Node a) = 1 + tree1_size f a) ∧
        (∀f. tree1_size f [] = 0) ∧
        ∀f a0 a1.
          tree1_size f (a0::a1) = 1 + (tree_size f a0 + tree1_size f a1)
   
   [btree_11]  Theorem
      
      ⊢ (∀a a'. BLeaf a = BLeaf a' ⇔ a = a') ∧
        ∀a0 a1 a0' a1'. BNode a0 a1 = BNode a0' a1' ⇔ a0 = a0' ∧ a1 = a1'
   
   [btree_Axiom]  Theorem
      
      ⊢ ∀f0 f1. ∃fn.
          (∀a. fn (BLeaf a) = f0 a) ∧
          ∀a0 a1. fn (BNode a0 a1) = f1 a0 a1 (fn a0) (fn a1)
   
   [btree_case_cong]  Theorem
      
      ⊢ ∀M M' f f1.
          M = M' ∧ (∀a. M' = BLeaf a ⇒ f a = f' a) ∧
          (∀a0 a1. M' = BNode a0 a1 ⇒ f1 a0 a1 = f1' a0 a1) ⇒
          btree_CASE M f f1 = btree_CASE M' f' f1'
   
   [btree_case_eq]  Theorem
      
      ⊢ btree_CASE x f f1 = v ⇔
        (∃a. x = BLeaf a ∧ f a = v) ∨ ∃b b0. x = BNode b b0 ∧ f1 b b0 = v
   
   [btree_distinct]  Theorem
      
      ⊢ ∀a1 a0 a. BLeaf a ≠ BNode a0 a1
   
   [btree_induction]  Theorem
      
      ⊢ ∀P. (∀a. P (BLeaf a)) ∧ (∀b b0. P b ∧ P b0 ⇒ P (BNode b b0)) ⇒
            ∀b. P b
   
   [btree_nchotomy]  Theorem
      
      ⊢ ∀bb. (∃a. bb = BLeaf a) ∨ ∃b b0. bb = BNode b b0
   
   [datatype_btree]  Theorem
      
      ⊢ DATATYPE (btree BLeaf BNode)
   
   [datatype_list_t]  Theorem
      
      ⊢ DATATYPE (list_t ListCons ListNil)
   
   [datatype_tree]  Theorem
      
      ⊢ DATATYPE (tree TLeaf TNode ∧ node Node)
   
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
   
   [node_11]  Theorem
      
      ⊢ ∀a a'. Node a = Node a' ⇔ a = a'
   
   [node_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3 f4. ∃fn0 fn1 fn2.
          (∀a. fn0 (TLeaf a) = f0 a) ∧ (∀a. fn0 (TNode a) = f1 a (fn1 a)) ∧
          (∀a. fn1 (Node a) = f2 a (fn2 a)) ∧ fn2 [] = f3 ∧
          ∀a0 a1. fn2 (a0::a1) = f4 a0 a1 (fn0 a0) (fn2 a1)
   
   [node_case_cong]  Theorem
      
      ⊢ ∀M M' f.
          M = M' ∧ (∀a. M' = Node a ⇒ f a = f' a) ⇒
          node_CASE M f = node_CASE M' f'
   
   [node_case_eq]  Theorem
      
      ⊢ node_CASE x f = v ⇔ ∃l. x = Node l ∧ f l = v
   
   [node_induction]  Theorem
      
      ⊢ ∀P0 P1 P2.
          (∀a. P0 (TLeaf a)) ∧ (∀n. P1 n ⇒ P0 (TNode n)) ∧
          (∀l. P2 l ⇒ P1 (Node l)) ∧ P2 [] ∧
          (∀t l. P0 t ∧ P2 l ⇒ P2 (t::l)) ⇒
          (∀t. P0 t) ∧ (∀n. P1 n) ∧ ∀l. P2 l
   
   [node_nchotomy]  Theorem
      
      ⊢ ∀nn. ∃l. nn = Node l
   
   [tree_11]  Theorem
      
      ⊢ (∀a a'. TLeaf a = TLeaf a' ⇔ a = a') ∧
        ∀a a'. TNode a = TNode a' ⇔ a = a'
   
   [tree_Axiom]  Theorem
      
      ⊢ ∀f0 f1 f2 f3 f4. ∃fn0 fn1 fn2.
          (∀a. fn0 (TLeaf a) = f0 a) ∧ (∀a. fn0 (TNode a) = f1 a (fn1 a)) ∧
          (∀a. fn1 (Node a) = f2 a (fn2 a)) ∧ fn2 [] = f3 ∧
          ∀a0 a1. fn2 (a0::a1) = f4 a0 a1 (fn0 a0) (fn2 a1)
   
   [tree_case_cong]  Theorem
      
      ⊢ ∀M M' f f1.
          M = M' ∧ (∀a. M' = TLeaf a ⇒ f a = f' a) ∧
          (∀a. M' = TNode a ⇒ f1 a = f1' a) ⇒
          tree_CASE M f f1 = tree_CASE M' f' f1'
   
   [tree_case_eq]  Theorem
      
      ⊢ tree_CASE x f f1 = v ⇔
        (∃a. x = TLeaf a ∧ f a = v) ∨ ∃n. x = TNode n ∧ f1 n = v
   
   [tree_distinct]  Theorem
      
      ⊢ ∀a' a. TLeaf a ≠ TNode a'
   
   [tree_induction]  Theorem
      
      ⊢ ∀P0 P1 P2.
          (∀a. P0 (TLeaf a)) ∧ (∀n. P1 n ⇒ P0 (TNode n)) ∧
          (∀l. P2 l ⇒ P1 (Node l)) ∧ P2 [] ∧
          (∀t l. P0 t ∧ P2 l ⇒ P2 (t::l)) ⇒
          (∀t. P0 t) ∧ (∀n. P1 n) ∧ ∀l. P2 l
   
   [tree_nchotomy]  Theorem
      
      ⊢ ∀tt. (∃a. tt = TLeaf a) ∨ ∃n. tt = TNode n
   
   
*)
end
