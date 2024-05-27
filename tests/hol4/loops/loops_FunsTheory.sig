signature loops_FunsTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val clear_fwd_back_def : thm
    val clear_loop_fwd_back_def : thm
    val get_elem_mut_back_def : thm
    val get_elem_mut_fwd_def : thm
    val get_elem_mut_loop_back_def : thm
    val get_elem_mut_loop_fwd_def : thm
    val get_elem_shared_fwd_def : thm
    val get_elem_shared_loop_fwd_def : thm
    val id_mut_back_def : thm
    val id_mut_fwd_def : thm
    val id_shared_fwd_def : thm
    val list_mem_fwd_def : thm
    val list_mem_loop_fwd_def : thm
    val list_nth_mut_loop_back_def : thm
    val list_nth_mut_loop_fwd_def : thm
    val list_nth_mut_loop_loop_back_def : thm
    val list_nth_mut_loop_loop_fwd_def : thm
    val list_nth_mut_loop_pair_back'a_def : thm
    val list_nth_mut_loop_pair_back'b_def : thm
    val list_nth_mut_loop_pair_fwd_def : thm
    val list_nth_mut_loop_pair_loop_back'a_def : thm
    val list_nth_mut_loop_pair_loop_back'b_def : thm
    val list_nth_mut_loop_pair_loop_fwd_def : thm
    val list_nth_mut_loop_pair_merge_back_def : thm
    val list_nth_mut_loop_pair_merge_fwd_def : thm
    val list_nth_mut_loop_pair_merge_loop_back_def : thm
    val list_nth_mut_loop_pair_merge_loop_fwd_def : thm
    val list_nth_mut_loop_with_id_back_def : thm
    val list_nth_mut_loop_with_id_fwd_def : thm
    val list_nth_mut_loop_with_id_loop_back_def : thm
    val list_nth_mut_loop_with_id_loop_fwd_def : thm
    val list_nth_mut_shared_loop_pair_back_def : thm
    val list_nth_mut_shared_loop_pair_fwd_def : thm
    val list_nth_mut_shared_loop_pair_loop_back_def : thm
    val list_nth_mut_shared_loop_pair_loop_fwd_def : thm
    val list_nth_mut_shared_loop_pair_merge_back_def : thm
    val list_nth_mut_shared_loop_pair_merge_fwd_def : thm
    val list_nth_mut_shared_loop_pair_merge_loop_back_def : thm
    val list_nth_mut_shared_loop_pair_merge_loop_fwd_def : thm
    val list_nth_shared_loop_fwd_def : thm
    val list_nth_shared_loop_loop_fwd_def : thm
    val list_nth_shared_loop_pair_fwd_def : thm
    val list_nth_shared_loop_pair_loop_fwd_def : thm
    val list_nth_shared_loop_pair_merge_fwd_def : thm
    val list_nth_shared_loop_pair_merge_loop_fwd_def : thm
    val list_nth_shared_loop_with_id_fwd_def : thm
    val list_nth_shared_loop_with_id_loop_fwd_def : thm
    val list_nth_shared_mut_loop_pair_back_def : thm
    val list_nth_shared_mut_loop_pair_fwd_def : thm
    val list_nth_shared_mut_loop_pair_loop_back_def : thm
    val list_nth_shared_mut_loop_pair_loop_fwd_def : thm
    val list_nth_shared_mut_loop_pair_merge_back_def : thm
    val list_nth_shared_mut_loop_pair_merge_fwd_def : thm
    val list_nth_shared_mut_loop_pair_merge_loop_back_def : thm
    val list_nth_shared_mut_loop_pair_merge_loop_fwd_def : thm
    val sum_fwd_def : thm
    val sum_loop_fwd_def : thm
    val sum_with_mut_borrows_fwd_def : thm
    val sum_with_mut_borrows_loop_fwd_def : thm
    val sum_with_shared_borrows_fwd_def : thm
    val sum_with_shared_borrows_loop_fwd_def : thm
  
  val loops_Funs_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [loops_Types] Parent theory of "loops_Funs"
   
   [clear_fwd_back_def]  Definition
      
      ⊢ ∀v. clear_fwd_back v = clear_loop_fwd_back v (int_to_usize 0)
   
   [clear_loop_fwd_back_def]  Definition
      
      ⊢ ∀v i.
          clear_loop_fwd_back v i =
          (let
             i0 = vec_len v
           in
             if usize_lt i i0 then
               do
                 i1 <- usize_add i (int_to_usize 1);
                 v0 <- vec_index_mut_back v i (int_to_u32 0);
                 clear_loop_fwd_back v0 i1
               od
             else Return v)
   
   [get_elem_mut_back_def]  Definition
      
      ⊢ ∀slots x ret.
          get_elem_mut_back slots x ret =
          do
            l <- vec_index_mut_fwd slots (int_to_usize 0);
            l0 <- get_elem_mut_loop_back x l ret;
            vec_index_mut_back slots (int_to_usize 0) l0
          od
   
   [get_elem_mut_fwd_def]  Definition
      
      ⊢ ∀slots x.
          get_elem_mut_fwd slots x =
          do
            l <- vec_index_mut_fwd slots (int_to_usize 0);
            get_elem_mut_loop_fwd x l
          od
   
   [get_elem_mut_loop_back_def]  Definition
      
      ⊢ ∀x ls ret.
          get_elem_mut_loop_back x ls ret =
          case ls of
            ListCons y tl =>
              if y = x then Return (ListCons ret tl)
              else
                do
                  tl0 <- get_elem_mut_loop_back x tl ret;
                  Return (ListCons y tl0)
                od
          | ListNil => Fail Failure
   
   [get_elem_mut_loop_fwd_def]  Definition
      
      ⊢ ∀x ls.
          get_elem_mut_loop_fwd x ls =
          case ls of
            ListCons y tl =>
              if y = x then Return y else get_elem_mut_loop_fwd x tl
          | ListNil => Fail Failure
   
   [get_elem_shared_fwd_def]  Definition
      
      ⊢ ∀slots x.
          get_elem_shared_fwd slots x =
          do
            l <- vec_index_fwd slots (int_to_usize 0);
            get_elem_shared_loop_fwd x l
          od
   
   [get_elem_shared_loop_fwd_def]  Definition
      
      ⊢ ∀x ls.
          get_elem_shared_loop_fwd x ls =
          case ls of
            ListCons y tl =>
              if y = x then Return y else get_elem_shared_loop_fwd x tl
          | ListNil => Fail Failure
   
   [id_mut_back_def]  Definition
      
      ⊢ ∀ls ret. id_mut_back ls ret = Return ret
   
   [id_mut_fwd_def]  Definition
      
      ⊢ ∀ls. id_mut_fwd ls = Return ls
   
   [id_shared_fwd_def]  Definition
      
      ⊢ ∀ls. id_shared_fwd ls = Return ls
   
   [list_mem_fwd_def]  Definition
      
      ⊢ ∀x ls. list_mem_fwd x ls = list_mem_loop_fwd x ls
   
   [list_mem_loop_fwd_def]  Definition
      
      ⊢ ∀x ls.
          list_mem_loop_fwd x ls =
          case ls of
            ListCons y tl =>
              if y = x then Return T else list_mem_loop_fwd x tl
          | ListNil => Return F
   
   [list_nth_mut_loop_back_def]  Definition
      
      ⊢ ∀ls i ret.
          list_nth_mut_loop_back ls i ret =
          list_nth_mut_loop_loop_back ls i ret
   
   [list_nth_mut_loop_fwd_def]  Definition
      
      ⊢ ∀ls i. list_nth_mut_loop_fwd ls i = list_nth_mut_loop_loop_fwd ls i
   
   [list_nth_mut_loop_loop_back_def]  Definition
      
      ⊢ ∀ls i ret.
          list_nth_mut_loop_loop_back ls i ret =
          case ls of
            ListCons x tl =>
              if i = int_to_u32 0 then Return (ListCons ret tl)
              else
                do
                  i0 <- u32_sub i (int_to_u32 1);
                  tl0 <- list_nth_mut_loop_loop_back tl i0 ret;
                  Return (ListCons x tl0)
                od
          | ListNil => Fail Failure
   
   [list_nth_mut_loop_loop_fwd_def]  Definition
      
      ⊢ ∀ls i.
          list_nth_mut_loop_loop_fwd ls i =
          case ls of
            ListCons x tl =>
              if i = int_to_u32 0 then Return x
              else
                do
                  i0 <- u32_sub i (int_to_u32 1);
                  list_nth_mut_loop_loop_fwd tl i0
                od
          | ListNil => Fail Failure
   
   [list_nth_mut_loop_pair_back'a_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_mut_loop_pair_back'a ls0 ls1 i ret =
          list_nth_mut_loop_pair_loop_back'a ls0 ls1 i ret
   
   [list_nth_mut_loop_pair_back'b_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_mut_loop_pair_back'b ls0 ls1 i ret =
          list_nth_mut_loop_pair_loop_back'b ls0 ls1 i ret
   
   [list_nth_mut_loop_pair_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_mut_loop_pair_fwd ls0 ls1 i =
          list_nth_mut_loop_pair_loop_fwd ls0 ls1 i
   
   [list_nth_mut_loop_pair_loop_back'a_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_mut_loop_pair_loop_back'a ls0 ls1 i ret =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (ListCons ret tl0)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       tl00 <-
                         list_nth_mut_loop_pair_loop_back'a tl0 tl1 i0 ret;
                       Return (ListCons x0 tl00)
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_mut_loop_pair_loop_back'b_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_mut_loop_pair_loop_back'b ls0 ls1 i ret =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (ListCons ret tl1)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       tl10 <-
                         list_nth_mut_loop_pair_loop_back'b tl0 tl1 i0 ret;
                       Return (ListCons x1 tl10)
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_mut_loop_pair_loop_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_mut_loop_pair_loop_fwd ls0 ls1 i =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (x0,x1)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       list_nth_mut_loop_pair_loop_fwd tl0 tl1 i0
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_mut_loop_pair_merge_back_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_mut_loop_pair_merge_back ls0 ls1 i ret =
          list_nth_mut_loop_pair_merge_loop_back ls0 ls1 i ret
   
   [list_nth_mut_loop_pair_merge_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_mut_loop_pair_merge_fwd ls0 ls1 i =
          list_nth_mut_loop_pair_merge_loop_fwd ls0 ls1 i
   
   [list_nth_mut_loop_pair_merge_loop_back_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_mut_loop_pair_merge_loop_back ls0 ls1 i ret =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then
                     (let
                        (t,t0) = ret
                      in
                        Return (ListCons t tl0,ListCons t0 tl1))
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       (tl00,tl10) <-
                         list_nth_mut_loop_pair_merge_loop_back tl0 tl1 i0
                           ret;
                       Return (ListCons x0 tl00,ListCons x1 tl10)
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_mut_loop_pair_merge_loop_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_mut_loop_pair_merge_loop_fwd ls0 ls1 i =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (x0,x1)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       list_nth_mut_loop_pair_merge_loop_fwd tl0 tl1 i0
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_mut_loop_with_id_back_def]  Definition
      
      ⊢ ∀ls i ret.
          list_nth_mut_loop_with_id_back ls i ret =
          do
            ls0 <- id_mut_fwd ls;
            l <- list_nth_mut_loop_with_id_loop_back i ls0 ret;
            id_mut_back ls l
          od
   
   [list_nth_mut_loop_with_id_fwd_def]  Definition
      
      ⊢ ∀ls i.
          list_nth_mut_loop_with_id_fwd ls i =
          do
            ls0 <- id_mut_fwd ls;
            list_nth_mut_loop_with_id_loop_fwd i ls0
          od
   
   [list_nth_mut_loop_with_id_loop_back_def]  Definition
      
      ⊢ ∀i ls ret.
          list_nth_mut_loop_with_id_loop_back i ls ret =
          case ls of
            ListCons x tl =>
              if i = int_to_u32 0 then Return (ListCons ret tl)
              else
                do
                  i0 <- u32_sub i (int_to_u32 1);
                  tl0 <- list_nth_mut_loop_with_id_loop_back i0 tl ret;
                  Return (ListCons x tl0)
                od
          | ListNil => Fail Failure
   
   [list_nth_mut_loop_with_id_loop_fwd_def]  Definition
      
      ⊢ ∀i ls.
          list_nth_mut_loop_with_id_loop_fwd i ls =
          case ls of
            ListCons x tl =>
              if i = int_to_u32 0 then Return x
              else
                do
                  i0 <- u32_sub i (int_to_u32 1);
                  list_nth_mut_loop_with_id_loop_fwd i0 tl
                od
          | ListNil => Fail Failure
   
   [list_nth_mut_shared_loop_pair_back_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_mut_shared_loop_pair_back ls0 ls1 i ret =
          list_nth_mut_shared_loop_pair_loop_back ls0 ls1 i ret
   
   [list_nth_mut_shared_loop_pair_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_mut_shared_loop_pair_fwd ls0 ls1 i =
          list_nth_mut_shared_loop_pair_loop_fwd ls0 ls1 i
   
   [list_nth_mut_shared_loop_pair_loop_back_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_mut_shared_loop_pair_loop_back ls0 ls1 i ret =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (ListCons ret tl0)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       tl00 <-
                         list_nth_mut_shared_loop_pair_loop_back tl0 tl1 i0
                           ret;
                       Return (ListCons x0 tl00)
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_mut_shared_loop_pair_loop_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_mut_shared_loop_pair_loop_fwd ls0 ls1 i =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (x0,x1)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       list_nth_mut_shared_loop_pair_loop_fwd tl0 tl1 i0
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_mut_shared_loop_pair_merge_back_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_mut_shared_loop_pair_merge_back ls0 ls1 i ret =
          list_nth_mut_shared_loop_pair_merge_loop_back ls0 ls1 i ret
   
   [list_nth_mut_shared_loop_pair_merge_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_mut_shared_loop_pair_merge_fwd ls0 ls1 i =
          list_nth_mut_shared_loop_pair_merge_loop_fwd ls0 ls1 i
   
   [list_nth_mut_shared_loop_pair_merge_loop_back_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_mut_shared_loop_pair_merge_loop_back ls0 ls1 i ret =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (ListCons ret tl0)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       tl00 <-
                         list_nth_mut_shared_loop_pair_merge_loop_back tl0
                           tl1 i0 ret;
                       Return (ListCons x0 tl00)
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_mut_shared_loop_pair_merge_loop_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_mut_shared_loop_pair_merge_loop_fwd ls0 ls1 i =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (x0,x1)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       list_nth_mut_shared_loop_pair_merge_loop_fwd tl0 tl1
                         i0
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_shared_loop_fwd_def]  Definition
      
      ⊢ ∀ls i.
          list_nth_shared_loop_fwd ls i =
          list_nth_shared_loop_loop_fwd ls i
   
   [list_nth_shared_loop_loop_fwd_def]  Definition
      
      ⊢ ∀ls i.
          list_nth_shared_loop_loop_fwd ls i =
          case ls of
            ListCons x tl =>
              if i = int_to_u32 0 then Return x
              else
                do
                  i0 <- u32_sub i (int_to_u32 1);
                  list_nth_shared_loop_loop_fwd tl i0
                od
          | ListNil => Fail Failure
   
   [list_nth_shared_loop_pair_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_shared_loop_pair_fwd ls0 ls1 i =
          list_nth_shared_loop_pair_loop_fwd ls0 ls1 i
   
   [list_nth_shared_loop_pair_loop_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_shared_loop_pair_loop_fwd ls0 ls1 i =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (x0,x1)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       list_nth_shared_loop_pair_loop_fwd tl0 tl1 i0
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_shared_loop_pair_merge_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_shared_loop_pair_merge_fwd ls0 ls1 i =
          list_nth_shared_loop_pair_merge_loop_fwd ls0 ls1 i
   
   [list_nth_shared_loop_pair_merge_loop_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_shared_loop_pair_merge_loop_fwd ls0 ls1 i =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (x0,x1)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       list_nth_shared_loop_pair_merge_loop_fwd tl0 tl1 i0
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_shared_loop_with_id_fwd_def]  Definition
      
      ⊢ ∀ls i.
          list_nth_shared_loop_with_id_fwd ls i =
          do
            ls0 <- id_shared_fwd ls;
            list_nth_shared_loop_with_id_loop_fwd i ls0
          od
   
   [list_nth_shared_loop_with_id_loop_fwd_def]  Definition
      
      ⊢ ∀i ls.
          list_nth_shared_loop_with_id_loop_fwd i ls =
          case ls of
            ListCons x tl =>
              if i = int_to_u32 0 then Return x
              else
                do
                  i0 <- u32_sub i (int_to_u32 1);
                  list_nth_shared_loop_with_id_loop_fwd i0 tl
                od
          | ListNil => Fail Failure
   
   [list_nth_shared_mut_loop_pair_back_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_shared_mut_loop_pair_back ls0 ls1 i ret =
          list_nth_shared_mut_loop_pair_loop_back ls0 ls1 i ret
   
   [list_nth_shared_mut_loop_pair_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_shared_mut_loop_pair_fwd ls0 ls1 i =
          list_nth_shared_mut_loop_pair_loop_fwd ls0 ls1 i
   
   [list_nth_shared_mut_loop_pair_loop_back_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_shared_mut_loop_pair_loop_back ls0 ls1 i ret =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (ListCons ret tl1)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       tl10 <-
                         list_nth_shared_mut_loop_pair_loop_back tl0 tl1 i0
                           ret;
                       Return (ListCons x1 tl10)
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_shared_mut_loop_pair_loop_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_shared_mut_loop_pair_loop_fwd ls0 ls1 i =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (x0,x1)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       list_nth_shared_mut_loop_pair_loop_fwd tl0 tl1 i0
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_shared_mut_loop_pair_merge_back_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_shared_mut_loop_pair_merge_back ls0 ls1 i ret =
          list_nth_shared_mut_loop_pair_merge_loop_back ls0 ls1 i ret
   
   [list_nth_shared_mut_loop_pair_merge_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_shared_mut_loop_pair_merge_fwd ls0 ls1 i =
          list_nth_shared_mut_loop_pair_merge_loop_fwd ls0 ls1 i
   
   [list_nth_shared_mut_loop_pair_merge_loop_back_def]  Definition
      
      ⊢ ∀ls0 ls1 i ret.
          list_nth_shared_mut_loop_pair_merge_loop_back ls0 ls1 i ret =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (ListCons ret tl1)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       tl10 <-
                         list_nth_shared_mut_loop_pair_merge_loop_back tl0
                           tl1 i0 ret;
                       Return (ListCons x1 tl10)
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [list_nth_shared_mut_loop_pair_merge_loop_fwd_def]  Definition
      
      ⊢ ∀ls0 ls1 i.
          list_nth_shared_mut_loop_pair_merge_loop_fwd ls0 ls1 i =
          case ls0 of
            ListCons x0 tl0 =>
              (case ls1 of
                 ListCons x1 tl1 =>
                   if i = int_to_u32 0 then Return (x0,x1)
                   else
                     do
                       i0 <- u32_sub i (int_to_u32 1);
                       list_nth_shared_mut_loop_pair_merge_loop_fwd tl0 tl1
                         i0
                     od
               | ListNil => Fail Failure)
          | ListNil => Fail Failure
   
   [sum_fwd_def]  Definition
      
      ⊢ ∀max. sum_fwd max = sum_loop_fwd max (int_to_u32 0) (int_to_u32 0)
   
   [sum_loop_fwd_def]  Definition
      
      ⊢ ∀max i s.
          sum_loop_fwd max i s =
          if u32_lt i max then
            do
              s0 <- u32_add s i;
              i0 <- u32_add i (int_to_u32 1);
              sum_loop_fwd max i0 s0
            od
          else u32_mul s (int_to_u32 2)
   
   [sum_with_mut_borrows_fwd_def]  Definition
      
      ⊢ ∀max.
          sum_with_mut_borrows_fwd max =
          sum_with_mut_borrows_loop_fwd max (int_to_u32 0) (int_to_u32 0)
   
   [sum_with_mut_borrows_loop_fwd_def]  Definition
      
      ⊢ ∀max mi ms.
          sum_with_mut_borrows_loop_fwd max mi ms =
          if u32_lt mi max then
            do
              ms0 <- u32_add ms mi;
              mi0 <- u32_add mi (int_to_u32 1);
              sum_with_mut_borrows_loop_fwd max mi0 ms0
            od
          else u32_mul ms (int_to_u32 2)
   
   [sum_with_shared_borrows_fwd_def]  Definition
      
      ⊢ ∀max.
          sum_with_shared_borrows_fwd max =
          sum_with_shared_borrows_loop_fwd max (int_to_u32 0)
            (int_to_u32 0)
   
   [sum_with_shared_borrows_loop_fwd_def]  Definition
      
      ⊢ ∀max i s.
          sum_with_shared_borrows_loop_fwd max i s =
          if u32_lt i max then
            do
              i0 <- u32_add i (int_to_u32 1);
              s0 <- u32_add s i0;
              sum_with_shared_borrows_loop_fwd max i0 s0
            od
          else u32_mul s (int_to_u32 2)
   
   
*)
end
