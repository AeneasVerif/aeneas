signature hashmapMain_FunsTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val hashmap_hash_key_fwd_def : thm
    val hashmap_hash_map_allocate_slots_fwd_def : thm
    val hashmap_hash_map_allocate_slots_loop_fwd_def : thm
    val hashmap_hash_map_clear_fwd_back_def : thm
    val hashmap_hash_map_clear_loop_fwd_back_def : thm
    val hashmap_hash_map_contains_key_fwd_def : thm
    val hashmap_hash_map_contains_key_in_list_fwd_def : thm
    val hashmap_hash_map_contains_key_in_list_loop_fwd_def : thm
    val hashmap_hash_map_get_fwd_def : thm
    val hashmap_hash_map_get_in_list_fwd_def : thm
    val hashmap_hash_map_get_in_list_loop_fwd_def : thm
    val hashmap_hash_map_get_mut_back_def : thm
    val hashmap_hash_map_get_mut_fwd_def : thm
    val hashmap_hash_map_get_mut_in_list_back_def : thm
    val hashmap_hash_map_get_mut_in_list_fwd_def : thm
    val hashmap_hash_map_get_mut_in_list_loop_back_def : thm
    val hashmap_hash_map_get_mut_in_list_loop_fwd_def : thm
    val hashmap_hash_map_insert_fwd_back_def : thm
    val hashmap_hash_map_insert_in_list_back_def : thm
    val hashmap_hash_map_insert_in_list_fwd_def : thm
    val hashmap_hash_map_insert_in_list_loop_back_def : thm
    val hashmap_hash_map_insert_in_list_loop_fwd_def : thm
    val hashmap_hash_map_insert_no_resize_fwd_back_def : thm
    val hashmap_hash_map_len_fwd_def : thm
    val hashmap_hash_map_move_elements_from_list_fwd_back_def : thm
    val hashmap_hash_map_move_elements_from_list_loop_fwd_back_def : thm
    val hashmap_hash_map_move_elements_fwd_back_def : thm
    val hashmap_hash_map_move_elements_loop_fwd_back_def : thm
    val hashmap_hash_map_new_fwd_def : thm
    val hashmap_hash_map_new_with_capacity_fwd_def : thm
    val hashmap_hash_map_remove_back_def : thm
    val hashmap_hash_map_remove_from_list_back_def : thm
    val hashmap_hash_map_remove_from_list_fwd_def : thm
    val hashmap_hash_map_remove_from_list_loop_back_def : thm
    val hashmap_hash_map_remove_from_list_loop_fwd_def : thm
    val hashmap_hash_map_remove_fwd_def : thm
    val hashmap_hash_map_try_resize_fwd_back_def : thm
    val hashmap_test1_fwd_def : thm
    val insert_on_disk_fwd_def : thm
    val main_fwd_def : thm
  
  val hashmapMain_Funs_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [hashmapMain_Opaque] Parent theory of "hashmapMain_Funs"
   
   [hashmap_hash_key_fwd_def]  Definition
      
      ⊢ ∀k. hashmap_hash_key_fwd k = Return k
   
   [hashmap_hash_map_allocate_slots_fwd_def]  Definition
      
      ⊢ ∀slots n.
          hashmap_hash_map_allocate_slots_fwd slots n =
          hashmap_hash_map_allocate_slots_loop_fwd slots n
   
   [hashmap_hash_map_allocate_slots_loop_fwd_def]  Definition
      
      ⊢ ∀slots n.
          hashmap_hash_map_allocate_slots_loop_fwd slots n =
          if usize_gt n (int_to_usize 0) then
            do
              slots0 <- vec_push_back slots HashmapListNil;
              n0 <- usize_sub n (int_to_usize 1);
              hashmap_hash_map_allocate_slots_loop_fwd slots0 n0
            od
          else Return slots
   
   [hashmap_hash_map_clear_fwd_back_def]  Definition
      
      ⊢ ∀self.
          hashmap_hash_map_clear_fwd_back self =
          do
            v <-
              hashmap_hash_map_clear_loop_fwd_back
                self.hashmap_hash_map_slots (int_to_usize 0);
            Return
              (self with
               <|hashmap_hash_map_num_entries := int_to_usize 0;
                 hashmap_hash_map_slots := v|>)
          od
   
   [hashmap_hash_map_clear_loop_fwd_back_def]  Definition
      
      ⊢ ∀slots i.
          hashmap_hash_map_clear_loop_fwd_back slots i =
          (let
             i0 = vec_len slots
           in
             if usize_lt i i0 then
               do
                 i1 <- usize_add i (int_to_usize 1);
                 slots0 <- vec_index_mut_back slots i HashmapListNil;
                 hashmap_hash_map_clear_loop_fwd_back slots0 i1
               od
             else Return slots)
   
   [hashmap_hash_map_contains_key_fwd_def]  Definition
      
      ⊢ ∀self key.
          hashmap_hash_map_contains_key_fwd self key =
          do
            hash <- hashmap_hash_key_fwd key;
            i <<- vec_len self.hashmap_hash_map_slots;
            hash_mod <- usize_rem hash i;
            l <- vec_index_fwd self.hashmap_hash_map_slots hash_mod;
            hashmap_hash_map_contains_key_in_list_fwd key l
          od
   
   [hashmap_hash_map_contains_key_in_list_fwd_def]  Definition
      
      ⊢ ∀key ls.
          hashmap_hash_map_contains_key_in_list_fwd key ls =
          hashmap_hash_map_contains_key_in_list_loop_fwd key ls
   
   [hashmap_hash_map_contains_key_in_list_loop_fwd_def]  Definition
      
      ⊢ ∀key ls.
          hashmap_hash_map_contains_key_in_list_loop_fwd key ls =
          case ls of
            HashmapListCons ckey t tl =>
              if ckey = key then Return T
              else hashmap_hash_map_contains_key_in_list_loop_fwd key tl
          | HashmapListNil => Return F
   
   [hashmap_hash_map_get_fwd_def]  Definition
      
      ⊢ ∀self key.
          hashmap_hash_map_get_fwd self key =
          do
            hash <- hashmap_hash_key_fwd key;
            i <<- vec_len self.hashmap_hash_map_slots;
            hash_mod <- usize_rem hash i;
            l <- vec_index_fwd self.hashmap_hash_map_slots hash_mod;
            hashmap_hash_map_get_in_list_fwd key l
          od
   
   [hashmap_hash_map_get_in_list_fwd_def]  Definition
      
      ⊢ ∀key ls.
          hashmap_hash_map_get_in_list_fwd key ls =
          hashmap_hash_map_get_in_list_loop_fwd key ls
   
   [hashmap_hash_map_get_in_list_loop_fwd_def]  Definition
      
      ⊢ ∀key ls.
          hashmap_hash_map_get_in_list_loop_fwd key ls =
          case ls of
            HashmapListCons ckey cvalue tl =>
              if ckey = key then Return cvalue
              else hashmap_hash_map_get_in_list_loop_fwd key tl
          | HashmapListNil => Fail Failure
   
   [hashmap_hash_map_get_mut_back_def]  Definition
      
      ⊢ ∀self key ret.
          hashmap_hash_map_get_mut_back self key ret =
          do
            hash <- hashmap_hash_key_fwd key;
            i <<- vec_len self.hashmap_hash_map_slots;
            hash_mod <- usize_rem hash i;
            l <- vec_index_mut_fwd self.hashmap_hash_map_slots hash_mod;
            l0 <- hashmap_hash_map_get_mut_in_list_back l key ret;
            v <- vec_index_mut_back self.hashmap_hash_map_slots hash_mod l0;
            Return (self with hashmap_hash_map_slots := v)
          od
   
   [hashmap_hash_map_get_mut_fwd_def]  Definition
      
      ⊢ ∀self key.
          hashmap_hash_map_get_mut_fwd self key =
          do
            hash <- hashmap_hash_key_fwd key;
            i <<- vec_len self.hashmap_hash_map_slots;
            hash_mod <- usize_rem hash i;
            l <- vec_index_mut_fwd self.hashmap_hash_map_slots hash_mod;
            hashmap_hash_map_get_mut_in_list_fwd l key
          od
   
   [hashmap_hash_map_get_mut_in_list_back_def]  Definition
      
      ⊢ ∀ls key ret.
          hashmap_hash_map_get_mut_in_list_back ls key ret =
          hashmap_hash_map_get_mut_in_list_loop_back ls key ret
   
   [hashmap_hash_map_get_mut_in_list_fwd_def]  Definition
      
      ⊢ ∀ls key.
          hashmap_hash_map_get_mut_in_list_fwd ls key =
          hashmap_hash_map_get_mut_in_list_loop_fwd ls key
   
   [hashmap_hash_map_get_mut_in_list_loop_back_def]  Definition
      
      ⊢ ∀ls key ret.
          hashmap_hash_map_get_mut_in_list_loop_back ls key ret =
          case ls of
            HashmapListCons ckey cvalue tl =>
              if ckey = key then Return (HashmapListCons ckey ret tl)
              else
                do
                  tl0 <-
                    hashmap_hash_map_get_mut_in_list_loop_back tl key ret;
                  Return (HashmapListCons ckey cvalue tl0)
                od
          | HashmapListNil => Fail Failure
   
   [hashmap_hash_map_get_mut_in_list_loop_fwd_def]  Definition
      
      ⊢ ∀ls key.
          hashmap_hash_map_get_mut_in_list_loop_fwd ls key =
          case ls of
            HashmapListCons ckey cvalue tl =>
              if ckey = key then Return cvalue
              else hashmap_hash_map_get_mut_in_list_loop_fwd tl key
          | HashmapListNil => Fail Failure
   
   [hashmap_hash_map_insert_fwd_back_def]  Definition
      
      ⊢ ∀self key value.
          hashmap_hash_map_insert_fwd_back self key value =
          do
            self0 <-
              hashmap_hash_map_insert_no_resize_fwd_back self key value;
            i <- hashmap_hash_map_len_fwd self0;
            if usize_gt i self0.hashmap_hash_map_max_load then
              hashmap_hash_map_try_resize_fwd_back self0
            else Return self0
          od
   
   [hashmap_hash_map_insert_in_list_back_def]  Definition
      
      ⊢ ∀key value ls.
          hashmap_hash_map_insert_in_list_back key value ls =
          hashmap_hash_map_insert_in_list_loop_back key value ls
   
   [hashmap_hash_map_insert_in_list_fwd_def]  Definition
      
      ⊢ ∀key value ls.
          hashmap_hash_map_insert_in_list_fwd key value ls =
          hashmap_hash_map_insert_in_list_loop_fwd key value ls
   
   [hashmap_hash_map_insert_in_list_loop_back_def]  Definition
      
      ⊢ ∀key value ls.
          hashmap_hash_map_insert_in_list_loop_back key value ls =
          case ls of
            HashmapListCons ckey cvalue tl =>
              if ckey = key then Return (HashmapListCons ckey value tl)
              else
                do
                  tl0 <-
                    hashmap_hash_map_insert_in_list_loop_back key value tl;
                  Return (HashmapListCons ckey cvalue tl0)
                od
          | HashmapListNil =>
            (let
               l = HashmapListNil
             in
               Return (HashmapListCons key value l))
   
   [hashmap_hash_map_insert_in_list_loop_fwd_def]  Definition
      
      ⊢ ∀key value ls.
          hashmap_hash_map_insert_in_list_loop_fwd key value ls =
          case ls of
            HashmapListCons ckey cvalue tl =>
              if ckey = key then Return F
              else hashmap_hash_map_insert_in_list_loop_fwd key value tl
          | HashmapListNil => Return T
   
   [hashmap_hash_map_insert_no_resize_fwd_back_def]  Definition
      
      ⊢ ∀self key value.
          hashmap_hash_map_insert_no_resize_fwd_back self key value =
          do
            hash <- hashmap_hash_key_fwd key;
            i <<- vec_len self.hashmap_hash_map_slots;
            hash_mod <- usize_rem hash i;
            l <- vec_index_mut_fwd self.hashmap_hash_map_slots hash_mod;
            inserted <- hashmap_hash_map_insert_in_list_fwd key value l;
            if inserted then
              do
                i0 <-
                  usize_add self.hashmap_hash_map_num_entries
                    (int_to_usize 1);
                l0 <- hashmap_hash_map_insert_in_list_back key value l;
                v <-
                  vec_index_mut_back self.hashmap_hash_map_slots hash_mod
                    l0;
                Return
                  (self with
                   <|hashmap_hash_map_num_entries := i0;
                     hashmap_hash_map_slots := v|>)
              od
            else
              do
                l0 <- hashmap_hash_map_insert_in_list_back key value l;
                v <-
                  vec_index_mut_back self.hashmap_hash_map_slots hash_mod
                    l0;
                Return (self with hashmap_hash_map_slots := v)
              od
          od
   
   [hashmap_hash_map_len_fwd_def]  Definition
      
      ⊢ ∀self.
          hashmap_hash_map_len_fwd self =
          Return self.hashmap_hash_map_num_entries
   
   [hashmap_hash_map_move_elements_from_list_fwd_back_def]  Definition
      
      ⊢ ∀ntable ls.
          hashmap_hash_map_move_elements_from_list_fwd_back ntable ls =
          hashmap_hash_map_move_elements_from_list_loop_fwd_back ntable ls
   
   [hashmap_hash_map_move_elements_from_list_loop_fwd_back_def]  Definition
      
      ⊢ ∀ntable ls.
          hashmap_hash_map_move_elements_from_list_loop_fwd_back ntable ls =
          case ls of
            HashmapListCons k v tl =>
              do
                ntable0 <-
                  hashmap_hash_map_insert_no_resize_fwd_back ntable k v;
                hashmap_hash_map_move_elements_from_list_loop_fwd_back
                  ntable0 tl
              od
          | HashmapListNil => Return ntable
   
   [hashmap_hash_map_move_elements_fwd_back_def]  Definition
      
      ⊢ ∀ntable slots i.
          hashmap_hash_map_move_elements_fwd_back ntable slots i =
          hashmap_hash_map_move_elements_loop_fwd_back ntable slots i
   
   [hashmap_hash_map_move_elements_loop_fwd_back_def]  Definition
      
      ⊢ ∀ntable slots i.
          hashmap_hash_map_move_elements_loop_fwd_back ntable slots i =
          (let
             i0 = vec_len slots
           in
             if usize_lt i i0 then
               do
                 l <- vec_index_mut_fwd slots i;
                 ls <<- mem_replace_fwd l HashmapListNil;
                 ntable0 <-
                   hashmap_hash_map_move_elements_from_list_fwd_back ntable
                     ls;
                 i1 <- usize_add i (int_to_usize 1);
                 l0 <<- mem_replace_back l HashmapListNil;
                 slots0 <- vec_index_mut_back slots i l0;
                 hashmap_hash_map_move_elements_loop_fwd_back ntable0
                   slots0 i1
               od
             else Return (ntable,slots))
   
   [hashmap_hash_map_new_fwd_def]  Definition
      
      ⊢ hashmap_hash_map_new_fwd =
        hashmap_hash_map_new_with_capacity_fwd (int_to_usize 32)
          (int_to_usize 4) (int_to_usize 5)
   
   [hashmap_hash_map_new_with_capacity_fwd_def]  Definition
      
      ⊢ ∀capacity max_load_dividend max_load_divisor.
          hashmap_hash_map_new_with_capacity_fwd capacity max_load_dividend
            max_load_divisor =
          (let
             v = vec_new
           in
             do
               slots <- hashmap_hash_map_allocate_slots_fwd v capacity;
               i <- usize_mul capacity max_load_dividend;
               i0 <- usize_div i max_load_divisor;
               Return
                 <|hashmap_hash_map_num_entries := int_to_usize 0;
                   hashmap_hash_map_max_load_factor :=
                     (max_load_dividend,max_load_divisor);
                   hashmap_hash_map_max_load := i0;
                   hashmap_hash_map_slots := slots|>
             od)
   
   [hashmap_hash_map_remove_back_def]  Definition
      
      ⊢ ∀self key.
          hashmap_hash_map_remove_back self key =
          do
            hash <- hashmap_hash_key_fwd key;
            i <<- vec_len self.hashmap_hash_map_slots;
            hash_mod <- usize_rem hash i;
            l <- vec_index_mut_fwd self.hashmap_hash_map_slots hash_mod;
            x <- hashmap_hash_map_remove_from_list_fwd key l;
            case x of
              NONE =>
                do
                  l0 <- hashmap_hash_map_remove_from_list_back key l;
                  v <-
                    vec_index_mut_back self.hashmap_hash_map_slots hash_mod
                      l0;
                  Return (self with hashmap_hash_map_slots := v)
                od
            | SOME x0 =>
              do
                i0 <-
                  usize_sub self.hashmap_hash_map_num_entries
                    (int_to_usize 1);
                l0 <- hashmap_hash_map_remove_from_list_back key l;
                v <-
                  vec_index_mut_back self.hashmap_hash_map_slots hash_mod
                    l0;
                Return
                  (self with
                   <|hashmap_hash_map_num_entries := i0;
                     hashmap_hash_map_slots := v|>)
              od
          od
   
   [hashmap_hash_map_remove_from_list_back_def]  Definition
      
      ⊢ ∀key ls.
          hashmap_hash_map_remove_from_list_back key ls =
          hashmap_hash_map_remove_from_list_loop_back key ls
   
   [hashmap_hash_map_remove_from_list_fwd_def]  Definition
      
      ⊢ ∀key ls.
          hashmap_hash_map_remove_from_list_fwd key ls =
          hashmap_hash_map_remove_from_list_loop_fwd key ls
   
   [hashmap_hash_map_remove_from_list_loop_back_def]  Definition
      
      ⊢ ∀key ls.
          hashmap_hash_map_remove_from_list_loop_back key ls =
          case ls of
            HashmapListCons ckey t tl =>
              if ckey = key then
                (let
                   mv_ls =
                     mem_replace_fwd (HashmapListCons ckey t tl)
                       HashmapListNil
                 in
                   case mv_ls of
                     HashmapListCons i cvalue tl0 => Return tl0
                   | HashmapListNil => Fail Failure)
              else
                do
                  tl0 <- hashmap_hash_map_remove_from_list_loop_back key tl;
                  Return (HashmapListCons ckey t tl0)
                od
          | HashmapListNil => Return HashmapListNil
   
   [hashmap_hash_map_remove_from_list_loop_fwd_def]  Definition
      
      ⊢ ∀key ls.
          hashmap_hash_map_remove_from_list_loop_fwd key ls =
          case ls of
            HashmapListCons ckey t tl =>
              if ckey = key then
                (let
                   mv_ls =
                     mem_replace_fwd (HashmapListCons ckey t tl)
                       HashmapListNil
                 in
                   case mv_ls of
                     HashmapListCons i cvalue tl0 => Return (SOME cvalue)
                   | HashmapListNil => Fail Failure)
              else hashmap_hash_map_remove_from_list_loop_fwd key tl
          | HashmapListNil => Return NONE
   
   [hashmap_hash_map_remove_fwd_def]  Definition
      
      ⊢ ∀self key.
          hashmap_hash_map_remove_fwd self key =
          do
            hash <- hashmap_hash_key_fwd key;
            i <<- vec_len self.hashmap_hash_map_slots;
            hash_mod <- usize_rem hash i;
            l <- vec_index_mut_fwd self.hashmap_hash_map_slots hash_mod;
            x <- hashmap_hash_map_remove_from_list_fwd key l;
            case x of
              NONE => Return NONE
            | SOME x0 =>
              monad_ignore_bind
                (usize_sub self.hashmap_hash_map_num_entries
                   (int_to_usize 1)) (Return (SOME x0))
          od
   
   [hashmap_hash_map_try_resize_fwd_back_def]  Definition
      
      ⊢ ∀self.
          hashmap_hash_map_try_resize_fwd_back self =
          do
            max_usize <- mk_usize (u32_to_int core_u32_max);
            capacity <<- vec_len self.hashmap_hash_map_slots;
            n1 <- usize_div max_usize (int_to_usize 2);
            (i,i0) <<- self.hashmap_hash_map_max_load_factor;
            i1 <- usize_div n1 i;
            if usize_le capacity i1 then
              do
                i2 <- usize_mul capacity (int_to_usize 2);
                ntable <- hashmap_hash_map_new_with_capacity_fwd i2 i i0;
                (ntable0,_) <-
                  hashmap_hash_map_move_elements_fwd_back ntable
                    self.hashmap_hash_map_slots (int_to_usize 0);
                Return
                  (ntable0 with
                   <|hashmap_hash_map_num_entries :=
                       self.hashmap_hash_map_num_entries;
                     hashmap_hash_map_max_load_factor := (i,i0)|>)
              od
            else
              Return (self with hashmap_hash_map_max_load_factor := (i,i0))
          od
   
   [hashmap_test1_fwd_def]  Definition
      
      ⊢ hashmap_test1_fwd =
        do
          hm <- hashmap_hash_map_new_fwd;
          hm0 <-
            hashmap_hash_map_insert_fwd_back hm (int_to_usize 0)
              (int_to_u64 42);
          hm1 <-
            hashmap_hash_map_insert_fwd_back hm0 (int_to_usize 128)
              (int_to_u64 18);
          hm2 <-
            hashmap_hash_map_insert_fwd_back hm1 (int_to_usize 1024)
              (int_to_u64 138);
          hm3 <-
            hashmap_hash_map_insert_fwd_back hm2 (int_to_usize 1056)
              (int_to_u64 256);
          i <- hashmap_hash_map_get_fwd hm3 (int_to_usize 128);
          if i ≠ int_to_u64 18 then Fail Failure
          else
            do
              hm4 <-
                hashmap_hash_map_get_mut_back hm3 (int_to_usize 1024)
                  (int_to_u64 56);
              i0 <- hashmap_hash_map_get_fwd hm4 (int_to_usize 1024);
              if i0 ≠ int_to_u64 56 then Fail Failure
              else
                do
                  x <- hashmap_hash_map_remove_fwd hm4 (int_to_usize 1024);
                  case x of
                    NONE => Fail Failure
                  | SOME x0 =>
                    if x0 ≠ int_to_u64 56 then Fail Failure
                    else
                      do
                        hm5 <-
                          hashmap_hash_map_remove_back hm4
                            (int_to_usize 1024);
                        i1 <- hashmap_hash_map_get_fwd hm5 (int_to_usize 0);
                        if i1 ≠ int_to_u64 42 then Fail Failure
                        else
                          do
                            i2 <-
                              hashmap_hash_map_get_fwd hm5
                                (int_to_usize 128);
                            if i2 ≠ int_to_u64 18 then Fail Failure
                            else
                              do
                                i3 <-
                                  hashmap_hash_map_get_fwd hm5
                                    (int_to_usize 1056);
                                if i3 ≠ int_to_u64 256 then Fail Failure
                                else Return ()
                              od
                          od
                      od
                od
            od
        od
   
   [insert_on_disk_fwd_def]  Definition
      
      ⊢ ∀key value st.
          insert_on_disk_fwd key value st =
          do
            (st0,hm) <- utils_deserialize_fwd st;
            hm0 <- hashmap_hash_map_insert_fwd_back hm key value;
            (st1,_) <- utils_serialize_fwd hm0 st0;
            Return (st1,())
          od
   
   [main_fwd_def]  Definition
      
      ⊢ main_fwd = Return ()
   
   
*)
end
