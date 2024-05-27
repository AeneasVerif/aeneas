signature betree_FunsTheory =
sig
  type thm = Thm.thm
  
  (*  Definitions  *)
    val betree_be_tree_apply_back_def : thm
    val betree_be_tree_apply_fwd_def : thm
    val betree_be_tree_delete_back_def : thm
    val betree_be_tree_delete_fwd_def : thm
    val betree_be_tree_insert_back_def : thm
    val betree_be_tree_insert_fwd_def : thm
    val betree_be_tree_lookup_back_def : thm
    val betree_be_tree_lookup_fwd_def : thm
    val betree_be_tree_new_fwd_def : thm
    val betree_be_tree_upsert_back_def : thm
    val betree_be_tree_upsert_fwd_def : thm
    val betree_fresh_node_id_back_def : thm
    val betree_fresh_node_id_fwd_def : thm
    val betree_internal_flush_back_def : thm
    val betree_internal_flush_fwd_def : thm
    val betree_internal_lookup_in_children_back_def : thm
    val betree_internal_lookup_in_children_fwd_def : thm
    val betree_leaf_split_back_def : thm
    val betree_leaf_split_fwd_def : thm
    val betree_list_hd_fwd_def : thm
    val betree_list_head_has_key_fwd_def : thm
    val betree_list_len_fwd_def : thm
    val betree_list_partition_at_pivot_fwd_def : thm
    val betree_list_pop_front_back_def : thm
    val betree_list_pop_front_fwd_def : thm
    val betree_list_push_front_fwd_back_def : thm
    val betree_list_split_at_fwd_def : thm
    val betree_load_internal_node_fwd_def : thm
    val betree_load_leaf_node_fwd_def : thm
    val betree_node_apply_back_def : thm
    val betree_node_apply_fwd_def : thm
    val betree_node_apply_messages_back_def : thm
    val betree_node_apply_messages_fwd_def : thm
    val betree_node_apply_messages_to_internal_fwd_back_def : thm
    val betree_node_apply_messages_to_leaf_fwd_back_def : thm
    val betree_node_apply_to_internal_fwd_back_def : thm
    val betree_node_apply_to_leaf_fwd_back_def : thm
    val betree_node_apply_upserts_back_def : thm
    val betree_node_apply_upserts_fwd_def : thm
    val betree_node_filter_messages_for_key_fwd_back_def : thm
    val betree_node_id_counter_fresh_id_back_def : thm
    val betree_node_id_counter_fresh_id_fwd_def : thm
    val betree_node_id_counter_new_fwd_def : thm
    val betree_node_lookup_back_def : thm
    val betree_node_lookup_first_message_after_key_back_def : thm
    val betree_node_lookup_first_message_after_key_fwd_def : thm
    val betree_node_lookup_first_message_for_key_back_def : thm
    val betree_node_lookup_first_message_for_key_fwd_def : thm
    val betree_node_lookup_fwd_def : thm
    val betree_node_lookup_in_bindings_fwd_def : thm
    val betree_node_lookup_mut_in_bindings_back_def : thm
    val betree_node_lookup_mut_in_bindings_fwd_def : thm
    val betree_store_internal_node_fwd_def : thm
    val betree_store_leaf_node_fwd_def : thm
    val betree_upsert_update_fwd_def : thm
    val main_fwd_def : thm
  
  val betree_Funs_grammars : type_grammar.grammar * term_grammar.grammar
(*
   [betree_Opaque] Parent theory of "betree_Funs"
   
   [betree_be_tree_apply_back_def]  Definition
      
      ⊢ ∀self key msg st.
          betree_be_tree_apply_back self key msg st =
          do
            (n,nic) <-
              betree_node_apply_back self.betree_be_tree_root
                self.betree_be_tree_params self.betree_be_tree_node_id_cnt
                key msg st;
            Return
              (self with
               <|betree_be_tree_node_id_cnt := nic;
                 betree_be_tree_root := n|>)
          od
   
   [betree_be_tree_apply_fwd_def]  Definition
      
      ⊢ ∀self key msg st.
          betree_be_tree_apply_fwd self key msg st =
          do
            (st0,_) <-
              betree_node_apply_fwd self.betree_be_tree_root
                self.betree_be_tree_params self.betree_be_tree_node_id_cnt
                key msg st;
            monad_ignore_bind
              (betree_node_apply_back self.betree_be_tree_root
                 self.betree_be_tree_params self.betree_be_tree_node_id_cnt
                 key msg st) (Return (st0,()))
          od
   
   [betree_be_tree_delete_back_def]  Definition
      
      ⊢ ∀self key st.
          betree_be_tree_delete_back self key st =
          betree_be_tree_apply_back self key BetreeMessageDelete st
   
   [betree_be_tree_delete_fwd_def]  Definition
      
      ⊢ ∀self key st.
          betree_be_tree_delete_fwd self key st =
          do
            (st0,_) <-
              betree_be_tree_apply_fwd self key BetreeMessageDelete st;
            monad_ignore_bind
              (betree_be_tree_apply_back self key BetreeMessageDelete st)
              (Return (st0,()))
          od
   
   [betree_be_tree_insert_back_def]  Definition
      
      ⊢ ∀self key value st.
          betree_be_tree_insert_back self key value st =
          betree_be_tree_apply_back self key (BetreeMessageInsert value) st
   
   [betree_be_tree_insert_fwd_def]  Definition
      
      ⊢ ∀self key value st.
          betree_be_tree_insert_fwd self key value st =
          do
            (st0,_) <-
              betree_be_tree_apply_fwd self key (BetreeMessageInsert value)
                st;
            monad_ignore_bind
              (betree_be_tree_apply_back self key
                 (BetreeMessageInsert value) st) (Return (st0,()))
          od
   
   [betree_be_tree_lookup_back_def]  Definition
      
      ⊢ ∀self key st.
          betree_be_tree_lookup_back self key st =
          do
            n <- betree_node_lookup_back self.betree_be_tree_root key st;
            Return (self with betree_be_tree_root := n)
          od
   
   [betree_be_tree_lookup_fwd_def]  Definition
      
      ⊢ ∀self key st.
          betree_be_tree_lookup_fwd self key st =
          betree_node_lookup_fwd self.betree_be_tree_root key st
   
   [betree_be_tree_new_fwd_def]  Definition
      
      ⊢ ∀min_flush_size split_size st.
          betree_be_tree_new_fwd min_flush_size split_size st =
          do
            node_id_cnt <- betree_node_id_counter_new_fwd;
            id <- betree_node_id_counter_fresh_id_fwd node_id_cnt;
            (st0,_) <- betree_store_leaf_node_fwd id BetreeListNil st;
            node_id_cnt0 <-
              betree_node_id_counter_fresh_id_back node_id_cnt;
            Return
              (st0,
               <|betree_be_tree_params :=
                   <|betree_params_min_flush_size := min_flush_size;
                     betree_params_split_size := split_size|>;
                 betree_be_tree_node_id_cnt := node_id_cnt0;
                 betree_be_tree_root :=
                   BetreeNodeLeaf
                     <|betree_leaf_id := id;
                       betree_leaf_size := int_to_u64 0|> |>)
          od
   
   [betree_be_tree_upsert_back_def]  Definition
      
      ⊢ ∀self key upd st.
          betree_be_tree_upsert_back self key upd st =
          betree_be_tree_apply_back self key (BetreeMessageUpsert upd) st
   
   [betree_be_tree_upsert_fwd_def]  Definition
      
      ⊢ ∀self key upd st.
          betree_be_tree_upsert_fwd self key upd st =
          do
            (st0,_) <-
              betree_be_tree_apply_fwd self key (BetreeMessageUpsert upd)
                st;
            monad_ignore_bind
              (betree_be_tree_apply_back self key (BetreeMessageUpsert upd)
                 st) (Return (st0,()))
          od
   
   [betree_fresh_node_id_back_def]  Definition
      
      ⊢ ∀counter.
          betree_fresh_node_id_back counter =
          u64_add counter (int_to_u64 1)
   
   [betree_fresh_node_id_fwd_def]  Definition
      
      ⊢ ∀counter.
          betree_fresh_node_id_fwd counter =
          monad_ignore_bind (u64_add counter (int_to_u64 1))
            (Return counter)
   
   [betree_internal_flush_back_def]  Definition
      
      ⊢ ∀self params node_id_cnt content st.
          betree_internal_flush_back self params node_id_cnt content st =
          do
            p <-
              betree_list_partition_at_pivot_fwd content
                self.betree_internal_pivot;
            (msgs_left,msgs_right) <<- p;
            len_left <- betree_list_len_fwd msgs_left;
            if u64_ge len_left params.betree_params_min_flush_size then
              do
                (st0,_) <-
                  betree_node_apply_messages_fwd self.betree_internal_left
                    params node_id_cnt msgs_left st;
                (n,node_id_cnt0) <-
                  betree_node_apply_messages_back self.betree_internal_left
                    params node_id_cnt msgs_left st;
                len_right <- betree_list_len_fwd msgs_right;
                if
                  u64_ge len_right params.betree_params_min_flush_size
                then
                  do
                    (n0,node_id_cnt1) <-
                      betree_node_apply_messages_back
                        self.betree_internal_right params node_id_cnt0
                        msgs_right st0;
                    Return
                      (self with
                       <|betree_internal_left := n;
                         betree_internal_right := n0|>,node_id_cnt1)
                  od
                else
                  Return (self with betree_internal_left := n,node_id_cnt0)
              od
            else
              do
                (n,node_id_cnt0) <-
                  betree_node_apply_messages_back
                    self.betree_internal_right params node_id_cnt
                    msgs_right st;
                Return (self with betree_internal_right := n,node_id_cnt0)
              od
          od
   
   [betree_internal_flush_fwd_def]  Definition
      
      ⊢ ∀self params node_id_cnt content st.
          betree_internal_flush_fwd self params node_id_cnt content st =
          do
            p <-
              betree_list_partition_at_pivot_fwd content
                self.betree_internal_pivot;
            (msgs_left,msgs_right) <<- p;
            len_left <- betree_list_len_fwd msgs_left;
            if u64_ge len_left params.betree_params_min_flush_size then
              do
                (st0,_) <-
                  betree_node_apply_messages_fwd self.betree_internal_left
                    params node_id_cnt msgs_left st;
                (_,node_id_cnt0) <-
                  betree_node_apply_messages_back self.betree_internal_left
                    params node_id_cnt msgs_left st;
                len_right <- betree_list_len_fwd msgs_right;
                if
                  u64_ge len_right params.betree_params_min_flush_size
                then
                  do
                    (st1,_) <-
                      betree_node_apply_messages_fwd
                        self.betree_internal_right params node_id_cnt0
                        msgs_right st0;
                    monad_ignore_bind
                      (betree_node_apply_messages_back
                         self.betree_internal_right params node_id_cnt0
                         msgs_right st0) (Return (st1,BetreeListNil))
                  od
                else Return (st0,msgs_right)
              od
            else
              do
                (st0,_) <-
                  betree_node_apply_messages_fwd self.betree_internal_right
                    params node_id_cnt msgs_right st;
                monad_ignore_bind
                  (betree_node_apply_messages_back
                     self.betree_internal_right params node_id_cnt
                     msgs_right st) (Return (st0,msgs_left))
              od
          od
   
   [betree_internal_lookup_in_children_back_def]  Definition
      
      ⊢ ∀self key st.
          betree_internal_lookup_in_children_back self key st =
          if u64_lt key self.betree_internal_pivot then
            do
              n <- betree_node_lookup_back self.betree_internal_left key st;
              Return (self with betree_internal_left := n)
            od
          else
            do
              n <-
                betree_node_lookup_back self.betree_internal_right key st;
              Return (self with betree_internal_right := n)
            od
   
   [betree_internal_lookup_in_children_fwd_def]  Definition
      
      ⊢ ∀self key st.
          betree_internal_lookup_in_children_fwd self key st =
          if u64_lt key self.betree_internal_pivot then
            betree_node_lookup_fwd self.betree_internal_left key st
          else betree_node_lookup_fwd self.betree_internal_right key st
   
   [betree_leaf_split_back_def]  Definition
      
      ⊢ ∀self content params node_id_cnt st.
          betree_leaf_split_back self content params node_id_cnt st =
          do
            p <-
              betree_list_split_at_fwd content
                params.betree_params_split_size;
            (content0,content1) <<- p;
            monad_ignore_bind (betree_list_hd_fwd content1)
              do
                id0 <- betree_node_id_counter_fresh_id_fwd node_id_cnt;
                node_id_cnt0 <-
                  betree_node_id_counter_fresh_id_back node_id_cnt;
                id1 <- betree_node_id_counter_fresh_id_fwd node_id_cnt0;
                (st0,_) <- betree_store_leaf_node_fwd id0 content0 st;
                monad_ignore_bind
                  (betree_store_leaf_node_fwd id1 content1 st0)
                  (betree_node_id_counter_fresh_id_back node_id_cnt0)
              od
          od
   
   [betree_leaf_split_fwd_def]  Definition
      
      ⊢ ∀self content params node_id_cnt st.
          betree_leaf_split_fwd self content params node_id_cnt st =
          do
            p <-
              betree_list_split_at_fwd content
                params.betree_params_split_size;
            (content0,content1) <<- p;
            p0 <- betree_list_hd_fwd content1;
            (pivot,_) <<- p0;
            id0 <- betree_node_id_counter_fresh_id_fwd node_id_cnt;
            node_id_cnt0 <-
              betree_node_id_counter_fresh_id_back node_id_cnt;
            id1 <- betree_node_id_counter_fresh_id_fwd node_id_cnt0;
            (st0,_) <- betree_store_leaf_node_fwd id0 content0 st;
            (st1,_) <- betree_store_leaf_node_fwd id1 content1 st0;
            n <<-
              BetreeNodeLeaf
                <|betree_leaf_id := id0;
                  betree_leaf_size := params.betree_params_split_size|>;
            n0 <<-
              BetreeNodeLeaf
                <|betree_leaf_id := id1;
                  betree_leaf_size := params.betree_params_split_size|>;
            Return
              (st1,
               <|betree_internal_id := self.betree_leaf_id;
                 betree_internal_pivot := pivot; betree_internal_left := n;
                 betree_internal_right := n0|>)
          od
   
   [betree_list_hd_fwd_def]  Definition
      
      ⊢ ∀self.
          betree_list_hd_fwd self =
          case self of
            BetreeListCons hd l => Return hd
          | BetreeListNil => Fail Failure
   
   [betree_list_head_has_key_fwd_def]  Definition
      
      ⊢ ∀self key.
          betree_list_head_has_key_fwd self key =
          case self of
            BetreeListCons hd l => (let (i,_) = hd in Return (i = key))
          | BetreeListNil => Return F
   
   [betree_list_len_fwd_def]  Definition
      
      ⊢ ∀self.
          betree_list_len_fwd self =
          case self of
            BetreeListCons t tl =>
              do i <- betree_list_len_fwd tl; u64_add (int_to_u64 1) i od
          | BetreeListNil => Return (int_to_u64 0)
   
   [betree_list_partition_at_pivot_fwd_def]  Definition
      
      ⊢ ∀self pivot.
          betree_list_partition_at_pivot_fwd self pivot =
          case self of
            BetreeListCons hd tl =>
              (let
                 (i,t) = hd
               in
                 if u64_ge i pivot then
                   Return (BetreeListNil,BetreeListCons (i,t) tl)
                 else
                   do
                     p <- betree_list_partition_at_pivot_fwd tl pivot;
                     (ls0,ls1) <<- p;
                     l <<- ls0;
                     Return (BetreeListCons (i,t) l,ls1)
                   od)
          | BetreeListNil => Return (BetreeListNil,BetreeListNil)
   
   [betree_list_pop_front_back_def]  Definition
      
      ⊢ ∀self.
          betree_list_pop_front_back self =
          (let
             ls = mem_replace_fwd self BetreeListNil
           in
             case ls of
               BetreeListCons x tl => Return tl
             | BetreeListNil => Fail Failure)
   
   [betree_list_pop_front_fwd_def]  Definition
      
      ⊢ ∀self.
          betree_list_pop_front_fwd self =
          (let
             ls = mem_replace_fwd self BetreeListNil
           in
             case ls of
               BetreeListCons x tl => Return x
             | BetreeListNil => Fail Failure)
   
   [betree_list_push_front_fwd_back_def]  Definition
      
      ⊢ ∀self x.
          betree_list_push_front_fwd_back self x =
          (let
             tl = mem_replace_fwd self BetreeListNil;
             l = tl
           in
             Return (BetreeListCons x l))
   
   [betree_list_split_at_fwd_def]  Definition
      
      ⊢ ∀self n.
          betree_list_split_at_fwd self n =
          if n = int_to_u64 0 then Return (BetreeListNil,self)
          else
            case self of
              BetreeListCons hd tl =>
                do
                  i <- u64_sub n (int_to_u64 1);
                  p <- betree_list_split_at_fwd tl i;
                  (ls0,ls1) <<- p;
                  l <<- ls0;
                  Return (BetreeListCons hd l,ls1)
                od
            | BetreeListNil => Fail Failure
   
   [betree_load_internal_node_fwd_def]  Definition
      
      ⊢ ∀id st.
          betree_load_internal_node_fwd id st =
          betree_utils_load_internal_node_fwd id st
   
   [betree_load_leaf_node_fwd_def]  Definition
      
      ⊢ ∀id st.
          betree_load_leaf_node_fwd id st =
          betree_utils_load_leaf_node_fwd id st
   
   [betree_node_apply_back_def]  Definition
      
      ⊢ ∀self params node_id_cnt key new_msg st.
          betree_node_apply_back self params node_id_cnt key new_msg st =
          (let
             l = BetreeListNil
           in
             betree_node_apply_messages_back self params node_id_cnt
               (BetreeListCons (key,new_msg) l) st)
   
   [betree_node_apply_fwd_def]  Definition
      
      ⊢ ∀self params node_id_cnt key new_msg st.
          betree_node_apply_fwd self params node_id_cnt key new_msg st =
          (let
             l = BetreeListNil
           in
             do
               (st0,_) <-
                 betree_node_apply_messages_fwd self params node_id_cnt
                   (BetreeListCons (key,new_msg) l) st;
               monad_ignore_bind
                 (betree_node_apply_messages_back self params node_id_cnt
                    (BetreeListCons (key,new_msg) l) st) (Return (st0,()))
             od)
   
   [betree_node_apply_messages_back_def]  Definition
      
      ⊢ ∀self params node_id_cnt msgs st.
          betree_node_apply_messages_back self params node_id_cnt msgs st =
          case self of
            BetreeNodeInternal node =>
              do
                (st0,content) <-
                  betree_load_internal_node_fwd node.betree_internal_id st;
                content0 <-
                  betree_node_apply_messages_to_internal_fwd_back content
                    msgs;
                num_msgs <- betree_list_len_fwd content0;
                if u64_ge num_msgs params.betree_params_min_flush_size then
                  do
                    (st1,content1) <-
                      betree_internal_flush_fwd node params node_id_cnt
                        content0 st0;
                    (node0,node_id_cnt0) <-
                      betree_internal_flush_back node params node_id_cnt
                        content0 st0;
                    monad_ignore_bind
                      (betree_store_internal_node_fwd
                         node0.betree_internal_id content1 st1)
                      (Return (BetreeNodeInternal node0,node_id_cnt0))
                  od
                else
                  monad_ignore_bind
                    (betree_store_internal_node_fwd node.betree_internal_id
                       content0 st0)
                    (Return (BetreeNodeInternal node,node_id_cnt))
              od
          | BetreeNodeLeaf node' =>
            do
              (st0,content) <-
                betree_load_leaf_node_fwd node'.betree_leaf_id st;
              content0 <-
                betree_node_apply_messages_to_leaf_fwd_back content msgs;
              len <- betree_list_len_fwd content0;
              i <- u64_mul (int_to_u64 2) params.betree_params_split_size;
              if u64_ge len i then
                do
                  (st1,new_node) <-
                    betree_leaf_split_fwd node' content0 params node_id_cnt
                      st0;
                  monad_ignore_bind
                    (betree_store_leaf_node_fwd node'.betree_leaf_id
                       BetreeListNil st1)
                    do
                      node_id_cnt0 <-
                        betree_leaf_split_back node' content0 params
                          node_id_cnt st0;
                      Return (BetreeNodeInternal new_node,node_id_cnt0)
                    od
                od
              else
                monad_ignore_bind
                  (betree_store_leaf_node_fwd node'.betree_leaf_id content0
                     st0)
                  (Return
                     (BetreeNodeLeaf (node' with betree_leaf_size := len),
                      node_id_cnt))
            od
   
   [betree_node_apply_messages_fwd_def]  Definition
      
      ⊢ ∀self params node_id_cnt msgs st.
          betree_node_apply_messages_fwd self params node_id_cnt msgs st =
          case self of
            BetreeNodeInternal node =>
              do
                (st0,content) <-
                  betree_load_internal_node_fwd node.betree_internal_id st;
                content0 <-
                  betree_node_apply_messages_to_internal_fwd_back content
                    msgs;
                num_msgs <- betree_list_len_fwd content0;
                if u64_ge num_msgs params.betree_params_min_flush_size then
                  do
                    (st1,content1) <-
                      betree_internal_flush_fwd node params node_id_cnt
                        content0 st0;
                    (node0,_) <-
                      betree_internal_flush_back node params node_id_cnt
                        content0 st0;
                    (st2,_) <-
                      betree_store_internal_node_fwd
                        node0.betree_internal_id content1 st1;
                    Return (st2,())
                  od
                else
                  do
                    (st1,_) <-
                      betree_store_internal_node_fwd
                        node.betree_internal_id content0 st0;
                    Return (st1,())
                  od
              od
          | BetreeNodeLeaf node' =>
            do
              (st0,content) <-
                betree_load_leaf_node_fwd node'.betree_leaf_id st;
              content0 <-
                betree_node_apply_messages_to_leaf_fwd_back content msgs;
              len <- betree_list_len_fwd content0;
              i <- u64_mul (int_to_u64 2) params.betree_params_split_size;
              if u64_ge len i then
                do
                  (st1,_) <-
                    betree_leaf_split_fwd node' content0 params node_id_cnt
                      st0;
                  (st2,_) <-
                    betree_store_leaf_node_fwd node'.betree_leaf_id
                      BetreeListNil st1;
                  Return (st2,())
                od
              else
                do
                  (st1,_) <-
                    betree_store_leaf_node_fwd node'.betree_leaf_id
                      content0 st0;
                  Return (st1,())
                od
            od
   
   [betree_node_apply_messages_to_internal_fwd_back_def]  Definition
      
      ⊢ ∀msgs new_msgs.
          betree_node_apply_messages_to_internal_fwd_back msgs new_msgs =
          case new_msgs of
            BetreeListCons new_msg new_msgs_tl =>
              (let
                 (i,m) = new_msg
               in
                 do
                   msgs0 <- betree_node_apply_to_internal_fwd_back msgs i m;
                   betree_node_apply_messages_to_internal_fwd_back msgs0
                     new_msgs_tl
                 od)
          | BetreeListNil => Return msgs
   
   [betree_node_apply_messages_to_leaf_fwd_back_def]  Definition
      
      ⊢ ∀bindings new_msgs.
          betree_node_apply_messages_to_leaf_fwd_back bindings new_msgs =
          case new_msgs of
            BetreeListCons new_msg new_msgs_tl =>
              (let
                 (i,m) = new_msg
               in
                 do
                   bindings0 <-
                     betree_node_apply_to_leaf_fwd_back bindings i m;
                   betree_node_apply_messages_to_leaf_fwd_back bindings0
                     new_msgs_tl
                 od)
          | BetreeListNil => Return bindings
   
   [betree_node_apply_to_internal_fwd_back_def]  Definition
      
      ⊢ ∀msgs key new_msg.
          betree_node_apply_to_internal_fwd_back msgs key new_msg =
          do
            msgs0 <- betree_node_lookup_first_message_for_key_fwd key msgs;
            b <- betree_list_head_has_key_fwd msgs0 key;
            if b then
              case new_msg of
                BetreeMessageInsert i =>
                  do
                    msgs1 <-
                      betree_node_filter_messages_for_key_fwd_back key
                        msgs0;
                    msgs2 <-
                      betree_list_push_front_fwd_back msgs1
                        (key,BetreeMessageInsert i);
                    betree_node_lookup_first_message_for_key_back key msgs
                      msgs2
                  od
              | BetreeMessageDelete =>
                do
                  msgs1 <-
                    betree_node_filter_messages_for_key_fwd_back key msgs0;
                  msgs2 <-
                    betree_list_push_front_fwd_back msgs1
                      (key,BetreeMessageDelete);
                  betree_node_lookup_first_message_for_key_back key msgs
                    msgs2
                od
              | BetreeMessageUpsert s =>
                do
                  p <- betree_list_hd_fwd msgs0;
                  (_,m) <<- p;
                  case m of
                    BetreeMessageInsert prev =>
                      do
                        v <- betree_upsert_update_fwd (SOME prev) s;
                        msgs1 <- betree_list_pop_front_back msgs0;
                        msgs2 <-
                          betree_list_push_front_fwd_back msgs1
                            (key,BetreeMessageInsert v);
                        betree_node_lookup_first_message_for_key_back key
                          msgs msgs2
                      od
                  | BetreeMessageDelete =>
                    do
                      v <- betree_upsert_update_fwd NONE s;
                      msgs1 <- betree_list_pop_front_back msgs0;
                      msgs2 <-
                        betree_list_push_front_fwd_back msgs1
                          (key,BetreeMessageInsert v);
                      betree_node_lookup_first_message_for_key_back key
                        msgs msgs2
                    od
                  | BetreeMessageUpsert ufs =>
                    do
                      msgs1 <-
                        betree_node_lookup_first_message_after_key_fwd key
                          msgs0;
                      msgs2 <-
                        betree_list_push_front_fwd_back msgs1
                          (key,BetreeMessageUpsert s);
                      msgs3 <-
                        betree_node_lookup_first_message_after_key_back key
                          msgs0 msgs2;
                      betree_node_lookup_first_message_for_key_back key
                        msgs msgs3
                    od
                od
            else
              do
                msgs1 <-
                  betree_list_push_front_fwd_back msgs0 (key,new_msg);
                betree_node_lookup_first_message_for_key_back key msgs
                  msgs1
              od
          od
   
   [betree_node_apply_to_leaf_fwd_back_def]  Definition
      
      ⊢ ∀bindings key new_msg.
          betree_node_apply_to_leaf_fwd_back bindings key new_msg =
          do
            bindings0 <-
              betree_node_lookup_mut_in_bindings_fwd key bindings;
            b <- betree_list_head_has_key_fwd bindings0 key;
            if b then
              do
                hd <- betree_list_pop_front_fwd bindings0;
                case new_msg of
                  BetreeMessageInsert v =>
                    do
                      bindings1 <- betree_list_pop_front_back bindings0;
                      bindings2 <-
                        betree_list_push_front_fwd_back bindings1 (key,v);
                      betree_node_lookup_mut_in_bindings_back key bindings
                        bindings2
                    od
                | BetreeMessageDelete =>
                  do
                    bindings1 <- betree_list_pop_front_back bindings0;
                    betree_node_lookup_mut_in_bindings_back key bindings
                      bindings1
                  od
                | BetreeMessageUpsert s =>
                  (let
                     (_,i) = hd
                   in
                     do
                       v <- betree_upsert_update_fwd (SOME i) s;
                       bindings1 <- betree_list_pop_front_back bindings0;
                       bindings2 <-
                         betree_list_push_front_fwd_back bindings1 (key,v);
                       betree_node_lookup_mut_in_bindings_back key bindings
                         bindings2
                     od)
              od
            else
              case new_msg of
                BetreeMessageInsert v =>
                  do
                    bindings1 <-
                      betree_list_push_front_fwd_back bindings0 (key,v);
                    betree_node_lookup_mut_in_bindings_back key bindings
                      bindings1
                  od
              | BetreeMessageDelete =>
                betree_node_lookup_mut_in_bindings_back key bindings
                  bindings0
              | BetreeMessageUpsert s =>
                do
                  v <- betree_upsert_update_fwd NONE s;
                  bindings1 <-
                    betree_list_push_front_fwd_back bindings0 (key,v);
                  betree_node_lookup_mut_in_bindings_back key bindings
                    bindings1
                od
          od
   
   [betree_node_apply_upserts_back_def]  Definition
      
      ⊢ ∀msgs prev key st.
          betree_node_apply_upserts_back msgs prev key st =
          do
            b <- betree_list_head_has_key_fwd msgs key;
            if b then
              do
                msg <- betree_list_pop_front_fwd msgs;
                (_,m) <<- msg;
                case m of
                  BetreeMessageInsert i => Fail Failure
                | BetreeMessageDelete => Fail Failure
                | BetreeMessageUpsert s =>
                  do
                    v <- betree_upsert_update_fwd prev s;
                    msgs0 <- betree_list_pop_front_back msgs;
                    betree_node_apply_upserts_back msgs0 (SOME v) key st
                  od
              od
            else
              do
                (_,v) <- core_option_option_unwrap_fwd prev st;
                betree_list_push_front_fwd_back msgs
                  (key,BetreeMessageInsert v)
              od
          od
   
   [betree_node_apply_upserts_fwd_def]  Definition
      
      ⊢ ∀msgs prev key st.
          betree_node_apply_upserts_fwd msgs prev key st =
          do
            b <- betree_list_head_has_key_fwd msgs key;
            if b then
              do
                msg <- betree_list_pop_front_fwd msgs;
                (_,m) <<- msg;
                case m of
                  BetreeMessageInsert i => Fail Failure
                | BetreeMessageDelete => Fail Failure
                | BetreeMessageUpsert s =>
                  do
                    v <- betree_upsert_update_fwd prev s;
                    msgs0 <- betree_list_pop_front_back msgs;
                    betree_node_apply_upserts_fwd msgs0 (SOME v) key st
                  od
              od
            else
              do
                (st0,v) <- core_option_option_unwrap_fwd prev st;
                monad_ignore_bind
                  (betree_list_push_front_fwd_back msgs
                     (key,BetreeMessageInsert v)) (Return (st0,v))
              od
          od
   
   [betree_node_filter_messages_for_key_fwd_back_def]  Definition
      
      ⊢ ∀key msgs.
          betree_node_filter_messages_for_key_fwd_back key msgs =
          case msgs of
            BetreeListCons p l =>
              (let
                 (k,m) = p
               in
                 if k = key then
                   do
                     msgs0 <-
                       betree_list_pop_front_back (BetreeListCons (k,m) l);
                     betree_node_filter_messages_for_key_fwd_back key msgs0
                   od
                 else Return (BetreeListCons (k,m) l))
          | BetreeListNil => Return BetreeListNil
   
   [betree_node_id_counter_fresh_id_back_def]  Definition
      
      ⊢ ∀self.
          betree_node_id_counter_fresh_id_back self =
          do
            i <-
              u64_add self.betree_node_id_counter_next_node_id
                (int_to_u64 1);
            Return <|betree_node_id_counter_next_node_id := i|>
          od
   
   [betree_node_id_counter_fresh_id_fwd_def]  Definition
      
      ⊢ ∀self.
          betree_node_id_counter_fresh_id_fwd self =
          monad_ignore_bind
            (u64_add self.betree_node_id_counter_next_node_id
               (int_to_u64 1))
            (Return self.betree_node_id_counter_next_node_id)
   
   [betree_node_id_counter_new_fwd_def]  Definition
      
      ⊢ betree_node_id_counter_new_fwd =
        Return <|betree_node_id_counter_next_node_id := int_to_u64 0|>
   
   [betree_node_lookup_back_def]  Definition
      
      ⊢ ∀self key st.
          betree_node_lookup_back self key st =
          case self of
            BetreeNodeInternal node =>
              do
                (st0,msgs) <-
                  betree_load_internal_node_fwd node.betree_internal_id st;
                pending <-
                  betree_node_lookup_first_message_for_key_fwd key msgs;
                case pending of
                  BetreeListCons p l =>
                    (let
                       (k,msg) = p
                     in
                       if k ≠ key then
                         monad_ignore_bind
                           (betree_node_lookup_first_message_for_key_back
                              key msgs (BetreeListCons (k,msg) l))
                           do
                             node0 <-
                               betree_internal_lookup_in_children_back node
                                 key st0;
                             Return (BetreeNodeInternal node0)
                           od
                       else
                         case msg of
                           BetreeMessageInsert v =>
                             monad_ignore_bind
                               (betree_node_lookup_first_message_for_key_back
                                  key msgs
                                  (BetreeListCons (k,BetreeMessageInsert v)
                                     l)) (Return (BetreeNodeInternal node))
                         | BetreeMessageDelete =>
                           monad_ignore_bind
                             (betree_node_lookup_first_message_for_key_back
                                key msgs
                                (BetreeListCons (k,BetreeMessageDelete) l))
                             (Return (BetreeNodeInternal node))
                         | BetreeMessageUpsert ufs =>
                           do
                             (st1,v) <-
                               betree_internal_lookup_in_children_fwd node
                                 key st0;
                             (st2,_) <-
                               betree_node_apply_upserts_fwd
                                 (BetreeListCons
                                    (k,BetreeMessageUpsert ufs) l) v key
                                 st1;
                             node0 <-
                               betree_internal_lookup_in_children_back node
                                 key st0;
                             pending0 <-
                               betree_node_apply_upserts_back
                                 (BetreeListCons
                                    (k,BetreeMessageUpsert ufs) l) v key
                                 st1;
                             msgs0 <-
                               betree_node_lookup_first_message_for_key_back
                                 key msgs pending0;
                             monad_ignore_bind
                               (betree_store_internal_node_fwd
                                  node0.betree_internal_id msgs0 st2)
                               (Return (BetreeNodeInternal node0))
                           od)
                | BetreeListNil =>
                  monad_ignore_bind
                    (betree_node_lookup_first_message_for_key_back key msgs
                       BetreeListNil)
                    do
                      node0 <-
                        betree_internal_lookup_in_children_back node key
                          st0;
                      Return (BetreeNodeInternal node0)
                    od
              od
          | BetreeNodeLeaf node' =>
            do
              (_,bindings) <-
                betree_load_leaf_node_fwd node'.betree_leaf_id st;
              monad_ignore_bind
                (betree_node_lookup_in_bindings_fwd key bindings)
                (Return (BetreeNodeLeaf node'))
            od
   
   [betree_node_lookup_first_message_after_key_back_def]  Definition
      
      ⊢ ∀key msgs ret.
          betree_node_lookup_first_message_after_key_back key msgs ret =
          case msgs of
            BetreeListCons p next_msgs =>
              (let
                 (k,m) = p
               in
                 if k = key then
                   do
                     next_msgs0 <-
                       betree_node_lookup_first_message_after_key_back key
                         next_msgs ret;
                     Return (BetreeListCons (k,m) next_msgs0)
                   od
                 else Return ret)
          | BetreeListNil => Return ret
   
   [betree_node_lookup_first_message_after_key_fwd_def]  Definition
      
      ⊢ ∀key msgs.
          betree_node_lookup_first_message_after_key_fwd key msgs =
          case msgs of
            BetreeListCons p next_msgs =>
              (let
                 (k,m) = p
               in
                 if k = key then
                   betree_node_lookup_first_message_after_key_fwd key
                     next_msgs
                 else Return (BetreeListCons (k,m) next_msgs))
          | BetreeListNil => Return BetreeListNil
   
   [betree_node_lookup_first_message_for_key_back_def]  Definition
      
      ⊢ ∀key msgs ret.
          betree_node_lookup_first_message_for_key_back key msgs ret =
          case msgs of
            BetreeListCons x next_msgs =>
              (let
                 (i,m) = x
               in
                 if u64_ge i key then Return ret
                 else
                   do
                     next_msgs0 <-
                       betree_node_lookup_first_message_for_key_back key
                         next_msgs ret;
                     Return (BetreeListCons (i,m) next_msgs0)
                   od)
          | BetreeListNil => Return ret
   
   [betree_node_lookup_first_message_for_key_fwd_def]  Definition
      
      ⊢ ∀key msgs.
          betree_node_lookup_first_message_for_key_fwd key msgs =
          case msgs of
            BetreeListCons x next_msgs =>
              (let
                 (i,m) = x
               in
                 if u64_ge i key then
                   Return (BetreeListCons (i,m) next_msgs)
                 else
                   betree_node_lookup_first_message_for_key_fwd key
                     next_msgs)
          | BetreeListNil => Return BetreeListNil
   
   [betree_node_lookup_fwd_def]  Definition
      
      ⊢ ∀self key st.
          betree_node_lookup_fwd self key st =
          case self of
            BetreeNodeInternal node =>
              do
                (st0,msgs) <-
                  betree_load_internal_node_fwd node.betree_internal_id st;
                pending <-
                  betree_node_lookup_first_message_for_key_fwd key msgs;
                case pending of
                  BetreeListCons p l =>
                    (let
                       (k,msg) = p
                     in
                       if k ≠ key then
                         do
                           (st1,opt) <-
                             betree_internal_lookup_in_children_fwd node
                               key st0;
                           monad_ignore_bind
                             (betree_node_lookup_first_message_for_key_back
                                key msgs (BetreeListCons (k,msg) l))
                             (Return (st1,opt))
                         od
                       else
                         case msg of
                           BetreeMessageInsert v =>
                             monad_ignore_bind
                               (betree_node_lookup_first_message_for_key_back
                                  key msgs
                                  (BetreeListCons (k,BetreeMessageInsert v)
                                     l)) (Return (st0,SOME v))
                         | BetreeMessageDelete =>
                           monad_ignore_bind
                             (betree_node_lookup_first_message_for_key_back
                                key msgs
                                (BetreeListCons (k,BetreeMessageDelete) l))
                             (Return (st0,NONE))
                         | BetreeMessageUpsert ufs =>
                           do
                             (st1,v) <-
                               betree_internal_lookup_in_children_fwd node
                                 key st0;
                             (st2,v0) <-
                               betree_node_apply_upserts_fwd
                                 (BetreeListCons
                                    (k,BetreeMessageUpsert ufs) l) v key
                                 st1;
                             node0 <-
                               betree_internal_lookup_in_children_back node
                                 key st0;
                             pending0 <-
                               betree_node_apply_upserts_back
                                 (BetreeListCons
                                    (k,BetreeMessageUpsert ufs) l) v key
                                 st1;
                             msgs0 <-
                               betree_node_lookup_first_message_for_key_back
                                 key msgs pending0;
                             (st3,_) <-
                               betree_store_internal_node_fwd
                                 node0.betree_internal_id msgs0 st2;
                             Return (st3,SOME v0)
                           od)
                | BetreeListNil =>
                  do
                    (st1,opt) <-
                      betree_internal_lookup_in_children_fwd node key st0;
                    monad_ignore_bind
                      (betree_node_lookup_first_message_for_key_back key
                         msgs BetreeListNil) (Return (st1,opt))
                  od
              od
          | BetreeNodeLeaf node' =>
            do
              (st0,bindings) <-
                betree_load_leaf_node_fwd node'.betree_leaf_id st;
              opt <- betree_node_lookup_in_bindings_fwd key bindings;
              Return (st0,opt)
            od
   
   [betree_node_lookup_in_bindings_fwd_def]  Definition
      
      ⊢ ∀key bindings.
          betree_node_lookup_in_bindings_fwd key bindings =
          case bindings of
            BetreeListCons hd tl =>
              (let
                 (i,i0) = hd
               in
                 if i = key then Return (SOME i0)
                 else if u64_gt i key then Return NONE
                 else betree_node_lookup_in_bindings_fwd key tl)
          | BetreeListNil => Return NONE
   
   [betree_node_lookup_mut_in_bindings_back_def]  Definition
      
      ⊢ ∀key bindings ret.
          betree_node_lookup_mut_in_bindings_back key bindings ret =
          case bindings of
            BetreeListCons hd tl =>
              (let
                 (i,i0) = hd
               in
                 if u64_ge i key then Return ret
                 else
                   do
                     tl0 <-
                       betree_node_lookup_mut_in_bindings_back key tl ret;
                     Return (BetreeListCons (i,i0) tl0)
                   od)
          | BetreeListNil => Return ret
   
   [betree_node_lookup_mut_in_bindings_fwd_def]  Definition
      
      ⊢ ∀key bindings.
          betree_node_lookup_mut_in_bindings_fwd key bindings =
          case bindings of
            BetreeListCons hd tl =>
              (let
                 (i,i0) = hd
               in
                 if u64_ge i key then Return (BetreeListCons (i,i0) tl)
                 else betree_node_lookup_mut_in_bindings_fwd key tl)
          | BetreeListNil => Return BetreeListNil
   
   [betree_store_internal_node_fwd_def]  Definition
      
      ⊢ ∀id content st.
          betree_store_internal_node_fwd id content st =
          do
            (st0,_) <- betree_utils_store_internal_node_fwd id content st;
            Return (st0,())
          od
   
   [betree_store_leaf_node_fwd_def]  Definition
      
      ⊢ ∀id content st.
          betree_store_leaf_node_fwd id content st =
          do
            (st0,_) <- betree_utils_store_leaf_node_fwd id content st;
            Return (st0,())
          od
   
   [betree_upsert_update_fwd_def]  Definition
      
      ⊢ ∀prev st.
          betree_upsert_update_fwd prev st =
          case prev of
            NONE =>
              (case st of
                 BetreeUpsertFunStateAdd v => Return v
               | BetreeUpsertFunStateSub i => Return (int_to_u64 0))
          | SOME prev0 =>
            case st of
              BetreeUpsertFunStateAdd v =>
                do
                  margin <- u64_sub core_u64_max prev0;
                  if u64_ge margin v then u64_add prev0 v
                  else Return core_u64_max
                od
            | BetreeUpsertFunStateSub v' =>
              if u64_ge prev0 v' then u64_sub prev0 v'
              else Return (int_to_u64 0)
   
   [main_fwd_def]  Definition
      
      ⊢ main_fwd = Return ()
   
   
*)
end
