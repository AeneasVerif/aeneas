(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [betree]: function definitions *)
module Betree.Funs
open Primitives
include Betree.Types
include Betree.FunsExternal
include Betree.Clauses

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [betree::betree::load_internal_node]:
    Source: 'src/betree.rs', lines 36:0-38:1 *)
let betree_load_internal_node
  (id : u64) (st : state) :
  result (state & (betree_List_t (u64 & betree_Message_t)))
  =
  betree_utils_load_internal_node id st

(** [betree::betree::store_internal_node]:
    Source: 'src/betree.rs', lines 41:0-43:1 *)
let betree_store_internal_node
  (id : u64) (content : betree_List_t (u64 & betree_Message_t)) (st : state) :
  result (state & unit)
  =
  betree_utils_store_internal_node id content st

(** [betree::betree::load_leaf_node]:
    Source: 'src/betree.rs', lines 46:0-48:1 *)
let betree_load_leaf_node
  (id : u64) (st : state) : result (state & (betree_List_t (u64 & u64))) =
  betree_utils_load_leaf_node id st

(** [betree::betree::store_leaf_node]:
    Source: 'src/betree.rs', lines 51:0-53:1 *)
let betree_store_leaf_node
  (id : u64) (content : betree_List_t (u64 & u64)) (st : state) :
  result (state & unit)
  =
  betree_utils_store_leaf_node id content st

(** [betree::betree::fresh_node_id]:
    Source: 'src/betree.rs', lines 55:0-59:1 *)
let betree_fresh_node_id (counter : u64) : result (u64 & u64) =
  let* counter1 = u64_add counter 1 in Ok (counter, counter1)

(** [betree::betree::{betree::betree::NodeIdCounter}::new]:
    Source: 'src/betree.rs', lines 206:4-208:5 *)
let betree_NodeIdCounter_new : result betree_NodeIdCounter_t =
  Ok { next_node_id = 0 }

(** [betree::betree::{betree::betree::NodeIdCounter}::fresh_id]:
    Source: 'src/betree.rs', lines 210:4-214:5 *)
let betree_NodeIdCounter_fresh_id
  (self : betree_NodeIdCounter_t) : result (u64 & betree_NodeIdCounter_t) =
  let* i = u64_add self.next_node_id 1 in
  Ok (self.next_node_id, { next_node_id = i })

(** [betree::betree::upsert_update]:
    Source: 'src/betree.rs', lines 234:0-273:1 *)
let betree_upsert_update
  (prev : option u64) (st : betree_UpsertFunState_t) : result u64 =
  begin match prev with
  | None ->
    begin match st with
    | Betree_UpsertFunState_Add v -> Ok v
    | Betree_UpsertFunState_Sub _ -> Ok 0
    end
  | Some prev1 ->
    begin match st with
    | Betree_UpsertFunState_Add v ->
      let* margin = u64_sub core_u64_max prev1 in
      if margin >= v then u64_add prev1 v else Ok core_u64_max
    | Betree_UpsertFunState_Sub v ->
      if prev1 >= v then u64_sub prev1 v else Ok 0
    end
  end

(** [betree::betree::{betree::betree::List<T>}#1::len]: loop 0:
    Source: 'src/betree.rs', lines 279:8-282:9 *)
let rec betree_List_len_loop
  (#t : Type0) (self : betree_List_t t) (len : u64) :
  Tot (result u64) (decreases (betree_List_len_loop_decreases self len))
  =
  begin match self with
  | Betree_List_Cons _ tl ->
    let* len1 = u64_add len 1 in betree_List_len_loop tl len1
  | Betree_List_Nil -> Ok len
  end

(** [betree::betree::{betree::betree::List<T>}#1::len]:
    Source: 'src/betree.rs', lines 276:4-284:5 *)
let betree_List_len (#t : Type0) (self : betree_List_t t) : result u64 =
  betree_List_len_loop self 0

(** [betree::betree::{betree::betree::List<T>}#1::reverse]: loop 0:
    Source: 'src/betree.rs', lines 306:8-310:9 *)
let rec betree_List_reverse_loop
  (#t : Type0) (self : betree_List_t t) (out : betree_List_t t) :
  Tot (result (betree_List_t t))
  (decreases (betree_List_reverse_loop_decreases self out))
  =
  begin match self with
  | Betree_List_Cons hd tl ->
    betree_List_reverse_loop tl (Betree_List_Cons hd out)
  | Betree_List_Nil -> Ok out
  end

(** [betree::betree::{betree::betree::List<T>}#1::reverse]:
    Source: 'src/betree.rs', lines 304:4-312:5 *)
let betree_List_reverse
  (#t : Type0) (self : betree_List_t t) : result (betree_List_t t) =
  betree_List_reverse_loop self Betree_List_Nil

(** [betree::betree::{betree::betree::List<T>}#1::split_at]: loop 0:
    Source: 'src/betree.rs', lines 290:8-300:9 *)
let rec betree_List_split_at_loop
  (#t : Type0) (n : u64) (beg : betree_List_t t) (self : betree_List_t t) :
  Tot (result ((betree_List_t t) & (betree_List_t t)))
  (decreases (betree_List_split_at_loop_decreases n beg self))
  =
  if n > 0
  then
    begin match self with
    | Betree_List_Cons hd tl ->
      let* n1 = u64_sub n 1 in
      betree_List_split_at_loop n1 (Betree_List_Cons hd beg) tl
    | Betree_List_Nil -> Fail Failure
    end
  else let* l = betree_List_reverse beg in Ok (l, self)

(** [betree::betree::{betree::betree::List<T>}#1::split_at]:
    Source: 'src/betree.rs', lines 287:4-302:5 *)
let betree_List_split_at
  (#t : Type0) (self : betree_List_t t) (n : u64) :
  result ((betree_List_t t) & (betree_List_t t))
  =
  betree_List_split_at_loop n Betree_List_Nil self

(** [betree::betree::{betree::betree::List<T>}#1::push_front]:
    Source: 'src/betree.rs', lines 315:4-319:5 *)
let betree_List_push_front
  (#t : Type0) (self : betree_List_t t) (x : t) : result (betree_List_t t) =
  let (tl, _) = core_mem_replace self Betree_List_Nil in
  Ok (Betree_List_Cons x tl)

(** [betree::betree::{betree::betree::List<T>}#1::pop_front]:
    Source: 'src/betree.rs', lines 322:4-332:5 *)
let betree_List_pop_front
  (#t : Type0) (self : betree_List_t t) : result (t & (betree_List_t t)) =
  let (ls, _) = core_mem_replace self Betree_List_Nil in
  begin match ls with
  | Betree_List_Cons x tl -> Ok (x, tl)
  | Betree_List_Nil -> Fail Failure
  end

(** [betree::betree::{betree::betree::List<T>}#1::hd]:
    Source: 'src/betree.rs', lines 334:4-339:5 *)
let betree_List_hd (#t : Type0) (self : betree_List_t t) : result t =
  begin match self with
  | Betree_List_Cons hd _ -> Ok hd
  | Betree_List_Nil -> Fail Failure
  end

(** [betree::betree::{betree::betree::List<(u64, T)>}#2::head_has_key]:
    Source: 'src/betree.rs', lines 343:4-348:5 *)
let betree_ListPairU64T_head_has_key
  (#t : Type0) (self : betree_List_t (u64 & t)) (key : u64) : result bool =
  begin match self with
  | Betree_List_Cons hd _ -> let (i, _) = hd in Ok (i = key)
  | Betree_List_Nil -> Ok false
  end

(** [betree::betree::{betree::betree::List<(u64, T)>}#2::partition_at_pivot]: loop 0:
    Source: 'src/betree.rs', lines 359:8-368:9 *)
let rec betree_ListPairU64T_partition_at_pivot_loop
  (#t : Type0) (pivot : u64) (beg : betree_List_t (u64 & t))
  (end1 : betree_List_t (u64 & t)) (self : betree_List_t (u64 & t)) :
  Tot (result ((betree_List_t (u64 & t)) & (betree_List_t (u64 & t))))
  (decreases (
    betree_ListPairU64T_partition_at_pivot_loop_decreases pivot beg end1 self))
  =
  begin match self with
  | Betree_List_Cons hd tl ->
    let (i, _) = hd in
    if i >= pivot
    then
      betree_ListPairU64T_partition_at_pivot_loop pivot beg (Betree_List_Cons
        hd end1) tl
    else
      betree_ListPairU64T_partition_at_pivot_loop pivot (Betree_List_Cons hd
        beg) end1 tl
  | Betree_List_Nil ->
    let* l = betree_List_reverse beg in
    let* l1 = betree_List_reverse end1 in
    Ok (l, l1)
  end

(** [betree::betree::{betree::betree::List<(u64, T)>}#2::partition_at_pivot]:
    Source: 'src/betree.rs', lines 355:4-370:5 *)
let betree_ListPairU64T_partition_at_pivot
  (#t : Type0) (self : betree_List_t (u64 & t)) (pivot : u64) :
  result ((betree_List_t (u64 & t)) & (betree_List_t (u64 & t)))
  =
  betree_ListPairU64T_partition_at_pivot_loop pivot Betree_List_Nil
    Betree_List_Nil self

(** [betree::betree::{betree::betree::Leaf}#3::split]:
    Source: 'src/betree.rs', lines 378:4-409:5 *)
let betree_Leaf_split
  (self : betree_Leaf_t) (content : betree_List_t (u64 & u64))
  (params : betree_Params_t) (node_id_cnt : betree_NodeIdCounter_t)
  (st : state) :
  result (state & (betree_Internal_t & betree_NodeIdCounter_t))
  =
  let* p = betree_List_split_at content params.split_size in
  let (content0, content1) = p in
  let* p1 = betree_List_hd content1 in
  let (pivot, _) = p1 in
  let* (id0, node_id_cnt1) = betree_NodeIdCounter_fresh_id node_id_cnt in
  let* (id1, node_id_cnt2) = betree_NodeIdCounter_fresh_id node_id_cnt1 in
  let* (st1, _) = betree_store_leaf_node id0 content0 st in
  let* (st2, _) = betree_store_leaf_node id1 content1 st1 in
  let n = Betree_Node_Leaf { id = id0; size = params.split_size } in
  let n1 = Betree_Node_Leaf { id = id1; size = params.split_size } in
  Ok (st2, ({ id = self.id; pivot; left = n; right = n1 }, node_id_cnt2))

(** [betree::betree::{betree::betree::Node}#5::lookup_in_bindings]: loop 0:
    Source: 'src/betree.rs', lines 650:8-660:5 *)
let rec betree_Node_lookup_in_bindings_loop
  (key : u64) (bindings : betree_List_t (u64 & u64)) :
  Tot (result (option u64))
  (decreases (betree_Node_lookup_in_bindings_loop_decreases key bindings))
  =
  begin match bindings with
  | Betree_List_Cons hd tl ->
    let (i, i1) = hd in
    if i = key
    then Ok (Some i1)
    else
      if i > key then Ok None else betree_Node_lookup_in_bindings_loop key tl
  | Betree_List_Nil -> Ok None
  end

(** [betree::betree::{betree::betree::Node}#5::lookup_in_bindings]:
    Source: 'src/betree.rs', lines 649:4-660:5 *)
let betree_Node_lookup_in_bindings
  (key : u64) (bindings : betree_List_t (u64 & u64)) : result (option u64) =
  betree_Node_lookup_in_bindings_loop key bindings

(** [betree::betree::{betree::betree::Node}#5::lookup_first_message_for_key]: loop 0:
    Source: 'src/betree.rs', lines 796:8-810:5 *)
let rec betree_Node_lookup_first_message_for_key_loop
  (key : u64) (msgs : betree_List_t (u64 & betree_Message_t)) :
  Tot (result ((betree_List_t (u64 & betree_Message_t)) & (betree_List_t (u64 &
    betree_Message_t) -> betree_List_t (u64 & betree_Message_t))))
  (decreases (
    betree_Node_lookup_first_message_for_key_loop_decreases key msgs))
  =
  begin match msgs with
  | Betree_List_Cons x next_msgs ->
    let (i, _) = x in
    if i >= key
    then Ok (msgs, (fun ret -> ret))
    else
      let* (l, back) =
        betree_Node_lookup_first_message_for_key_loop key next_msgs in
      let back1 =
        fun ret -> let next_msgs1 = back ret in Betree_List_Cons x next_msgs1
        in
      Ok (l, back1)
  | Betree_List_Nil -> Ok (Betree_List_Nil, (fun ret -> ret))
  end

(** [betree::betree::{betree::betree::Node}#5::lookup_first_message_for_key]:
    Source: 'src/betree.rs', lines 792:4-810:5 *)
let betree_Node_lookup_first_message_for_key
  (key : u64) (msgs : betree_List_t (u64 & betree_Message_t)) :
  result ((betree_List_t (u64 & betree_Message_t)) & (betree_List_t (u64 &
    betree_Message_t) -> betree_List_t (u64 & betree_Message_t)))
  =
  betree_Node_lookup_first_message_for_key_loop key msgs

(** [betree::betree::{betree::betree::Node}#5::apply_upserts]: loop 0:
    Source: 'src/betree.rs', lines 821:8-838:9 *)
let rec betree_Node_apply_upserts_loop
  (msgs : betree_List_t (u64 & betree_Message_t)) (prev : option u64)
  (key : u64) :
  Tot (result (u64 & (betree_List_t (u64 & betree_Message_t))))
  (decreases (betree_Node_apply_upserts_loop_decreases msgs prev key))
  =
  let* b = betree_ListPairU64T_head_has_key msgs key in
  if b
  then
    let* (msg, msgs1) = betree_List_pop_front msgs in
    let (_, m) = msg in
    begin match m with
    | Betree_Message_Insert _ -> Fail Failure
    | Betree_Message_Delete -> Fail Failure
    | Betree_Message_Upsert s ->
      let* v = betree_upsert_update prev s in
      betree_Node_apply_upserts_loop msgs1 (Some v) key
    end
  else
    let* v = core_option_Option_unwrap prev in
    let* msgs1 = betree_List_push_front msgs (key, (Betree_Message_Insert v))
      in
    Ok (v, msgs1)

(** [betree::betree::{betree::betree::Node}#5::apply_upserts]:
    Source: 'src/betree.rs', lines 820:4-844:5 *)
let betree_Node_apply_upserts
  (msgs : betree_List_t (u64 & betree_Message_t)) (prev : option u64)
  (key : u64) :
  result (u64 & (betree_List_t (u64 & betree_Message_t)))
  =
  betree_Node_apply_upserts_loop msgs prev key

(** [betree::betree::{betree::betree::Internal}#4::lookup_in_children]:
    Source: 'src/betree.rs', lines 414:4-420:5 *)
let rec betree_Internal_lookup_in_children
  (self : betree_Internal_t) (key : u64) (st : state) :
  Tot (result (state & ((option u64) & betree_Internal_t)))
  (decreases (betree_Internal_lookup_in_children_decreases self key st))
  =
  if key < self.pivot
  then
    let* (st1, (o, n)) = betree_Node_lookup self.left key st in
    Ok (st1, (o, { self with left = n }))
  else
    let* (st1, (o, n)) = betree_Node_lookup self.right key st in
    Ok (st1, (o, { self with right = n }))

(** [betree::betree::{betree::betree::Node}#5::lookup]:
    Source: 'src/betree.rs', lines 712:4-785:5 *)
and betree_Node_lookup
  (self : betree_Node_t) (key : u64) (st : state) :
  Tot (result (state & ((option u64) & betree_Node_t)))
  (decreases (betree_Node_lookup_decreases self key st))
  =
  begin match self with
  | Betree_Node_Internal node ->
    let* (st1, msgs) = betree_load_internal_node node.id st in
    let* (pending, lookup_first_message_for_key_back) =
      betree_Node_lookup_first_message_for_key key msgs in
    begin match pending with
    | Betree_List_Cons p _ ->
      let (k, msg) = p in
      if k <> key
      then
        let* (st2, (o, node1)) =
          betree_Internal_lookup_in_children node key st1 in
        Ok (st2, (o, (Betree_Node_Internal node1)))
      else
        begin match msg with
        | Betree_Message_Insert v -> Ok (st1, ((Some v), self))
        | Betree_Message_Delete -> Ok (st1, (None, self))
        | Betree_Message_Upsert _ ->
          let* (st2, (v, node1)) =
            betree_Internal_lookup_in_children node key st1 in
          let* (v1, pending1) = betree_Node_apply_upserts pending v key in
          let msgs1 = lookup_first_message_for_key_back pending1 in
          let* (st3, _) = betree_store_internal_node node1.id msgs1 st2 in
          Ok (st3, ((Some v1), (Betree_Node_Internal node1)))
        end
    | Betree_List_Nil ->
      let* (st2, (o, node1)) = betree_Internal_lookup_in_children node key st1
        in
      Ok (st2, (o, (Betree_Node_Internal node1)))
    end
  | Betree_Node_Leaf node ->
    let* (st1, bindings) = betree_load_leaf_node node.id st in
    let* o = betree_Node_lookup_in_bindings key bindings in
    Ok (st1, (o, self))
  end

(** [betree::betree::{betree::betree::Node}#5::filter_messages_for_key]: loop 0:
    Source: 'src/betree.rs', lines 684:8-692:5 *)
let rec betree_Node_filter_messages_for_key_loop
  (key : u64) (msgs : betree_List_t (u64 & betree_Message_t)) :
  Tot (result (betree_List_t (u64 & betree_Message_t)))
  (decreases (betree_Node_filter_messages_for_key_loop_decreases key msgs))
  =
  begin match msgs with
  | Betree_List_Cons p _ ->
    let (k, _) = p in
    if k = key
    then
      let* (_, msgs1) = betree_List_pop_front msgs in
      betree_Node_filter_messages_for_key_loop key msgs1
    else Ok msgs
  | Betree_List_Nil -> Ok Betree_List_Nil
  end

(** [betree::betree::{betree::betree::Node}#5::filter_messages_for_key]:
    Source: 'src/betree.rs', lines 683:4-692:5 *)
let betree_Node_filter_messages_for_key
  (key : u64) (msgs : betree_List_t (u64 & betree_Message_t)) :
  result (betree_List_t (u64 & betree_Message_t))
  =
  betree_Node_filter_messages_for_key_loop key msgs

(** [betree::betree::{betree::betree::Node}#5::lookup_first_message_after_key]: loop 0:
    Source: 'src/betree.rs', lines 698:8-704:9 *)
let rec betree_Node_lookup_first_message_after_key_loop
  (key : u64) (msgs : betree_List_t (u64 & betree_Message_t)) :
  Tot (result ((betree_List_t (u64 & betree_Message_t)) & (betree_List_t (u64 &
    betree_Message_t) -> betree_List_t (u64 & betree_Message_t))))
  (decreases (
    betree_Node_lookup_first_message_after_key_loop_decreases key msgs))
  =
  begin match msgs with
  | Betree_List_Cons p next_msgs ->
    let (k, _) = p in
    if k = key
    then
      let* (l, back) =
        betree_Node_lookup_first_message_after_key_loop key next_msgs in
      let back1 =
        fun ret -> let next_msgs1 = back ret in Betree_List_Cons p next_msgs1
        in
      Ok (l, back1)
    else Ok (msgs, (fun ret -> ret))
  | Betree_List_Nil -> Ok (Betree_List_Nil, (fun ret -> ret))
  end

(** [betree::betree::{betree::betree::Node}#5::lookup_first_message_after_key]:
    Source: 'src/betree.rs', lines 694:4-706:5 *)
let betree_Node_lookup_first_message_after_key
  (key : u64) (msgs : betree_List_t (u64 & betree_Message_t)) :
  result ((betree_List_t (u64 & betree_Message_t)) & (betree_List_t (u64 &
    betree_Message_t) -> betree_List_t (u64 & betree_Message_t)))
  =
  betree_Node_lookup_first_message_after_key_loop key msgs

(** [betree::betree::{betree::betree::Node}#5::apply_to_internal]:
    Source: 'src/betree.rs', lines 534:4-586:5 *)
let betree_Node_apply_to_internal
  (msgs : betree_List_t (u64 & betree_Message_t)) (key : u64)
  (new_msg : betree_Message_t) :
  result (betree_List_t (u64 & betree_Message_t))
  =
  let* (msgs1, lookup_first_message_for_key_back) =
    betree_Node_lookup_first_message_for_key key msgs in
  let* b = betree_ListPairU64T_head_has_key msgs1 key in
  if b
  then
    begin match new_msg with
    | Betree_Message_Insert _ ->
      let* msgs2 = betree_Node_filter_messages_for_key key msgs1 in
      let* msgs3 = betree_List_push_front msgs2 (key, new_msg) in
      Ok (lookup_first_message_for_key_back msgs3)
    | Betree_Message_Delete ->
      let* msgs2 = betree_Node_filter_messages_for_key key msgs1 in
      let* msgs3 = betree_List_push_front msgs2 (key, Betree_Message_Delete) in
      Ok (lookup_first_message_for_key_back msgs3)
    | Betree_Message_Upsert s ->
      let* p = betree_List_hd msgs1 in
      let (_, m) = p in
      begin match m with
      | Betree_Message_Insert prev ->
        let* v = betree_upsert_update (Some prev) s in
        let* (_, msgs2) = betree_List_pop_front msgs1 in
        let* msgs3 =
          betree_List_push_front msgs2 (key, (Betree_Message_Insert v)) in
        Ok (lookup_first_message_for_key_back msgs3)
      | Betree_Message_Delete ->
        let* (_, msgs2) = betree_List_pop_front msgs1 in
        let* v = betree_upsert_update None s in
        let* msgs3 =
          betree_List_push_front msgs2 (key, (Betree_Message_Insert v)) in
        Ok (lookup_first_message_for_key_back msgs3)
      | Betree_Message_Upsert _ ->
        let* (msgs2, lookup_first_message_after_key_back) =
          betree_Node_lookup_first_message_after_key key msgs1 in
        let* msgs3 = betree_List_push_front msgs2 (key, new_msg) in
        let msgs4 = lookup_first_message_after_key_back msgs3 in
        Ok (lookup_first_message_for_key_back msgs4)
      end
    end
  else
    let* msgs2 = betree_List_push_front msgs1 (key, new_msg) in
    Ok (lookup_first_message_for_key_back msgs2)

(** [betree::betree::{betree::betree::Node}#5::apply_messages_to_internal]: loop 0:
    Source: 'src/betree.rs', lines 522:8-525:9 *)
let rec betree_Node_apply_messages_to_internal_loop
  (msgs : betree_List_t (u64 & betree_Message_t))
  (new_msgs : betree_List_t (u64 & betree_Message_t)) :
  Tot (result (betree_List_t (u64 & betree_Message_t)))
  (decreases (
    betree_Node_apply_messages_to_internal_loop_decreases msgs new_msgs))
  =
  begin match new_msgs with
  | Betree_List_Cons new_msg new_msgs_tl ->
    let (i, m) = new_msg in
    let* msgs1 = betree_Node_apply_to_internal msgs i m in
    betree_Node_apply_messages_to_internal_loop msgs1 new_msgs_tl
  | Betree_List_Nil -> Ok msgs
  end

(** [betree::betree::{betree::betree::Node}#5::apply_messages_to_internal]:
    Source: 'src/betree.rs', lines 518:4-526:5 *)
let betree_Node_apply_messages_to_internal
  (msgs : betree_List_t (u64 & betree_Message_t))
  (new_msgs : betree_List_t (u64 & betree_Message_t)) :
  result (betree_List_t (u64 & betree_Message_t))
  =
  betree_Node_apply_messages_to_internal_loop msgs new_msgs

(** [betree::betree::{betree::betree::Node}#5::lookup_mut_in_bindings]: loop 0:
    Source: 'src/betree.rs', lines 668:8-675:9 *)
let rec betree_Node_lookup_mut_in_bindings_loop
  (key : u64) (bindings : betree_List_t (u64 & u64)) :
  Tot (result ((betree_List_t (u64 & u64)) & (betree_List_t (u64 & u64) ->
    betree_List_t (u64 & u64))))
  (decreases (betree_Node_lookup_mut_in_bindings_loop_decreases key bindings))
  =
  begin match bindings with
  | Betree_List_Cons hd tl ->
    let (i, _) = hd in
    if i >= key
    then Ok (bindings, (fun ret -> ret))
    else
      let* (l, back) = betree_Node_lookup_mut_in_bindings_loop key tl in
      let back1 = fun ret -> let tl1 = back ret in Betree_List_Cons hd tl1 in
      Ok (l, back1)
  | Betree_List_Nil -> Ok (Betree_List_Nil, (fun ret -> ret))
  end

(** [betree::betree::{betree::betree::Node}#5::lookup_mut_in_bindings]:
    Source: 'src/betree.rs', lines 664:4-677:5 *)
let betree_Node_lookup_mut_in_bindings
  (key : u64) (bindings : betree_List_t (u64 & u64)) :
  result ((betree_List_t (u64 & u64)) & (betree_List_t (u64 & u64) ->
    betree_List_t (u64 & u64)))
  =
  betree_Node_lookup_mut_in_bindings_loop key bindings

(** [betree::betree::{betree::betree::Node}#5::apply_to_leaf]:
    Source: 'src/betree.rs', lines 476:4-515:5 *)
let betree_Node_apply_to_leaf
  (bindings : betree_List_t (u64 & u64)) (key : u64)
  (new_msg : betree_Message_t) :
  result (betree_List_t (u64 & u64))
  =
  let* (bindings1, lookup_mut_in_bindings_back) =
    betree_Node_lookup_mut_in_bindings key bindings in
  let* b = betree_ListPairU64T_head_has_key bindings1 key in
  if b
  then
    let* (hd, bindings2) = betree_List_pop_front bindings1 in
    begin match new_msg with
    | Betree_Message_Insert v ->
      let* bindings3 = betree_List_push_front bindings2 (key, v) in
      Ok (lookup_mut_in_bindings_back bindings3)
    | Betree_Message_Delete -> Ok (lookup_mut_in_bindings_back bindings2)
    | Betree_Message_Upsert s ->
      let (_, i) = hd in
      let* v = betree_upsert_update (Some i) s in
      let* bindings3 = betree_List_push_front bindings2 (key, v) in
      Ok (lookup_mut_in_bindings_back bindings3)
    end
  else
    begin match new_msg with
    | Betree_Message_Insert v ->
      let* bindings2 = betree_List_push_front bindings1 (key, v) in
      Ok (lookup_mut_in_bindings_back bindings2)
    | Betree_Message_Delete -> Ok (lookup_mut_in_bindings_back bindings1)
    | Betree_Message_Upsert s ->
      let* v = betree_upsert_update None s in
      let* bindings2 = betree_List_push_front bindings1 (key, v) in
      Ok (lookup_mut_in_bindings_back bindings2)
    end

(** [betree::betree::{betree::betree::Node}#5::apply_messages_to_leaf]: loop 0:
    Source: 'src/betree.rs', lines 467:8-470:9 *)
let rec betree_Node_apply_messages_to_leaf_loop
  (bindings : betree_List_t (u64 & u64))
  (new_msgs : betree_List_t (u64 & betree_Message_t)) :
  Tot (result (betree_List_t (u64 & u64)))
  (decreases (
    betree_Node_apply_messages_to_leaf_loop_decreases bindings new_msgs))
  =
  begin match new_msgs with
  | Betree_List_Cons new_msg new_msgs_tl ->
    let (i, m) = new_msg in
    let* bindings1 = betree_Node_apply_to_leaf bindings i m in
    betree_Node_apply_messages_to_leaf_loop bindings1 new_msgs_tl
  | Betree_List_Nil -> Ok bindings
  end

(** [betree::betree::{betree::betree::Node}#5::apply_messages_to_leaf]:
    Source: 'src/betree.rs', lines 463:4-471:5 *)
let betree_Node_apply_messages_to_leaf
  (bindings : betree_List_t (u64 & u64))
  (new_msgs : betree_List_t (u64 & betree_Message_t)) :
  result (betree_List_t (u64 & u64))
  =
  betree_Node_apply_messages_to_leaf_loop bindings new_msgs

(** [betree::betree::{betree::betree::Internal}#4::flush]:
    Source: 'src/betree.rs', lines 429:4-458:5 *)
let rec betree_Internal_flush
  (self : betree_Internal_t) (params : betree_Params_t)
  (node_id_cnt : betree_NodeIdCounter_t)
  (content : betree_List_t (u64 & betree_Message_t)) (st : state) :
  Tot (result (state & ((betree_List_t (u64 & betree_Message_t)) &
    (betree_Internal_t & betree_NodeIdCounter_t))))
  (decreases (
    betree_Internal_flush_decreases self params node_id_cnt content st))
  =
  let* p = betree_ListPairU64T_partition_at_pivot content self.pivot in
  let (msgs_left, msgs_right) = p in
  let* len_left = betree_List_len msgs_left in
  if len_left >= params.min_flush_size
  then
    let* (st1, p1) =
      betree_Node_apply_messages self.left params node_id_cnt msgs_left st in
    let (n, node_id_cnt1) = p1 in
    let* len_right = betree_List_len msgs_right in
    if len_right >= params.min_flush_size
    then
      let* (st2, p2) =
        betree_Node_apply_messages self.right params node_id_cnt1 msgs_right
          st1 in
      let (n1, node_id_cnt2) = p2 in
      Ok (st2, (Betree_List_Nil, ({ self with left = n; right = n1 },
        node_id_cnt2)))
    else Ok (st1, (msgs_right, ({ self with left = n }, node_id_cnt1)))
  else
    let* (st1, p1) =
      betree_Node_apply_messages self.right params node_id_cnt msgs_right st in
    let (n, node_id_cnt1) = p1 in
    Ok (st1, (msgs_left, ({ self with right = n }, node_id_cnt1)))

(** [betree::betree::{betree::betree::Node}#5::apply_messages]:
    Source: 'src/betree.rs', lines 601:4-645:5 *)
and betree_Node_apply_messages
  (self : betree_Node_t) (params : betree_Params_t)
  (node_id_cnt : betree_NodeIdCounter_t)
  (msgs : betree_List_t (u64 & betree_Message_t)) (st : state) :
  Tot (result (state & (betree_Node_t & betree_NodeIdCounter_t)))
  (decreases (
    betree_Node_apply_messages_decreases self params node_id_cnt msgs st))
  =
  begin match self with
  | Betree_Node_Internal node ->
    let* (st1, content) = betree_load_internal_node node.id st in
    let* content1 = betree_Node_apply_messages_to_internal content msgs in
    let* num_msgs = betree_List_len content1 in
    if num_msgs >= params.min_flush_size
    then
      let* (st2, (content2, p)) =
        betree_Internal_flush node params node_id_cnt content1 st1 in
      let (node1, node_id_cnt1) = p in
      let* (st3, _) = betree_store_internal_node node1.id content2 st2 in
      Ok (st3, ((Betree_Node_Internal node1), node_id_cnt1))
    else
      let* (st2, _) = betree_store_internal_node node.id content1 st1 in
      Ok (st2, (self, node_id_cnt))
  | Betree_Node_Leaf node ->
    let* (st1, content) = betree_load_leaf_node node.id st in
    let* content1 = betree_Node_apply_messages_to_leaf content msgs in
    let* len = betree_List_len content1 in
    let* i = u64_mul 2 params.split_size in
    if len >= i
    then
      let* (st2, (new_node, node_id_cnt1)) =
        betree_Leaf_split node content1 params node_id_cnt st1 in
      let* (st3, _) = betree_store_leaf_node node.id Betree_List_Nil st2 in
      Ok (st3, ((Betree_Node_Internal new_node), node_id_cnt1))
    else
      let* (st2, _) = betree_store_leaf_node node.id content1 st1 in
      Ok (st2, ((Betree_Node_Leaf { node with size = len }), node_id_cnt))
  end

(** [betree::betree::{betree::betree::Node}#5::apply]:
    Source: 'src/betree.rs', lines 589:4-598:5 *)
let betree_Node_apply
  (self : betree_Node_t) (params : betree_Params_t)
  (node_id_cnt : betree_NodeIdCounter_t) (key : u64)
  (new_msg : betree_Message_t) (st : state) :
  result (state & (betree_Node_t & betree_NodeIdCounter_t))
  =
  betree_Node_apply_messages self params node_id_cnt (Betree_List_Cons (key,
    new_msg) Betree_List_Nil) st

(** [betree::betree::{betree::betree::BeTree}#6::new]:
    Source: 'src/betree.rs', lines 848:4-862:5 *)
let betree_BeTree_new
  (min_flush_size : u64) (split_size : u64) (st : state) :
  result (state & betree_BeTree_t)
  =
  let* node_id_cnt = betree_NodeIdCounter_new in
  let* (id, node_id_cnt1) = betree_NodeIdCounter_fresh_id node_id_cnt in
  let* (st1, _) = betree_store_leaf_node id Betree_List_Nil st in
  Ok (st1,
    {
      params = { min_flush_size; split_size };
      node_id_cnt = node_id_cnt1;
      root = (Betree_Node_Leaf { id; size = 0 })
    })

(** [betree::betree::{betree::betree::BeTree}#6::apply]:
    Source: 'src/betree.rs', lines 867:4-870:5 *)
let betree_BeTree_apply
  (self : betree_BeTree_t) (key : u64) (msg : betree_Message_t) (st : state) :
  result (state & betree_BeTree_t)
  =
  let* (st1, p) =
    betree_Node_apply self.root self.params self.node_id_cnt key msg st in
  let (n, nic) = p in
  Ok (st1, { self with node_id_cnt = nic; root = n })

(** [betree::betree::{betree::betree::BeTree}#6::insert]:
    Source: 'src/betree.rs', lines 873:4-876:5 *)
let betree_BeTree_insert
  (self : betree_BeTree_t) (key : u64) (value : u64) (st : state) :
  result (state & betree_BeTree_t)
  =
  betree_BeTree_apply self key (Betree_Message_Insert value) st

(** [betree::betree::{betree::betree::BeTree}#6::delete]:
    Source: 'src/betree.rs', lines 879:4-882:5 *)
let betree_BeTree_delete
  (self : betree_BeTree_t) (key : u64) (st : state) :
  result (state & betree_BeTree_t)
  =
  betree_BeTree_apply self key Betree_Message_Delete st

(** [betree::betree::{betree::betree::BeTree}#6::upsert]:
    Source: 'src/betree.rs', lines 885:4-888:5 *)
let betree_BeTree_upsert
  (self : betree_BeTree_t) (key : u64) (upd : betree_UpsertFunState_t)
  (st : state) :
  result (state & betree_BeTree_t)
  =
  betree_BeTree_apply self key (Betree_Message_Upsert upd) st

(** [betree::betree::{betree::betree::BeTree}#6::lookup]:
    Source: 'src/betree.rs', lines 894:4-896:5 *)
let betree_BeTree_lookup
  (self : betree_BeTree_t) (key : u64) (st : state) :
  result (state & ((option u64) & betree_BeTree_t))
  =
  let* (st1, (o, n)) = betree_Node_lookup self.root key st in
  Ok (st1, (o, { self with root = n }))

(** [betree::main]:
    Source: 'src/main.rs', lines 4:0-4:12 *)
let main : result unit =
  Ok ()

(** Unit test for [betree::main] *)
let _ = assert_norm (main = Ok ())

