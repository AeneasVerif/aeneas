(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [betree_main]: function definitions *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import BetreeMain_Types.
Include BetreeMain_Types.
Require Import BetreeMain_FunsExternal.
Include BetreeMain_FunsExternal.
Module BetreeMain_Funs.

(** [betree_main::betree::load_internal_node]:
    Source: 'src/betree.rs', lines 36:0-36:52 *)
Definition betree_load_internal_node
  (id : u64) (st : state) :
  result (state * (betree_List_t (u64 * betree_Message_t)))
  :=
  betree_utils_load_internal_node id st
.

(** [betree_main::betree::store_internal_node]:
    Source: 'src/betree.rs', lines 41:0-41:60 *)
Definition betree_store_internal_node
  (id : u64) (content : betree_List_t (u64 * betree_Message_t)) (st : state) :
  result (state * unit)
  :=
  betree_utils_store_internal_node id content st
.

(** [betree_main::betree::load_leaf_node]:
    Source: 'src/betree.rs', lines 46:0-46:44 *)
Definition betree_load_leaf_node
  (id : u64) (st : state) : result (state * (betree_List_t (u64 * u64))) :=
  betree_utils_load_leaf_node id st
.

(** [betree_main::betree::store_leaf_node]:
    Source: 'src/betree.rs', lines 51:0-51:52 *)
Definition betree_store_leaf_node
  (id : u64) (content : betree_List_t (u64 * u64)) (st : state) :
  result (state * unit)
  :=
  betree_utils_store_leaf_node id content st
.

(** [betree_main::betree::fresh_node_id]:
    Source: 'src/betree.rs', lines 55:0-55:48 *)
Definition betree_fresh_node_id (counter : u64) : result (u64 * u64) :=
  counter1 <- u64_add counter 1%u64; Ok (counter, counter1)
.

(** [betree_main::betree::{betree_main::betree::NodeIdCounter}::new]:
    Source: 'src/betree.rs', lines 206:4-206:20 *)
Definition betree_NodeIdCounter_new : result betree_NodeIdCounter_t :=
  Ok {| betree_NodeIdCounter_next_node_id := 0%u64 |}
.

(** [betree_main::betree::{betree_main::betree::NodeIdCounter}::fresh_id]:
    Source: 'src/betree.rs', lines 210:4-210:36 *)
Definition betree_NodeIdCounter_fresh_id
  (self : betree_NodeIdCounter_t) : result (u64 * betree_NodeIdCounter_t) :=
  i <- u64_add self.(betree_NodeIdCounter_next_node_id) 1%u64;
  Ok (self.(betree_NodeIdCounter_next_node_id),
    {| betree_NodeIdCounter_next_node_id := i |})
.

(** [betree_main::betree::upsert_update]:
    Source: 'src/betree.rs', lines 234:0-234:70 *)
Definition betree_upsert_update
  (prev : option u64) (st : betree_UpsertFunState_t) : result u64 :=
  match prev with
  | None =>
    match st with
    | Betree_UpsertFunState_Add v => Ok v
    | Betree_UpsertFunState_Sub _ => Ok 0%u64
    end
  | Some prev1 =>
    match st with
    | Betree_UpsertFunState_Add v =>
      margin <- u64_sub core_u64_max prev1;
      if margin s>= v then u64_add prev1 v else Ok core_u64_max
    | Betree_UpsertFunState_Sub v =>
      if prev1 s>= v then u64_sub prev1 v else Ok 0%u64
    end
  end
.

(** [betree_main::betree::{betree_main::betree::List<T>#1}::len]:
    Source: 'src/betree.rs', lines 276:4-276:24 *)
Fixpoint betree_List_len
  (T : Type) (n : nat) (self : betree_List_t T) : result u64 :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match self with
    | Betree_List_Cons _ tl => i <- betree_List_len T n1 tl; u64_add 1%u64 i
    | Betree_List_Nil => Ok 0%u64
    end
  end
.

(** [betree_main::betree::{betree_main::betree::List<T>#1}::split_at]:
    Source: 'src/betree.rs', lines 284:4-284:51 *)
Fixpoint betree_List_split_at
  (T : Type) (n : nat) (self : betree_List_t T) (n1 : u64) :
  result ((betree_List_t T) * (betree_List_t T))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n2 =>
    if n1 s= 0%u64
    then Ok (Betree_List_Nil, self)
    else
      match self with
      | Betree_List_Cons hd tl =>
        i <- u64_sub n1 1%u64;
        p <- betree_List_split_at T n2 tl i;
        let (ls0, ls1) := p in
        Ok (Betree_List_Cons hd ls0, ls1)
      | Betree_List_Nil => Fail_ Failure
      end
  end
.

(** [betree_main::betree::{betree_main::betree::List<T>#1}::push_front]:
    Source: 'src/betree.rs', lines 299:4-299:34 *)
Definition betree_List_push_front
  (T : Type) (self : betree_List_t T) (x : T) : result (betree_List_t T) :=
  let (tl, _) := core_mem_replace (betree_List_t T) self Betree_List_Nil in
  Ok (Betree_List_Cons x tl)
.

(** [betree_main::betree::{betree_main::betree::List<T>#1}::pop_front]:
    Source: 'src/betree.rs', lines 306:4-306:32 *)
Definition betree_List_pop_front
  (T : Type) (self : betree_List_t T) : result (T * (betree_List_t T)) :=
  let (ls, _) := core_mem_replace (betree_List_t T) self Betree_List_Nil in
  match ls with
  | Betree_List_Cons x tl => Ok (x, tl)
  | Betree_List_Nil => Fail_ Failure
  end
.

(** [betree_main::betree::{betree_main::betree::List<T>#1}::hd]:
    Source: 'src/betree.rs', lines 318:4-318:22 *)
Definition betree_List_hd (T : Type) (self : betree_List_t T) : result T :=
  match self with
  | Betree_List_Cons hd _ => Ok hd
  | Betree_List_Nil => Fail_ Failure
  end
.

(** [betree_main::betree::{betree_main::betree::List<(u64, T)>#2}::head_has_key]:
    Source: 'src/betree.rs', lines 327:4-327:44 *)
Definition betree_ListPairU64T_head_has_key
  (T : Type) (self : betree_List_t (u64 * T)) (key : u64) : result bool :=
  match self with
  | Betree_List_Cons hd _ => let (i, _) := hd in Ok (i s= key)
  | Betree_List_Nil => Ok false
  end
.

(** [betree_main::betree::{betree_main::betree::List<(u64, T)>#2}::partition_at_pivot]:
    Source: 'src/betree.rs', lines 339:4-339:73 *)
Fixpoint betree_ListPairU64T_partition_at_pivot
  (T : Type) (n : nat) (self : betree_List_t (u64 * T)) (pivot : u64) :
  result ((betree_List_t (u64 * T)) * (betree_List_t (u64 * T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match self with
    | Betree_List_Cons hd tl =>
      let (i, t) := hd in
      if i s>= pivot
      then Ok (Betree_List_Nil, Betree_List_Cons (i, t) tl)
      else (
        p <- betree_ListPairU64T_partition_at_pivot T n1 tl pivot;
        let (ls0, ls1) := p in
        Ok (Betree_List_Cons (i, t) ls0, ls1))
    | Betree_List_Nil => Ok (Betree_List_Nil, Betree_List_Nil)
    end
  end
.

(** [betree_main::betree::{betree_main::betree::Leaf#3}::split]:
    Source: 'src/betree.rs', lines 359:4-364:17 *)
Definition betree_Leaf_split
  (n : nat) (self : betree_Leaf_t) (content : betree_List_t (u64 * u64))
  (params : betree_Params_t) (node_id_cnt : betree_NodeIdCounter_t)
  (st : state) :
  result (state * (betree_Internal_t * betree_NodeIdCounter_t))
  :=
  p <-
    betree_List_split_at (u64 * u64) n content
      params.(betree_Params_split_size);
  let (content0, content1) := p in
  p1 <- betree_List_hd (u64 * u64) content1;
  let (pivot, _) := p1 in
  p2 <- betree_NodeIdCounter_fresh_id node_id_cnt;
  let (id0, node_id_cnt1) := p2 in
  p3 <- betree_NodeIdCounter_fresh_id node_id_cnt1;
  let (id1, node_id_cnt2) := p3 in
  p4 <- betree_store_leaf_node id0 content0 st;
  let (st1, _) := p4 in
  p5 <- betree_store_leaf_node id1 content1 st1;
  let (st2, _) := p5 in
  let n1 := Betree_Node_Leaf
    {|
      betree_Leaf_id := id0;
      betree_Leaf_size := params.(betree_Params_split_size)
    |} in
  let n2 := Betree_Node_Leaf
    {|
      betree_Leaf_id := id1;
      betree_Leaf_size := params.(betree_Params_split_size)
    |} in
  Ok (st2, (mkbetree_Internal_t self.(betree_Leaf_id) pivot n1 n2,
    node_id_cnt2))
.

(** [betree_main::betree::{betree_main::betree::Node#5}::lookup_first_message_for_key]:
    Source: 'src/betree.rs', lines 789:4-792:34 *)
Fixpoint betree_Node_lookup_first_message_for_key
  (n : nat) (key : u64) (msgs : betree_List_t (u64 * betree_Message_t)) :
  result ((betree_List_t (u64 * betree_Message_t)) * (betree_List_t (u64 *
    betree_Message_t) -> result (betree_List_t (u64 * betree_Message_t))))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match msgs with
    | Betree_List_Cons x next_msgs =>
      let (i, m) := x in
      if i s>= key
      then Ok (Betree_List_Cons (i, m) next_msgs, Ok)
      else (
        p <- betree_Node_lookup_first_message_for_key n1 key next_msgs;
        let (l, lookup_first_message_for_key_back) := p in
        let back :=
          fun (ret : betree_List_t (u64 * betree_Message_t)) =>
            next_msgs1 <- lookup_first_message_for_key_back ret;
            Ok (Betree_List_Cons (i, m) next_msgs1) in
        Ok (l, back))
    | Betree_List_Nil => Ok (Betree_List_Nil, Ok)
    end
  end
.

(** [betree_main::betree::{betree_main::betree::Node#5}::lookup_in_bindings]:
    Source: 'src/betree.rs', lines 636:4-636:80 *)
Fixpoint betree_Node_lookup_in_bindings
  (n : nat) (key : u64) (bindings : betree_List_t (u64 * u64)) :
  result (option u64)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match bindings with
    | Betree_List_Cons hd tl =>
      let (i, i1) := hd in
      if i s= key
      then Ok (Some i1)
      else
        if i s> key then Ok None else betree_Node_lookup_in_bindings n1 key tl
    | Betree_List_Nil => Ok None
    end
  end
.

(** [betree_main::betree::{betree_main::betree::Node#5}::apply_upserts]:
    Source: 'src/betree.rs', lines 819:4-819:90 *)
Fixpoint betree_Node_apply_upserts
  (n : nat) (msgs : betree_List_t (u64 * betree_Message_t)) (prev : option u64)
  (key : u64) (st : state) :
  result (state * (u64 * (betree_List_t (u64 * betree_Message_t))))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    b <- betree_ListPairU64T_head_has_key betree_Message_t msgs key;
    if b
    then (
      p <- betree_List_pop_front (u64 * betree_Message_t) msgs;
      let (msg, msgs1) := p in
      let (_, m) := msg in
      match m with
      | Betree_Message_Insert _ => Fail_ Failure
      | Betree_Message_Delete => Fail_ Failure
      | Betree_Message_Upsert s =>
        v <- betree_upsert_update prev s;
        betree_Node_apply_upserts n1 msgs1 (Some v) key st
      end)
    else (
      p <- core_option_Option_unwrap u64 prev st;
      let (st1, v) := p in
      msgs1 <-
        betree_List_push_front (u64 * betree_Message_t) msgs (key,
          Betree_Message_Insert v);
      Ok (st1, (v, msgs1)))
  end
.

(** [betree_main::betree::{betree_main::betree::Internal#4}::lookup_in_children]:
    Source: 'src/betree.rs', lines 395:4-395:63 *)
Fixpoint betree_Internal_lookup_in_children
  (n : nat) (self : betree_Internal_t) (key : u64) (st : state) :
  result (state * ((option u64) * betree_Internal_t))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if key s< self.(betree_Internal_pivot)
    then (
      p <- betree_Node_lookup n1 self.(betree_Internal_left) key st;
      let (st1, p1) := p in
      let (o, n2) := p1 in
      Ok (st1, (o, mkbetree_Internal_t self.(betree_Internal_id)
        self.(betree_Internal_pivot) n2 self.(betree_Internal_right))))
    else (
      p <- betree_Node_lookup n1 self.(betree_Internal_right) key st;
      let (st1, p1) := p in
      let (o, n2) := p1 in
      Ok (st1, (o, mkbetree_Internal_t self.(betree_Internal_id)
        self.(betree_Internal_pivot) self.(betree_Internal_left) n2)))
  end

(** [betree_main::betree::{betree_main::betree::Node#5}::lookup]:
    Source: 'src/betree.rs', lines 709:4-709:58 *)
with betree_Node_lookup
  (n : nat) (self : betree_Node_t) (key : u64) (st : state) :
  result (state * ((option u64) * betree_Node_t))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match self with
    | Betree_Node_Internal node =>
      p <- betree_load_internal_node node.(betree_Internal_id) st;
      let (st1, msgs) := p in
      p1 <- betree_Node_lookup_first_message_for_key n1 key msgs;
      let (pending, lookup_first_message_for_key_back) := p1 in
      match pending with
      | Betree_List_Cons p2 l =>
        let (k, msg) := p2 in
        if k s<> key
        then (
          p3 <- betree_Internal_lookup_in_children n1 node key st1;
          let (st2, p4) := p3 in
          let (o, node1) := p4 in
          _ <- lookup_first_message_for_key_back (Betree_List_Cons (k, msg) l);
          Ok (st2, (o, Betree_Node_Internal node1)))
        else
          match msg with
          | Betree_Message_Insert v =>
            _ <-
              lookup_first_message_for_key_back (Betree_List_Cons (k,
                Betree_Message_Insert v) l);
            Ok (st1, (Some v, Betree_Node_Internal node))
          | Betree_Message_Delete =>
            _ <-
              lookup_first_message_for_key_back (Betree_List_Cons (k,
                Betree_Message_Delete) l);
            Ok (st1, (None, Betree_Node_Internal node))
          | Betree_Message_Upsert ufs =>
            p3 <- betree_Internal_lookup_in_children n1 node key st1;
            let (st2, p4) := p3 in
            let (v, node1) := p4 in
            p5 <-
              betree_Node_apply_upserts n1 (Betree_List_Cons (k,
                Betree_Message_Upsert ufs) l) v key st2;
            let (st3, p6) := p5 in
            let (v1, pending1) := p6 in
            msgs1 <- lookup_first_message_for_key_back pending1;
            p7 <-
              betree_store_internal_node node1.(betree_Internal_id) msgs1 st3;
            let (st4, _) := p7 in
            Ok (st4, (Some v1, Betree_Node_Internal node1))
          end
      | Betree_List_Nil =>
        p2 <- betree_Internal_lookup_in_children n1 node key st1;
        let (st2, p3) := p2 in
        let (o, node1) := p3 in
        _ <- lookup_first_message_for_key_back Betree_List_Nil;
        Ok (st2, (o, Betree_Node_Internal node1))
      end
    | Betree_Node_Leaf node =>
      p <- betree_load_leaf_node node.(betree_Leaf_id) st;
      let (st1, bindings) := p in
      o <- betree_Node_lookup_in_bindings n1 key bindings;
      Ok (st1, (o, Betree_Node_Leaf node))
    end
  end
.

(** [betree_main::betree::{betree_main::betree::Node#5}::filter_messages_for_key]:
    Source: 'src/betree.rs', lines 674:4-674:77 *)
Fixpoint betree_Node_filter_messages_for_key
  (n : nat) (key : u64) (msgs : betree_List_t (u64 * betree_Message_t)) :
  result (betree_List_t (u64 * betree_Message_t))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match msgs with
    | Betree_List_Cons p l =>
      let (k, m) := p in
      if k s= key
      then (
        p1 <-
          betree_List_pop_front (u64 * betree_Message_t) (Betree_List_Cons (k,
            m) l);
        let (_, msgs1) := p1 in
        betree_Node_filter_messages_for_key n1 key msgs1)
      else Ok (Betree_List_Cons (k, m) l)
    | Betree_List_Nil => Ok Betree_List_Nil
    end
  end
.

(** [betree_main::betree::{betree_main::betree::Node#5}::lookup_first_message_after_key]:
    Source: 'src/betree.rs', lines 689:4-692:34 *)
Fixpoint betree_Node_lookup_first_message_after_key
  (n : nat) (key : u64) (msgs : betree_List_t (u64 * betree_Message_t)) :
  result ((betree_List_t (u64 * betree_Message_t)) * (betree_List_t (u64 *
    betree_Message_t) -> result (betree_List_t (u64 * betree_Message_t))))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match msgs with
    | Betree_List_Cons p next_msgs =>
      let (k, m) := p in
      if k s= key
      then (
        p1 <- betree_Node_lookup_first_message_after_key n1 key next_msgs;
        let (l, lookup_first_message_after_key_back) := p1 in
        let back :=
          fun (ret : betree_List_t (u64 * betree_Message_t)) =>
            next_msgs1 <- lookup_first_message_after_key_back ret;
            Ok (Betree_List_Cons (k, m) next_msgs1) in
        Ok (l, back))
      else Ok (Betree_List_Cons (k, m) next_msgs, Ok)
    | Betree_List_Nil => Ok (Betree_List_Nil, Ok)
    end
  end
.

(** [betree_main::betree::{betree_main::betree::Node#5}::apply_to_internal]:
    Source: 'src/betree.rs', lines 521:4-521:89 *)
Definition betree_Node_apply_to_internal
  (n : nat) (msgs : betree_List_t (u64 * betree_Message_t)) (key : u64)
  (new_msg : betree_Message_t) :
  result (betree_List_t (u64 * betree_Message_t))
  :=
  p <- betree_Node_lookup_first_message_for_key n key msgs;
  let (msgs1, lookup_first_message_for_key_back) := p in
  b <- betree_ListPairU64T_head_has_key betree_Message_t msgs1 key;
  if b
  then
    match new_msg with
    | Betree_Message_Insert i =>
      msgs2 <- betree_Node_filter_messages_for_key n key msgs1;
      msgs3 <-
        betree_List_push_front (u64 * betree_Message_t) msgs2 (key,
          Betree_Message_Insert i);
      lookup_first_message_for_key_back msgs3
    | Betree_Message_Delete =>
      msgs2 <- betree_Node_filter_messages_for_key n key msgs1;
      msgs3 <-
        betree_List_push_front (u64 * betree_Message_t) msgs2 (key,
          Betree_Message_Delete);
      lookup_first_message_for_key_back msgs3
    | Betree_Message_Upsert s =>
      p1 <- betree_List_hd (u64 * betree_Message_t) msgs1;
      let (_, m) := p1 in
      match m with
      | Betree_Message_Insert prev =>
        v <- betree_upsert_update (Some prev) s;
        p2 <- betree_List_pop_front (u64 * betree_Message_t) msgs1;
        let (_, msgs2) := p2 in
        msgs3 <-
          betree_List_push_front (u64 * betree_Message_t) msgs2 (key,
            Betree_Message_Insert v);
        lookup_first_message_for_key_back msgs3
      | Betree_Message_Delete =>
        p2 <- betree_List_pop_front (u64 * betree_Message_t) msgs1;
        let (_, msgs2) := p2 in
        v <- betree_upsert_update None s;
        msgs3 <-
          betree_List_push_front (u64 * betree_Message_t) msgs2 (key,
            Betree_Message_Insert v);
        lookup_first_message_for_key_back msgs3
      | Betree_Message_Upsert _ =>
        p2 <- betree_Node_lookup_first_message_after_key n key msgs1;
        let (msgs2, lookup_first_message_after_key_back) := p2 in
        msgs3 <-
          betree_List_push_front (u64 * betree_Message_t) msgs2 (key,
            Betree_Message_Upsert s);
        msgs4 <- lookup_first_message_after_key_back msgs3;
        lookup_first_message_for_key_back msgs4
      end
    end
  else (
    msgs2 <-
      betree_List_push_front (u64 * betree_Message_t) msgs1 (key, new_msg);
    lookup_first_message_for_key_back msgs2)
.

(** [betree_main::betree::{betree_main::betree::Node#5}::apply_messages_to_internal]:
    Source: 'src/betree.rs', lines 502:4-505:5 *)
Fixpoint betree_Node_apply_messages_to_internal
  (n : nat) (msgs : betree_List_t (u64 * betree_Message_t))
  (new_msgs : betree_List_t (u64 * betree_Message_t)) :
  result (betree_List_t (u64 * betree_Message_t))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match new_msgs with
    | Betree_List_Cons new_msg new_msgs_tl =>
      let (i, m) := new_msg in
      msgs1 <- betree_Node_apply_to_internal n1 msgs i m;
      betree_Node_apply_messages_to_internal n1 msgs1 new_msgs_tl
    | Betree_List_Nil => Ok msgs
    end
  end
.

(** [betree_main::betree::{betree_main::betree::Node#5}::lookup_mut_in_bindings]:
    Source: 'src/betree.rs', lines 653:4-656:32 *)
Fixpoint betree_Node_lookup_mut_in_bindings
  (n : nat) (key : u64) (bindings : betree_List_t (u64 * u64)) :
  result ((betree_List_t (u64 * u64)) * (betree_List_t (u64 * u64) -> result
    (betree_List_t (u64 * u64))))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match bindings with
    | Betree_List_Cons hd tl =>
      let (i, i1) := hd in
      if i s>= key
      then Ok (Betree_List_Cons (i, i1) tl, Ok)
      else (
        p <- betree_Node_lookup_mut_in_bindings n1 key tl;
        let (l, lookup_mut_in_bindings_back) := p in
        let back :=
          fun (ret : betree_List_t (u64 * u64)) =>
            tl1 <- lookup_mut_in_bindings_back ret;
            Ok (Betree_List_Cons (i, i1) tl1) in
        Ok (l, back))
    | Betree_List_Nil => Ok (Betree_List_Nil, Ok)
    end
  end
.

(** [betree_main::betree::{betree_main::betree::Node#5}::apply_to_leaf]:
    Source: 'src/betree.rs', lines 460:4-460:87 *)
Definition betree_Node_apply_to_leaf
  (n : nat) (bindings : betree_List_t (u64 * u64)) (key : u64)
  (new_msg : betree_Message_t) :
  result (betree_List_t (u64 * u64))
  :=
  p <- betree_Node_lookup_mut_in_bindings n key bindings;
  let (bindings1, lookup_mut_in_bindings_back) := p in
  b <- betree_ListPairU64T_head_has_key u64 bindings1 key;
  if b
  then (
    p1 <- betree_List_pop_front (u64 * u64) bindings1;
    let (hd, bindings2) := p1 in
    match new_msg with
    | Betree_Message_Insert v =>
      bindings3 <- betree_List_push_front (u64 * u64) bindings2 (key, v);
      lookup_mut_in_bindings_back bindings3
    | Betree_Message_Delete => lookup_mut_in_bindings_back bindings2
    | Betree_Message_Upsert s =>
      let (_, i) := hd in
      v <- betree_upsert_update (Some i) s;
      bindings3 <- betree_List_push_front (u64 * u64) bindings2 (key, v);
      lookup_mut_in_bindings_back bindings3
    end)
  else
    match new_msg with
    | Betree_Message_Insert v =>
      bindings2 <- betree_List_push_front (u64 * u64) bindings1 (key, v);
      lookup_mut_in_bindings_back bindings2
    | Betree_Message_Delete => lookup_mut_in_bindings_back bindings1
    | Betree_Message_Upsert s =>
      v <- betree_upsert_update None s;
      bindings2 <- betree_List_push_front (u64 * u64) bindings1 (key, v);
      lookup_mut_in_bindings_back bindings2
    end
.

(** [betree_main::betree::{betree_main::betree::Node#5}::apply_messages_to_leaf]:
    Source: 'src/betree.rs', lines 444:4-447:5 *)
Fixpoint betree_Node_apply_messages_to_leaf
  (n : nat) (bindings : betree_List_t (u64 * u64))
  (new_msgs : betree_List_t (u64 * betree_Message_t)) :
  result (betree_List_t (u64 * u64))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match new_msgs with
    | Betree_List_Cons new_msg new_msgs_tl =>
      let (i, m) := new_msg in
      bindings1 <- betree_Node_apply_to_leaf n1 bindings i m;
      betree_Node_apply_messages_to_leaf n1 bindings1 new_msgs_tl
    | Betree_List_Nil => Ok bindings
    end
  end
.

(** [betree_main::betree::{betree_main::betree::Internal#4}::flush]:
    Source: 'src/betree.rs', lines 410:4-415:26 *)
Fixpoint betree_Internal_flush
  (n : nat) (self : betree_Internal_t) (params : betree_Params_t)
  (node_id_cnt : betree_NodeIdCounter_t)
  (content : betree_List_t (u64 * betree_Message_t)) (st : state) :
  result (state * ((betree_List_t (u64 * betree_Message_t)) *
    (betree_Internal_t * betree_NodeIdCounter_t)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    p <-
      betree_ListPairU64T_partition_at_pivot betree_Message_t n1 content
        self.(betree_Internal_pivot);
    let (msgs_left, msgs_right) := p in
    len_left <- betree_List_len (u64 * betree_Message_t) n1 msgs_left;
    if len_left s>= params.(betree_Params_min_flush_size)
    then (
      p1 <-
        betree_Node_apply_messages n1 self.(betree_Internal_left) params
          node_id_cnt msgs_left st;
      let (st1, p2) := p1 in
      let (n2, node_id_cnt1) := p2 in
      len_right <- betree_List_len (u64 * betree_Message_t) n1 msgs_right;
      if len_right s>= params.(betree_Params_min_flush_size)
      then (
        p3 <-
          betree_Node_apply_messages n1 self.(betree_Internal_right) params
            node_id_cnt1 msgs_right st1;
        let (st2, p4) := p3 in
        let (n3, node_id_cnt2) := p4 in
        Ok (st2, (Betree_List_Nil, (mkbetree_Internal_t
          self.(betree_Internal_id) self.(betree_Internal_pivot) n2 n3,
          node_id_cnt2))))
      else
        Ok (st1, (msgs_right, (mkbetree_Internal_t self.(betree_Internal_id)
          self.(betree_Internal_pivot) n2 self.(betree_Internal_right),
          node_id_cnt1))))
    else (
      p1 <-
        betree_Node_apply_messages n1 self.(betree_Internal_right) params
          node_id_cnt msgs_right st;
      let (st1, p2) := p1 in
      let (n2, node_id_cnt1) := p2 in
      Ok (st1, (msgs_left, (mkbetree_Internal_t self.(betree_Internal_id)
        self.(betree_Internal_pivot) self.(betree_Internal_left) n2,
        node_id_cnt1))))
  end

(** [betree_main::betree::{betree_main::betree::Node#5}::apply_messages]:
    Source: 'src/betree.rs', lines 588:4-593:5 *)
with betree_Node_apply_messages
  (n : nat) (self : betree_Node_t) (params : betree_Params_t)
  (node_id_cnt : betree_NodeIdCounter_t)
  (msgs : betree_List_t (u64 * betree_Message_t)) (st : state) :
  result (state * (betree_Node_t * betree_NodeIdCounter_t))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match self with
    | Betree_Node_Internal node =>
      p <- betree_load_internal_node node.(betree_Internal_id) st;
      let (st1, content) := p in
      content1 <- betree_Node_apply_messages_to_internal n1 content msgs;
      num_msgs <- betree_List_len (u64 * betree_Message_t) n1 content1;
      if num_msgs s>= params.(betree_Params_min_flush_size)
      then (
        p1 <- betree_Internal_flush n1 node params node_id_cnt content1 st1;
        let (st2, p2) := p1 in
        let (content2, p3) := p2 in
        let (node1, node_id_cnt1) := p3 in
        p4 <-
          betree_store_internal_node node1.(betree_Internal_id) content2 st2;
        let (st3, _) := p4 in
        Ok (st3, (Betree_Node_Internal node1, node_id_cnt1)))
      else (
        p1 <-
          betree_store_internal_node node.(betree_Internal_id) content1 st1;
        let (st2, _) := p1 in
        Ok (st2, (Betree_Node_Internal node, node_id_cnt)))
    | Betree_Node_Leaf node =>
      p <- betree_load_leaf_node node.(betree_Leaf_id) st;
      let (st1, content) := p in
      content1 <- betree_Node_apply_messages_to_leaf n1 content msgs;
      len <- betree_List_len (u64 * u64) n1 content1;
      i <- u64_mul 2%u64 params.(betree_Params_split_size);
      if len s>= i
      then (
        p1 <- betree_Leaf_split n1 node content1 params node_id_cnt st1;
        let (st2, p2) := p1 in
        let (new_node, node_id_cnt1) := p2 in
        p3 <- betree_store_leaf_node node.(betree_Leaf_id) Betree_List_Nil st2;
        let (st3, _) := p3 in
        Ok (st3, (Betree_Node_Internal new_node, node_id_cnt1)))
      else (
        p1 <- betree_store_leaf_node node.(betree_Leaf_id) content1 st1;
        let (st2, _) := p1 in
        Ok (st2, (Betree_Node_Leaf
          {| betree_Leaf_id := node.(betree_Leaf_id); betree_Leaf_size := len
          |}, node_id_cnt)))
    end
  end
.

(** [betree_main::betree::{betree_main::betree::Node#5}::apply]:
    Source: 'src/betree.rs', lines 576:4-582:5 *)
Definition betree_Node_apply
  (n : nat) (self : betree_Node_t) (params : betree_Params_t)
  (node_id_cnt : betree_NodeIdCounter_t) (key : u64)
  (new_msg : betree_Message_t) (st : state) :
  result (state * (betree_Node_t * betree_NodeIdCounter_t))
  :=
  p <-
    betree_Node_apply_messages n self params node_id_cnt (Betree_List_Cons
      (key, new_msg) Betree_List_Nil) st;
  let (st1, p1) := p in
  let (self1, node_id_cnt1) := p1 in
  Ok (st1, (self1, node_id_cnt1))
.

(** [betree_main::betree::{betree_main::betree::BeTree#6}::new]:
    Source: 'src/betree.rs', lines 849:4-849:60 *)
Definition betree_BeTree_new
  (min_flush_size : u64) (split_size : u64) (st : state) :
  result (state * betree_BeTree_t)
  :=
  node_id_cnt <- betree_NodeIdCounter_new;
  p <- betree_NodeIdCounter_fresh_id node_id_cnt;
  let (id, node_id_cnt1) := p in
  p1 <- betree_store_leaf_node id Betree_List_Nil st;
  let (st1, _) := p1 in
  Ok (st1,
    {|
      betree_BeTree_params :=
        {|
          betree_Params_min_flush_size := min_flush_size;
          betree_Params_split_size := split_size
        |};
      betree_BeTree_node_id_cnt := node_id_cnt1;
      betree_BeTree_root :=
        (Betree_Node_Leaf
          {| betree_Leaf_id := id; betree_Leaf_size := 0%u64 |})
    |})
.

(** [betree_main::betree::{betree_main::betree::BeTree#6}::apply]:
    Source: 'src/betree.rs', lines 868:4-868:47 *)
Definition betree_BeTree_apply
  (n : nat) (self : betree_BeTree_t) (key : u64) (msg : betree_Message_t)
  (st : state) :
  result (state * betree_BeTree_t)
  :=
  p <-
    betree_Node_apply n self.(betree_BeTree_root) self.(betree_BeTree_params)
      self.(betree_BeTree_node_id_cnt) key msg st;
  let (st1, p1) := p in
  let (n1, nic) := p1 in
  Ok (st1,
    {|
      betree_BeTree_params := self.(betree_BeTree_params);
      betree_BeTree_node_id_cnt := nic;
      betree_BeTree_root := n1
    |})
.

(** [betree_main::betree::{betree_main::betree::BeTree#6}::insert]:
    Source: 'src/betree.rs', lines 874:4-874:52 *)
Definition betree_BeTree_insert
  (n : nat) (self : betree_BeTree_t) (key : u64) (value : u64) (st : state) :
  result (state * betree_BeTree_t)
  :=
  betree_BeTree_apply n self key (Betree_Message_Insert value) st
.

(** [betree_main::betree::{betree_main::betree::BeTree#6}::delete]:
    Source: 'src/betree.rs', lines 880:4-880:38 *)
Definition betree_BeTree_delete
  (n : nat) (self : betree_BeTree_t) (key : u64) (st : state) :
  result (state * betree_BeTree_t)
  :=
  betree_BeTree_apply n self key Betree_Message_Delete st
.

(** [betree_main::betree::{betree_main::betree::BeTree#6}::upsert]:
    Source: 'src/betree.rs', lines 886:4-886:59 *)
Definition betree_BeTree_upsert
  (n : nat) (self : betree_BeTree_t) (key : u64)
  (upd : betree_UpsertFunState_t) (st : state) :
  result (state * betree_BeTree_t)
  :=
  betree_BeTree_apply n self key (Betree_Message_Upsert upd) st
.

(** [betree_main::betree::{betree_main::betree::BeTree#6}::lookup]:
    Source: 'src/betree.rs', lines 895:4-895:62 *)
Definition betree_BeTree_lookup
  (n : nat) (self : betree_BeTree_t) (key : u64) (st : state) :
  result (state * ((option u64) * betree_BeTree_t))
  :=
  p <- betree_Node_lookup n self.(betree_BeTree_root) key st;
  let (st1, p1) := p in
  let (o, n1) := p1 in
  Ok (st1, (o,
    {|
      betree_BeTree_params := self.(betree_BeTree_params);
      betree_BeTree_node_id_cnt := self.(betree_BeTree_node_id_cnt);
      betree_BeTree_root := n1
    |}))
.

(** [betree_main::main]:
    Source: 'src/betree_main.rs', lines 5:0-5:9 *)
Definition main : result unit :=
  Ok tt.

(** Unit test for [betree_main::main] *)
Check (main )%return.

End BetreeMain_Funs.
