(** [betree_main]: templates for the decreases clauses *)
module BetreeMain.Clauses
open Primitives
open BetreeMain.Types

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(** [betree_main::betree::List::{1}::len]: decreases clause *)
unfold
let betree_list_1_len_decreases (t : Type0) (self : betree_list_t t) : nat =
  admit ()

(** [betree_main::betree::List::{1}::split_at]: decreases clause *)
unfold
let betree_list_1_split_at_decreases (t : Type0) (self : betree_list_t t)
  (n : u64) : nat =
  admit ()

(** [betree_main::betree::List::{2}::partition_at_pivot]: decreases clause *)
unfold
let betree_list_2_partition_at_pivot_decreases (t : Type0)
  (self : betree_list_t (u64 & t)) (pivot : u64) : nat =
  admit ()

(** [betree_main::betree::Node::{5}::lookup_in_bindings]: decreases clause *)
unfold
let betree_node_5_lookup_in_bindings_decreases (key : u64)
  (bindings : betree_list_t (u64 & u64)) : nat =
  admit ()

(** [betree_main::betree::Node::{5}::lookup_first_message_for_key]: decreases clause *)
unfold
let betree_node_5_lookup_first_message_for_key_decreases (key : u64)
  (msgs : betree_list_t (u64 & betree_message_t)) : nat =
  admit ()

(** [betree_main::betree::Node::{5}::apply_upserts]: decreases clause *)
unfold
let betree_node_5_apply_upserts_decreases
  (msgs : betree_list_t (u64 & betree_message_t)) (prev : option u64)
  (key : u64) (st : state) : nat =
  admit ()

(** [betree_main::betree::Internal::{4}::lookup_in_children]: decreases clause *)
unfold
let betree_internal_4_lookup_in_children_decreases (self : betree_internal_t)
  (key : u64) (st : state) : nat =
  admit ()

(** [betree_main::betree::Node::{5}::lookup]: decreases clause *)
unfold
let betree_node_5_lookup_decreases (self : betree_node_t) (key : u64)
  (st : state) : nat =
  admit ()

(** [betree_main::betree::Node::{5}::lookup_mut_in_bindings]: decreases clause *)
unfold
let betree_node_5_lookup_mut_in_bindings_decreases (key : u64)
  (bindings : betree_list_t (u64 & u64)) : nat =
  admit ()

(** [betree_main::betree::Node::{5}::filter_messages_for_key]: decreases clause *)
unfold
let betree_node_5_filter_messages_for_key_decreases (key : u64)
  (msgs : betree_list_t (u64 & betree_message_t)) : nat =
  admit ()

(** [betree_main::betree::Node::{5}::lookup_first_message_after_key]: decreases clause *)
unfold
let betree_node_5_lookup_first_message_after_key_decreases (key : u64)
  (msgs : betree_list_t (u64 & betree_message_t)) : nat =
  admit ()

(** [betree_main::betree::Internal::{4}::flush]: decreases clause *)
unfold
let betree_internal_4_flush_decreases (self : betree_internal_t)
  (params : betree_params_t) (node_id_cnt : betree_node_id_counter_t)
  (content : betree_list_t (u64 & betree_message_t)) (st : state) : nat =
  admit ()

(** [betree_main::betree::Node::{5}::apply_messages]: decreases clause *)
unfold
let betree_node_5_apply_messages_decreases (self : betree_node_t)
  (params : betree_params_t) (node_id_cnt : betree_node_id_counter_t)
  (msgs : betree_list_t (u64 & betree_message_t)) (st : state) : nat =
  admit ()

(** [betree_main::betree::Node::{5}::apply]: decreases clause *)
unfold
let betree_node_5_apply_decreases (self : betree_node_t)
  (params : betree_params_t) (node_id_cnt : betree_node_id_counter_t)
  (key : u64) (new_msg : betree_message_t) (st : state) : nat =
  admit ()

