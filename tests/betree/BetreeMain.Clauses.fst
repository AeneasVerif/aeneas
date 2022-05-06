(** [betree_main]: templates for the decreases clauses *)
module BetreeMain.Clauses
open Primitives
open BetreeMain.Types

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(** [betree_main::betree::List::{1}::len]: decreases clause *)
unfold
let betree_list_len_decreases (t : Type0) (self : betree_list_t t) : betree_list_t t =
  self

(** [betree_main::betree::List::{1}::split_at]: decreases clause *)
unfold
let betree_list_split_at_decreases (t : Type0) (self : betree_list_t t)
  (n : u64) : nat =
  n

(** [betree_main::betree::List::{2}::partition_at_pivot]: decreases clause *)
unfold
let betree_list_partition_at_pivot_decreases (t : Type0)
  (self : betree_list_t (u64 & t)) (pivot : u64) : betree_list_t (u64 & t) =
  self

(** [betree_main::betree::Node::{5}::lookup_in_bindings]: decreases clause *)
unfold
let betree_node_lookup_in_bindings_decreases (key : u64)
  (bindings : betree_list_t (u64 & u64)) : betree_list_t (u64 & u64) =
  bindings

(** [betree_main::betree::Node::{5}::lookup_first_message_for_key]: decreases clause *)
unfold
let betree_node_lookup_first_message_for_key_decreases (key : u64)
  (msgs : betree_list_t (u64 & betree_message_t)) : betree_list_t (u64 & betree_message_t) =
  msgs

(** [betree_main::betree::Node::{5}::apply_upserts]: decreases clause *)
unfold
let betree_node_apply_upserts_decreases
  (msgs : betree_list_t (u64 & betree_message_t)) (prev : option u64)
  (key : u64) (st : state) : betree_list_t (u64 & betree_message_t) =
  msgs

(** [betree_main::betree::Internal::{4}::lookup_in_children]: decreases clause *)
unfold
let betree_internal_lookup_in_children_decreases (self : betree_internal_t)
  (key : u64) (st : state) : betree_internal_t =
  self

(** [betree_main::betree::Node::{5}::lookup]: decreases clause *)
unfold
let betree_node_lookup_decreases (self : betree_node_t) (key : u64)
  (st : state) : betree_node_t =
  self

(** [betree_main::betree::Node::{5}::lookup_mut_in_bindings]: decreases clause *)
unfold
let betree_node_lookup_mut_in_bindings_decreases (key : u64)
  (bindings : betree_list_t (u64 & u64)) : betree_list_t (u64 & u64) =
  bindings

unfold
let betree_node_apply_messages_to_leaf_decreases
  (bindings : betree_list_t (u64 & u64))
  (new_msgs : betree_list_t (u64 & betree_message_t)) : betree_list_t (u64 & betree_message_t) =
  new_msgs

(** [betree_main::betree::Node::{5}::filter_messages_for_key]: decreases clause *)
unfold
let betree_node_filter_messages_for_key_decreases (key : u64)
  (msgs : betree_list_t (u64 & betree_message_t)) : betree_list_t (u64 & betree_message_t) =
  msgs

(** [betree_main::betree::Node::{5}::lookup_first_message_after_key]: decreases clause *)
unfold
let betree_node_lookup_first_message_after_key_decreases (key : u64)
  (msgs : betree_list_t (u64 & betree_message_t)) : betree_list_t (u64 & betree_message_t) =
  msgs

let betree_node_apply_messages_to_internal_decreases
  (msgs : betree_list_t (u64 & betree_message_t))
  (new_msgs : betree_list_t (u64 & betree_message_t)) : betree_list_t (u64 & betree_message_t) =
  new_msgs

(* This is annoying, we can't use the following trick when defining decrease
 * clauses as separate functions:
 * [https://github.com/FStarLang/FStar/issues/138]
 *
 * Note that the quantity which effectively decreases is:
 *
 *   [betree_size; messages_length]
 *   where messages_length is 0 when there are no messages
 *   (and where we use the lexicographic ordering, of course)
 *
 * For now, we "patch" the code directly (we need to find a better way...)
 *)
let rec betree_size (bt : betree_node_t) : nat =
  match bt with
  | BetreeNodeInternal node -> 1 + betree_internal_size node
  | BetreeNodeLeaf _ -> 1

and betree_internal_size (node : betree_internal_t) : nat =
  1 + betree_size node.betree_internal_left + betree_size node.betree_internal_right

let rec betree_list_len (#a : Type0) (ls : betree_list_t a) : nat =
  match ls with
  | BetreeListCons _ tl -> 1 + betree_list_len tl
  | BetreeListNil -> 0

(*
(** [betree_main::betree::Internal::{4}::flush]: decreases clause *)
unfold
let betree_internal_flush_decreases (self : betree_internal_t)
  (params : betree_params_t) (node_id_cnt : betree_node_id_counter_t)
  (content : betree_list_t (u64 & betree_message_t)) (st : state) : nat =
  admit ()

(** [betree_main::betree::Node::{5}::apply_messages]: decreases clause *)
unfold
let betree_node_apply_messages_decreases (self : betree_node_t)
  (params : betree_params_t) (node_id_cnt : betree_node_id_counter_t)
  (msgs : betree_list_t (u64 & betree_message_t)) (st : state) : nat =
  admit ()
*)
