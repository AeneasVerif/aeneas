(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [betree]: type definitions *)
module Betree.Types
open Primitives
include Betree.TypesExternal

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [betree::betree::List]
    Source: 'src/betree.rs', lines 17:0-17:23 *)
type betree_List_t (t : Type0) =
| Betree_List_Cons : t -> betree_List_t t -> betree_List_t t
| Betree_List_Nil : betree_List_t t

(** [betree::betree::UpsertFunState]
    Source: 'src/betree.rs', lines 63:0-63:23 *)
type betree_UpsertFunState_t =
| Betree_UpsertFunState_Add : u64 -> betree_UpsertFunState_t
| Betree_UpsertFunState_Sub : u64 -> betree_UpsertFunState_t

(** [betree::betree::Message]
    Source: 'src/betree.rs', lines 69:0-69:23 *)
type betree_Message_t =
| Betree_Message_Insert : u64 -> betree_Message_t
| Betree_Message_Delete : betree_Message_t
| Betree_Message_Upsert : betree_UpsertFunState_t -> betree_Message_t

(** [betree::betree::Leaf]
    Source: 'src/betree.rs', lines 167:0-167:11 *)
type betree_Leaf_t = { id : u64; size : u64; }

(** [betree::betree::Internal]
    Source: 'src/betree.rs', lines 156:0-156:15 *)
type betree_Internal_t =
{
  id : u64; pivot : u64; left : betree_Node_t; right : betree_Node_t;
}

(** [betree::betree::Node]
    Source: 'src/betree.rs', lines 179:0-179:9 *)
and betree_Node_t =
| Betree_Node_Internal : betree_Internal_t -> betree_Node_t
| Betree_Node_Leaf : betree_Leaf_t -> betree_Node_t

(** [betree::betree::Params]
    Source: 'src/betree.rs', lines 187:0-187:13 *)
type betree_Params_t = { min_flush_size : u64; split_size : u64; }

(** [betree::betree::NodeIdCounter]
    Source: 'src/betree.rs', lines 201:0-201:20 *)
type betree_NodeIdCounter_t = { next_node_id : u64; }

(** [betree::betree::BeTree]
    Source: 'src/betree.rs', lines 218:0-218:17 *)
type betree_BeTree_t =
{
  params : betree_Params_t;
  node_id_cnt : betree_NodeIdCounter_t;
  root : betree_Node_t;
}

