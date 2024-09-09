(** [betree_main]: templates for the decreases clauses *)
module Betree.Clauses
open Primitives
open Betree.Types

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(*** Well-founded relations *)

(* We had a few issues when proving termination of the mutually recursive functions:
 * - betree_Internal_flush
 * - betree_Node_apply_messages
 *
 * The quantity which effectively decreases is:
 *   (betree_size, messages_length)
 *   where messages_length is 0 when there are no messages
 *   (and where we use the lexicographic ordering, of course)
 *
 * However, the `%[...]` and `{:well-founded ...} notations are not available outside
 * of `decrease` clauses.
 * 
 * We thus resorted to writing and proving correct a well-founded relation over
 * pairs of natural numbers. The trick is that `<<` can be used outside of decrease
 * clauses, and can be used to trigger SMT patterns.
 *
 * What follows is adapted from:
 * https://www.fstar-lang.org/tutorial/book/part2/part2_well_founded.html
 *
 * Also, the following PR might make things easier:
 * https://github.com/FStarLang/FStar/pull/2561
 *)

module P = FStar.Preorder
module W = FStar.WellFounded
module L = FStar.LexicographicOrdering

let lt_nat (x y:nat) : Type = x < y == true
let rec wf_lt_nat (x:nat)
  : W.acc lt_nat x
  = W.AccIntro (fun y _ -> wf_lt_nat y)

// A type abbreviation for a pair of nats
let nat_pair = (x:nat & nat)

// Making a lexicographic ordering from a pair of nat ordering
let lex_order_nat_pair  : P.relation nat_pair =
  L.lex_t lt_nat (fun _ -> lt_nat)

// The lex order on nat pairs is well-founded, using our general proof
// of lexicographic composition of well-founded orders
let lex_order_nat_pair_wf : W.well_founded lex_order_nat_pair =
  L.lex_t_wf wf_lt_nat (fun _ -> wf_lt_nat)

// A utility to introduce lt_nat
let mk_lt_nat (x:nat) (y:nat { x < y }) : lt_nat x y =
  let _ : equals (x < y) true = Refl in
  ()
    
// A utility to make a lex ordering of nat pairs
let mk_lex_order_nat_pair (xy0:nat_pair) 
                          (xy1:nat_pair {
                            let (|x0, y0|) = xy0 in
                            let (|x1, y1|) = xy1 in
                            x0 < x1 \/ (x0 == x1 /\ y0 < y1)
                          }) : lex_order_nat_pair xy0 xy1 =
  let (|x0, y0|) = xy0 in
  let (|x1, y1|) = xy1 in
  if x0 < x1 then L.Left_lex x0 x1 y0 y1 (mk_lt_nat x0 x1)
  else L.Right_lex x0 y0 y1 (mk_lt_nat y0 y1)

let rec coerce #a #r #x (p:W.acc #a r x) : Tot (W.acc r x) (decreases p) =
  W.AccIntro (fun y r -> coerce (p.access_smaller y r))

let coerce_wf #a #r (p: (x:a -> W.acc r x)) : x:a -> W.acc r x =
  fun x -> coerce (p x)

(* We need this axiom, which comes from the following discussion:
 * https://github.com/FStarLang/FStar/issues/1916
 * An issue here is that the `{well-founded ... }` notation
 *)
assume
val axiom_well_founded (a : Type) (rel : a -> a -> Type0)
  (rwf : W.well_founded #a rel) (x y : a) :
  Lemma (requires (rel x y)) (ensures (x << y))

(* This lemma has a pattern (which makes it work) *)
let wf_nat_pair_lem (p0 p1 : nat_pair) :
  Lemma
  (requires (
    let (|x0, y0|) = p0 in
    let (|x1, y1|) = p1 in
    x0 < x1 || (x0 = x1 && y0 < y1)))
  (ensures (p0 << p1))
  [SMTPat (p0 << p1)] =
  let rel = lex_order_nat_pair in
  let rel_wf = lex_order_nat_pair_wf in
  let _ = mk_lex_order_nat_pair p0 p1 in
  assert(rel p0 p1);
  axiom_well_founded nat_pair rel rel_wf p0 p1

(*** Decrease clauses *)
/// "Standard" decrease clauses

(** [betree_main::betree::List::{1}::len]: decreases clause *)
unfold
let betree_List_len_loop_decreases (#t : Type0) (self : betree_List_t t) (len : u64) : betree_List_t t =
  self

(** [betree::betree::{betree::betree::List<T>#1}::reverse]: decreases clause
    Source: 'src/betree.rs', lines 304:4-312:5 *)
unfold
let betree_List_reverse_loop_decreases (#t : Type0) (self : betree_List_t t)
  (out : betree_List_t t) =
  self

(** [betree::betree::{betree::betree::List<T>#1}::split_at]: decreases clause
    Source: 'src/betree.rs', lines 287:4-302:5 *)
unfold
let betree_List_split_at_loop_decreases (#t : Type0) (n : u64)
  (beg : betree_List_t t) (self : betree_List_t t) : nat =
  n

(** [betree::betree::{betree::betree::List<(u64, T)>#2}::partition_at_pivot]: decreases clause
    Source: 'src/betree.rs', lines 355:4-370:5 *)
unfold
let betree_ListPairU64T_partition_at_pivot_loop_decreases (#t : Type0)
  (pivot : u64) (beg : betree_List_t (u64 & t)) (end0 : betree_List_t (u64 & t))
  (self : betree_List_t (u64 & t)) =
  self

(** [betree_main::betree::Node::{5}::lookup_in_bindings]: decreases clause *)
unfold
let betree_Node_lookup_in_bindings_loop_decreases (key : u64)
  (bindings : betree_List_t (u64 & u64)) : betree_List_t (u64 & u64) =
  bindings

(** [betree_main::betree::Node::{5}::lookup_first_message_for_key]: decreases clause *)
unfold
let betree_Node_lookup_first_message_for_key_loop_decreases (key : u64)
  (msgs : betree_List_t (u64 & betree_Message_t)) : betree_List_t (u64 & betree_Message_t) =
  msgs

(** [betree_main::betree::Node::{5}::apply_upserts]: decreases clause *)
unfold
let betree_Node_apply_upserts_loop_decreases
  (msgs : betree_List_t (u64 & betree_Message_t)) (prev : option u64)
  (key : u64) : betree_List_t (u64 & betree_Message_t) =
  msgs

(** [betree_main::betree::Internal::{4}::lookup_in_children]: decreases clause *)
unfold
let betree_Internal_lookup_in_children_decreases (self : betree_Internal_t)
  (key : u64) (st : state) : betree_Internal_t =
  self

(** [betree_main::betree::Node::{5}::lookup]: decreases clause *)
unfold
let betree_Node_lookup_decreases (self : betree_Node_t) (key : u64)
  (st : state) : betree_Node_t =
  self

(** [betree_main::betree::Node::{5}::lookup_mut_in_bindings]: decreases clause *)
unfold
let betree_Node_lookup_mut_in_bindings_loop_decreases (key : u64)
  (bindings : betree_List_t (u64 & u64)) : betree_List_t (u64 & u64) =
  bindings

unfold
let betree_Node_apply_messages_to_leaf_loop_decreases
  (bindings : betree_List_t (u64 & u64))
  (new_msgs : betree_List_t (u64 & betree_Message_t)) : betree_List_t (u64 & betree_Message_t) =
  new_msgs

(** [betree_main::betree::Node::{5}::filter_messages_for_key]: decreases clause *)
unfold
let betree_Node_filter_messages_for_key_loop_decreases (key : u64)
  (msgs : betree_List_t (u64 & betree_Message_t)) : betree_List_t (u64 & betree_Message_t) =
  msgs

(** [betree_main::betree::Node::{5}::lookup_first_message_after_key]: decreases clause *)
unfold
let betree_Node_lookup_first_message_after_key_loop_decreases (key : u64)
  (msgs : betree_List_t (u64 & betree_Message_t)) : betree_List_t (u64 & betree_Message_t) =
  msgs

let betree_Node_apply_messages_to_internal_loop_decreases
  (msgs : betree_List_t (u64 & betree_Message_t))
  (new_msgs : betree_List_t (u64 & betree_Message_t)) : betree_List_t (u64 & betree_Message_t) =
  new_msgs

(*** Decrease clauses - nat_pair *)
/// The following decrease clauses use the [nat_pair] definition and the well-founded
/// relation proven above.

let rec betree_size (bt : betree_Node_t) : nat =
  match bt with
  | Betree_Node_Internal node -> 1 + betree_Internal_size node
  | Betree_Node_Leaf _ -> 1

and betree_Internal_size (node : betree_Internal_t) : nat =
  1 + betree_size node.left + betree_size node.right

let rec betree_List_len (#a : Type0) (ls : betree_List_t a) : nat =
  match ls with
  | Betree_List_Cons _ tl -> 1 + betree_List_len tl
  | Betree_List_Nil -> 0

(** [betree_main::betree::Internal::{4}::flush]: decreases clause *)
unfold
let betree_Internal_flush_decreases (self : betree_Internal_t)
  (params : betree_Params_t) (node_id_cnt : betree_NodeIdCounter_t)
  (content : betree_List_t (u64 & betree_Message_t)) (st : state) : nat_pair =
  (|betree_Internal_size self, 0|)

(** [betree_main::betree::Node::{5}::apply_messages]: decreases clause *)
unfold
let betree_Node_apply_messages_decreases (self : betree_Node_t)
  (params : betree_Params_t) (node_id_cnt : betree_NodeIdCounter_t)
  (msgs : betree_List_t (u64 & betree_Message_t)) (st : state) : nat_pair =
  (|betree_size self, betree_List_len msgs|)
