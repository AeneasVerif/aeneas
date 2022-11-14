(** Properties about the hashmap *)
module Hashmap.Properties
open Primitives
open FStar.List.Tot
open FStar.Mul
open Hashmap.Types
open Hashmap.Clauses
open Hashmap.Funs

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

// Small trick to align the .fst and the .fsti
val _align_fsti : unit

(*** Utilities *)

type key : eqtype = usize

type hash : eqtype = usize

val hash_map_t_inv (#t : Type0) (hm : hash_map_t t) : Type0

val len_s (#t : Type0) (hm : hash_map_t t) : nat

val find_s (#t : Type0) (hm : hash_map_t t) (k : key) : option t

(*** Overloading *)

/// Upon inserting *new* entries in the hash map, the slots vector is resized
/// whenever we reach the max load, unless we can't resize anymore because
/// there are already too many entries. This way, we maintain performance by
/// limiting the hash collisions.
/// This is expressed by the following property, which is maintained in the hash
/// map invariant.
val hash_map_not_overloaded_lem (#t : Type0) (hm : hash_map_t t) :
  Lemma
  (requires (hash_map_t_inv hm))
  (ensures (
    // The capacity is the number of slots
    let capacity = length hm.hash_map_slots in
    // The max load factor defines a threshold on the number of entries:
    // if there are more entries than a given fraction of the number of slots,
    // we resize the slots vector to limit the hash collisions
    let (dividend, divisor) = hm.hash_map_max_load_factor in
    // technicality: this postcondition won't typecheck if we don't reveal
    // that divisor > 0 (because of the division)
    divisor > 0 /\
    begin
    // The max load, computed as a fraction of the capacity
    let max_load = (capacity * dividend) / divisor in
    // The number of entries inserted in the map is given by [len_s] (see
    // the functional correctness lemmas, which state how this number evolves):
    let len = len_s hm in
    // We prove that:
    // - either the number of entries is <= than the max load threshold
    len <= max_load
    // - or we couldn't resize the map, because then the arithmetic computations
    //   would overflow (note that we always multiply the number of slots by 2)
    || 2* capacity * dividend > usize_max
    end))

(*** Functional correctness *)
(**** [new'fwd] *)

/// [new] doesn't fail and returns an empty hash map
val hash_map_new_fwd_lem (t : Type0) :
  Lemma
  (ensures (
    match hash_map_new_fwd t with
    | Fail _ -> False
    | Return hm ->
      // The hash map invariant is satisfied
      hash_map_t_inv hm /\
      // The hash map has a length of 0
      len_s hm = 0 /\
      // It contains no bindings
      (forall k. find_s hm k == None)))

(**** [clear] *)

/// [clear] doesn't fail and turns the hash map into an empty map
val hash_map_clear_fwd_back_lem
  (#t : Type0) (self : hash_map_t t) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_clear_fwd_back t self with
    | Fail _ -> False
    | Return hm ->
      // The hash map invariant is satisfied
      hash_map_t_inv hm /\
      // The hash map has a length of 0
      len_s hm = 0 /\
      // It contains no bindings
      (forall k. find_s hm k == None)))

(**** [len] *)

/// [len] can't fail and returns the length (the number of elements) of the hash map
val hash_map_len_fwd_lem (#t : Type0) (self : hash_map_t t) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_len_fwd t self with
    | Fail _ -> False
    | Return l -> l = len_s self))


(**** [insert'fwd_back] *)

/// The backward function for [insert] (note it is named "...insert'fwd_back" because
/// the forward function doesn't return anything, and was thus filtered - in a
/// sense the effect of applying the forward function then the backward function is
/// entirely encompassed by the effect of the backward function alone).
/// 
/// [insert'fwd_back] simply inserts a binding.
val hash_map_insert_fwd_back_lem
  (#t : Type0) (self : hash_map_t t) (key : usize) (value : t) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_insert_fwd_back t self key value with
    | Fail _ ->
      // We can fail only if:
      // - the key is not in the map and we thus need to add it
      None? (find_s self key) /\
      // - and we are already saturated (we can't increment the internal counter)
      len_s self = usize_max
    | Return hm' ->
      // The invariant is preserved
      hash_map_t_inv hm' /\
      // [key] maps to [value]
      find_s hm' key == Some value /\
      // The other bindings are preserved
      (forall k'. k' <> key ==> find_s hm' k' == find_s self k') /\
      begin
      // The length is incremented, iff we inserted a new key
      match find_s self key with
      | None -> len_s hm' = len_s self + 1
      | Some _ -> len_s hm' = len_s self
      end))


(**** [contains_key] *)

/// [contains_key'fwd] can't fail and returns `true` if and only if there is
/// a binding for key [key]
val hash_map_contains_key_fwd_lem
  (#t : Type0) (self : hash_map_t t) (key : usize) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_contains_key_fwd t self key with
    | Fail _ -> False
    | Return b -> b = Some? (find_s self key)))

(**** [get'fwd] *)

/// [get] returns (a shared borrow to) the binding for key [key]
val hash_map_get_fwd_lem
  (#t : Type0) (self : hash_map_t t) (key : usize) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_get_fwd t self key, find_s self key with
    | Fail _, None -> True
    | Return x, Some x' -> x == x'
    | _ -> False))

(**** [get_mut'fwd] *)

/// [get_mut'fwd] returns (a mutable borrow to) the binding for key [key].
/// 
/// The *forward* function models the action of getting a borrow to an element
/// in Rust, which gives the possibility of modifying this element in place. Then,
/// upon ending the borrow, the effect of the modification is modelled in the
/// translation through a call to the backward function.
val hash_map_get_mut_fwd_lem
  (#t : Type0) (self : hash_map_t t) (key : usize) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_get_mut_fwd t self key, find_s self key with
    | Fail _, None -> True
    | Return x, Some x' -> x == x'
    | _ -> False))


(**** [get_mut'back] *)

/// [get_mut'back] updates the binding for key [key], without failing.
/// A call to [get_mut'back] must follow a call to [get_mut'fwd], which gives
/// us that there must be a binding for key [key] in the map (otherwise we
/// can't prove the absence of failure).
val hash_map_get_mut_back_lem
  (#t : Type0) (hm : hash_map_t t) (key : usize) (ret : t) :
  Lemma
  (requires (
    hash_map_t_inv hm /\
    // A call to the backward function must follow a call to the forward
    // function, whose success gives us that there is a binding for the key.
    // In the case of *forward* functions, "success" has to be understood as
    // the absence of panics. When translating code from Rust to pure lambda
    // calculus, we have the property that the generated calls to the backward
    // functions can't fail (because their are preceded by calls to forward
    // functions, which must then have succeeded before): for a backward function,
    // "failure" is to be understood as the semantics getting stuck.
    // This is of course true unless we filtered the call to the forward function
    // because its effect is encompassed by the backward function, as with
    // [hash_map_clear_fwd_back]).
    Some? (find_s hm key)))
  (ensures (
    match hash_map_get_mut_back t hm key ret with
    | Fail _ -> False // Can't fail
    | Return hm' ->
     // The invariant is preserved
     hash_map_t_inv hm' /\
     // The length is preserved
     len_s hm' = len_s hm /\
     // [key] maps to the update value, [ret]
     find_s hm' key == Some ret /\
     // The other bindings are preserved
     (forall k'. k' <> key ==> find_s hm' k' == find_s hm k')))

(**** [remove'fwd] *)

/// [remove'fwd] returns the (optional) element which has been removed from the map
/// (the rust function *moves* it out of the map). Note that the effect of the update
/// on the map is modelles through the call to [remove'back] ([remove] takes a
/// mutable borrow to the hash map as parameter).
val hash_map_remove_fwd_lem
  (#t : Type0) (self : hash_map_t t) (key : usize) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_remove_fwd t self key with
    | Fail _ -> False
    | Return opt_x -> opt_x == find_s self key))


(**** [remove'back] *)

/// The hash map given as parameter to [remove] is given through a mutable borrow:
/// hence the backward function which gives back the updated map, without the
/// binding.
val hash_map_remove_back_lem
  (#t : Type0) (self : hash_map_t t) (key : usize) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_remove_back t self key with
    | Fail _ -> False
    | Return hm' ->
      // The invariant is preserved
      hash_map_t_inv self /\
      // The binding for [key] is not there anymore
      find_s hm' key == None /\
      // The other bindings are preserved
      (forall k'. k' <> key ==> find_s hm' k' == find_s self k') /\
      begin
      // The length is decremented iff the key was in the map
      let len = len_s self in
      let len' = len_s hm' in
      match find_s self key with
      | None -> len = len'
      | Some _ -> len = len' + 1
      end))
