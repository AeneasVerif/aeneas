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

(*** new *)

/// [new] doesn't fail and returns an empty hash map
val hash_map_new_fwd_lem (t : Type0) :
  Lemma
  (ensures (
    match hash_map_new_fwd t with
    | Fail -> False
    | Return hm ->
      // The hash map invariant is satisfied
      hash_map_t_inv hm /\
      // The hash map has a length of 0
      len_s hm = 0 /\
      // It contains no bindings
      (forall k. find_s hm k == None)))

(*** [clear] *)

/// [clear] doesn't fail and turns the hash map into an empty map
val hash_map_clear_fwd_back_lem
  (#t : Type0) (self : hash_map_t t) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_clear_fwd_back t self with
    | Fail -> False
    | Return hm ->
      // The hash map invariant is satisfied
      hash_map_t_inv hm /\
      // The hash map has a length of 0
      len_s hm = 0 /\
      // It contains no bindings
      (forall k. find_s hm k == None)))

(*** [len] *)

/// [len] can't fail and returns the length (the number of elements) of the hash map
val hash_map_len_fwd_lem (#t : Type0) (self : hash_map_t t) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_len_fwd t self with
    | Fail -> False
    | Return l -> l = len_s self))


(*** [insert'fwd_back] *)

/// The backward function for [insert] (note it is named "...'fwd_back" because
/// the forward function doesn't return anything, and is was thus filtered - in a
/// sense the effect of applying the forward function then the backward function is
/// entirely given by the backward function alone).
/// [insert'fwd_back] simply inserts a binding.
val hash_map_insert_fwd_back_lem
  (#t : Type0) (self : hash_map_t t) (key : usize) (value : t) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_insert_fwd_back t self key value with
    | Fail ->
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


(*** [contains_key] *)

/// [contains_key'fwd] can't fail and return `true` if and only if there is
/// a binding for key [key]
val hash_map_contains_key_fwd_lem
  (#t : Type0) (self : hash_map_t t) (key : usize) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_contains_key_fwd t self key with
    | Fail -> False
    | Return b -> b = Some? (find_s self key)))

(*** [get'fwd] *)

/// [get] returns (a shared borrow to) the binding for key [key]
val hash_map_get_fwd_lem
  (#t : Type0) (self : hash_map_t t) (key : usize) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_get_fwd t self key, find_s self key with
    | Fail, None -> True
    | Return x, Some x' -> x == x'
    | _ -> False))

(*** [get_mut'fwd] *)

/// [get_mut'fwd] returns (mutable borrows to) the binding for key [key].
val hash_map_get_mut_fwd_lem
  (#t : Type0) (self : hash_map_t t) (key : usize) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_get_mut_fwd t self key, find_s self key with
    | Fail, None -> True
    | Return x, Some x' -> x == x'
    | _ -> False))


(*** [get_mut'back] *)

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
    Some? (find_s hm key)))
  (ensures (
    match hash_map_get_mut_back t hm key ret with
    | Fail -> False // Can't fail
    | Return hm' ->
     // The invariant is preserved
     hash_map_t_inv hm' /\
     // The length is preserved
     len_s hm' = len_s hm /\
     // [key] maps to the update value, [ret]
     find_s hm' key == Some ret /\
     // The other bindings are preserved
     (forall k'. k' <> key ==> find_s hm' k' == find_s hm k')))

(*** [remove'fwd] *)

/// [remove'fwd] returns the (optional) element which has been removed from the map
/// (the rust function *moves* it out of the map).
val hash_map_remove_fwd_lem
  (#t : Type0) (self : hash_map_t t) (key : usize) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_remove_fwd t self key with
    | Fail -> False
    | Return opt_x -> opt_x == find_s self key))


(*** [remove'back] *)

/// The hash map given as parameter to [remove] is given through a mutable borrow:
/// hence the backward function which gives back the updated map, without the
/// binding.
val hash_map_remove_back_lem
  (#t : Type0) (self : hash_map_t t) (key : usize) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_remove_back t self key with
    | Fail -> False
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
