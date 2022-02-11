(** Properties about the hashmap *)
module Hashmap.Properties
open Primitives
open FStar.List.Tot
open FStar.Mul
open Hashmap.Types
open Hashmap.Clauses
open Hashmap.Funs

// To help with the proofs
module InteractiveHelpers = FStar.InteractiveHelpers

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

(*** List lemmas *)

val index_append_lem (#a : Type0) (ls0 ls1 : list a) (i : nat{i < length ls0 + length ls1}) :
  Lemma (
    (i < length ls0 ==> index (ls0 @ ls1) i == index ls0 i) /\
    (i >= length ls0 ==> index (ls0 @ ls1) i == index ls1 (i - length ls0)))
  [SMTPat (index (ls0 @ ls1) i)]

#push-options "--fuel 1"
let rec index_append_lem #a ls0 ls1 i =
  match ls0 with
  | [] -> ()
  | x :: ls0' ->
    if i = 0 then ()
    else index_append_lem ls0' ls1 (i-1)
#pop-options

// TODO: remove?
// Returns the index of the value which satisfies the predicate
val find_index :
    #a:Type
  -> f:(a -> Tot bool)
  -> ls:list a{Some? (find f ls)}
  -> Tot (i:nat{
    i < length ls /\
    begin match find f ls with
    | None -> False
    | Some x -> x == index ls i
    end})

#push-options "--fuel 1"
let rec find_index #a f ls =
  match ls with
  | [] -> assert(False); 0
  | x :: ls' ->
    if f x then 0
    else 1 + find_index f ls'
#pop-options


(*** Lemmas about Primitives *)
/// TODO: move those lemmas

val list_update_index_dif_lem
  (#a : Type0) (ls : list a) (i : nat{i < length ls}) (x : a)
  (j : nat{j < length ls}) :
  Lemma (requires (j <> i))
  (ensures (index (list_update ls i x) j == index ls j))
  [SMTPat (index (list_update ls i x) j)]
#push-options "--fuel 1"
let rec list_update_index_dif_lem #a ls i x j =
  match ls with
  | x' :: ls ->
    if i = 0 then ()
    else if j = 0 then ()
    else
     list_update_index_dif_lem ls (i-1) x (j-1)
#pop-options


(*** Utilities *)
// TODO: filter the utilities

val find_update:
     #a:Type
  -> f:(a -> Tot bool)
  -> ls:list a
  -> x:a
  -> ls':list a{length ls' == length ls}
#push-options "--fuel 1"
let rec find_update #a f ls x =
  match ls with
  | [] -> []
  | hd::tl ->
    if f hd then x :: tl else hd :: find_update f tl x
#pop-options

val pairwise_distinct : #a:eqtype -> ls:list a -> Tot bool
let rec pairwise_distinct (#a : eqtype) (ls : list a) : Tot bool =
  match ls with
  | [] -> true
  | x :: ls' -> List.Tot.for_all (fun y -> x <> y) ls' && pairwise_distinct ls'

val for_allP: #a:Type -> f:(a -> Tot Type0) -> list a -> Tot Type0
let rec for_allP (f : 'a -> Tot Type0) (l : list 'a) : Tot Type0 =
  match l with
  | [] -> True
  | hd::tl -> f hd /\ for_allP f tl

val for_all_i_aux: #a:Type -> f:(nat -> a -> Tot bool) -> list a -> nat -> Tot bool
let rec for_all_i_aux (f : nat -> 'a -> Tot bool) (l : list 'a) (i : nat) : Tot bool =
  match l with
  | [] -> true
  | hd::tl -> f i hd && for_all_i_aux f tl (i+1)

val for_all_i: #a:Type -> f:(nat -> a -> Tot bool) -> list a -> Tot bool
let for_all_i (f : nat -> 'a -> Tot bool) (l : list 'a) : Tot bool =
  for_all_i_aux f l 0

val pairwise_relP : #a:Type -> pred:(a -> a -> Tot Type0) -> ls:list a -> Tot Type0
let rec pairwise_relP #a pred ls =
  match ls with
  | [] -> True
  | x :: ls' ->
    for_allP (pred x) ls' /\ pairwise_relP pred ls'

val pairwise_rel : #a:Type -> pred:(a -> a -> Tot bool) -> ls:list a -> Tot bool
let rec pairwise_rel #a pred ls =
  match ls with
  | [] -> true
  | x :: ls' ->
    List.Tot.for_all (pred x) ls' && pairwise_rel pred ls' 

/// The lack of lemmas about list manipulation is really annoying...

#push-options "--fuel 1"
let rec flatten_append (#a : Type) (l1 l2: list (list a)) :
  Lemma (flatten (l1 @ l2) == flatten l1 @ flatten l2) =
  match l1 with
  | [] -> ()
  | x :: l1' ->
    flatten_append l1' l2;
    append_assoc x (flatten l1') (flatten l2)
#pop-options

/// We don't use anonymous functions as parameters to other functions, but rather
/// introduce auxiliary functions instead: otherwise we can't reason (because
/// F*'s encoding to the SMT is imprecise for functions)
let fst_is_disctinct (#a : eqtype) (#b : Type0) (p0 : a & b) (p1 : a & b) : Type0 =
  fst p0 <> fst p1

(*** Invariants, models *)

(*
/// "Natural" length function for [list_t]
/// TODO: remove? we can reason simply with [list_t_v]
let rec list_t_len (#t : Type0) (ls : list_t t) : nat =
  match ls with
  | ListNil -> 0
  | ListCons _ _ tl -> 1 + list_t_len tl
*)

(*
/// "Natural" append function for [list_t]
/// TODO: remove? we can reason simply with [list_t_v]
#push-options "--fuel 1"
let rec list_t_append (#t : Type0) (ls0 ls1 : list_t t) :
  ls:list_t t{list_t_len ls = list_t_len ls0 + list_t_len ls1} =
  match ls0 with
  | ListNil -> ls1
  | ListCons x v tl -> ListCons x v (list_t_append tl ls1)
#pop-options
*)

/// The "key" type
type key : eqtype = usize

type hash : eqtype = usize

type binding (t : Type0) = key & t

type slots_t (t : Type0) = vec (list_t t)

/// We represent hash maps as associative lists
type assoc_list (t : Type0) = list (binding t)

/// Representation function for [list_t]
let rec list_t_v (#t : Type0) (ls : list_t t) : assoc_list t =
  match ls with
  | ListNil -> []
  | ListCons k v tl -> (k,v) :: list_t_v tl

let list_t_len (#t : Type0) (ls : list_t t) : nat = length (list_t_v ls)
let list_t_index (#t : Type0) (ls : list_t t) (i : nat{i < list_t_len ls}) : binding t =
  index (list_t_v ls) i

/// Representation function for the slots.
/// Rk.: I hesitated to use [concatMap]
let slots_t_v (#t : Type0) (slots : slots_t t) : assoc_list t =
  flatten (map list_t_v slots)

/// Representation function for [hash_map_t]
let hash_map_t_v (#t : Type0) (hm : hash_map_t t) : assoc_list t =
  slots_t_v hm.hash_map_slots

let hash_key (k : key) : hash =
  Return?.v (hash_key_fwd k)

let hash_mod_key (k : key) (len : usize{len > 0}) : hash =
  (hash_key k) % len

let same_key (#t : Type0) (k : key) (b : binding t) : bool = fst b = k

// We take a [nat] instead of a [hash] on purpose
let same_hash_mod_key (#t : Type0) (len : usize{len > 0}) (h : nat) (b : binding t) : bool =
  hash_mod_key (fst b) len = h

// We take a [nat] instead of a [hash] on purpose
(*let same_hash (#t : Type0) (h : nat) (b : binding t) : bool = hash_key (fst b) = h *)

let binding_neq (#t : Type0) (b0 b1 : binding t) : bool = fst b0 <> fst b1

let has_same_binding (#t : Type0) (al : assoc_list t) ((k,v) : binding t) : Type0 =
  match find (same_key k) al with
  | None -> False
  | Some (k',v') -> v' == v

let hash_map_t_mem (#t : Type0) (hm : hash_map_t t) (k : key) : bool =
  existsb (same_key k) (hash_map_t_v hm)

let hash_map_t_len (#t : Type0) (hm : hash_map_t t) : nat =
  hm.hash_map_num_entries

let slot_t_v_find (#t : Type0) (k : key) (slot : list (binding t)) : option t =
  match find (same_key k) slot with
  | None -> None
  | Some (_, v) -> Some v

let slot_t_find (#t : Type0) (k : key) (slot : list_t t) : option t =
  match find (same_key k) (list_t_v slot) with
  | None -> None
  | Some (_, v) -> Some v

// This is a simpler version of the "find" function, which captures the essence
// of what happens.
let hash_map_t_find
  (#t : Type0) (hm : hash_map_t t{length hm.hash_map_slots > 0}) (k : key) : option t =
  let slots = hm.hash_map_slots in
  let i = hash_mod_key k (length slots) in
  let slot = index slots i in
  slot_t_find k slot

(*let hash_map_t_find (#t : Type0) (hm : hash_map_t t) (k : key) : option t =
 match find (same_key k) (hash_map_t_v hm) with
 | None -> None
 | Some (_, v) -> Some v*)

/// Auxiliary function stating that two associative lists are "equivalent"
let assoc_list_equiv (#t : Type0) (al0 al1 : assoc_list t) : Type0 =
  // All the bindings in al0 can be found in al1
  for_allP (has_same_binding al1) al0 /\
  // And the reverse is true
  for_allP (has_same_binding al0) al1

// Introducing auxiliary definitions to help deal with the quantifiers

let not_same_keys_at_j_k
  (#t : Type0) (ls : list_t t) (j:nat{j < list_t_len ls}) (k:nat{k < list_t_len ls}) :
  Type0 =
  fst (list_t_index ls j) <> fst (list_t_index ls k)

(*let not_same_keys_at_j_k
  (#t : Type0) (ls : list_t t) (j:nat{j < list_t_len ls}) (k:nat{k < list_t_len ls}) :
  Type0 =
  fst (list_t_index ls j) <> fst (list_t_index ls k)*)

type slot_t_inv_hash_key_f (#t : Type0) (len : usize{len > 0}) (i : usize) (slot : list_t t) =
  (j:nat{j < list_t_len slot}) ->
  Lemma (hash_mod_key (fst (list_t_index slot j)) len = i)
  [SMTPat (hash_mod_key (fst (list_t_index slot j)) len)]
  
type slot_t_inv_not_same_keys_f (#t : Type0) (i : usize) (slot : list_t t) =
     (j:nat{j < list_t_len slot})
  -> (k:nat{k < list_t_len slot /\ j < k})
  -> Lemma (not_same_keys_at_j_k slot j k)
  [SMTPat (not_same_keys_at_j_k slot j k)]

(**)

/// Invariants for the slots
/// Rk.: making sure the quantifiers instantiations work was painful. As always.

let slot_t_v_inv
(#t : Type0) (len : usize{len > 0}) (i : usize) (slot : list (binding t)) : bool =
  // All the bindings are in the proper slot
  for_all (same_hash_mod_key len i) slot &&
  // All the keys are pairwise distinct
  pairwise_rel binding_neq slot

let slot_t_inv (#t : Type0) (len : usize{len > 0}) (i : usize) (slot : list_t t) : bool =
  // All the bindings are in the proper slot
  for_all (same_hash_mod_key len i) (list_t_v slot) &&
  // All the keys are pairwise distinct
  pairwise_rel binding_neq (list_t_v slot)

(*
/// Invariants for the slots
/// Rk.: making sure the quantifiers instantiations work was painful. As always.
let slot_t_inv (#t : Type0) (len : usize{len > 0}) (i : usize) (slot : list_t t) : Type0 =
  // All the hashes of the keys are equal to the current hash
  (forall (j:nat{j < list_t_len slot}).
    {:pattern (list_t_index slot j)}
    hash_mod_key (fst (list_t_index slot j)) len = i) /\
  // All the keys are pairwise distinct
  (forall (j:nat{j < list_t_len slot}) (k:nat{k < list_t_len slot /\ j < k}).
    {:pattern not_same_keys_at_j_k slot j k}
    k <> j ==> not_same_keys_at_j_k slot j k)

/// Helpers to deal with the quantifier proofs
let slot_t_inv_to_funs
  (#t : Type0) (len : usize{len > 0}) (i : usize) (slot : list_t t{slot_t_inv len i slot}) :
  slot_t_inv_hash_key_f len i slot & slot_t_inv_not_same_keys_f i slot =
  let f : slot_t_inv_hash_key_f len i slot =
    fun j -> ()
  in
  let g : slot_t_inv_not_same_keys_f i slot =
    fun j k -> ()
  in
  (f, g)

let slot_t_inv_from_funs_lem
  (#t : Type0) (len : usize{len > 0}) (i : usize) (slot : list_t t)
  (f : slot_t_inv_hash_key_f len i slot)
  (g : slot_t_inv_not_same_keys_f i slot) :
  Lemma (slot_t_inv len i slot) =
  // Dealing with quantifiers is annoying, like always
  let f' (j:nat{j < list_t_len slot}) :
    Lemma (hash_mod_key (fst (list_t_index slot j)) len = i)
    [SMTPat (hash_mod_key (fst (list_t_index slot j)) len)]
    =
    f j
  in
  let g' (j:nat{j < list_t_len slot}) (k:nat{k < list_t_len slot /\ j < k}) :
    Lemma (not_same_keys_at_j_k slot j k)
    [SMTPat (not_same_keys_at_j_k slot j k)]
    =
    g j k
  in
  ()
*)

let slots_t_inv (#t : Type0) (slots : slots_t t{length slots <= usize_max}) : Type0 =
  forall(i:nat{i < length slots}).
  {:pattern index slots i}
  slot_t_inv (length slots) i (index slots i)

type slots_t_inv_f (#t : Type0) (slots : slots_t t{length slots <= usize_max}) =
  (i:nat{i < length slots}) ->
  Lemma (slot_t_inv (length slots) i (index slots i))

let slots_t_inv_to_fun
  (#t : Type0) (slots : slots_t t{length slots <= usize_max /\ slots_t_inv slots}) :
  slots_t_inv_f slots =
  fun i -> ()

let slots_t_from_fun
  (#t : Type0) (slots : slots_t t{length slots <= usize_max})
  (f : slots_t_inv_f slots) :
  Lemma (slots_t_inv slots) =
  let f' (i:nat{i < length slots}) :
    Lemma (slot_t_inv (length slots) i (index slots i))
    [SMTPat (slot_t_inv (length slots) i (index slots i))]
    =
    f i
  in
  ()

/// Base invariant for the hashmap (the complete invariant can be temporarily
/// broken between the moment we inserted an element and the moment we resize)
let hash_map_t_base_inv (#t : Type0) (hm : hash_map_t t) : Type0 =
  let al = hash_map_t_v hm in
  // [num_entries] correctly tracks the number of entries in the table
  // Note that it gives us that the length of the slots array is <= usize_max
  hm.hash_map_num_entries = length al /\
  // Slots invariant
  slots_t_inv hm.hash_map_slots /\
  // The capacity must be > 0 (otherwise we can't resize, because we
  // multiply the capacity by two!)
  length hm.hash_map_slots > 0 /\
  // Load computation
  begin
  let capacity = length hm.hash_map_slots in
  let (dividend, divisor) = hm.hash_map_max_load_factor in
  0 < dividend /\ dividend < divisor /\
  hm.hash_map_max_load = (capacity * dividend) / divisor
  end

/// Invariant for the hashmap
let hash_map_t_inv (#t : Type0) (hm : hash_map_t t) : Type0 =
  // Base invariant
  hash_map_t_base_inv hm /\
  // The hash map is either: not overloaded, or we can't resize it
  (hm.hash_map_num_entries <= hm.hash_map_max_load
   || length hm.hash_map_slots * 2 > usize_max)

/// The following predicate links the hashmap to an associative list.
/// Note that it does not compute the representant: different (permuted)
/// lists can be used to represent the same hashmap!
let hash_map_t_is_al (#t : Type0) (hm : hash_map_t t) (al : assoc_list t) : Type0 =
  let hm_al = hash_map_t_v hm in
  assoc_list_equiv hm_al al

(*
/// The invariant we reveal to the user
let hash_map_t_inv_repr (#t : Type0) (hm : hash_map_t t) (al : assoc_list t) : Type0 =
  // The hash map invariant is satisfied
  hash_map_t_inv hm /\
  // And it can be seen as the given associative list
  hash_map_t_is_al hm al
*)

(*** Proofs *)
(**** allocate_slots *)

/// Auxiliary lemma
val slots_t_all_nil_inv_lem
  (#t : Type0) (slots : vec (list_t t){length slots <= usize_max}) :
  Lemma (requires (forall (i:nat{i < length slots}). index slots i == ListNil))
  (ensures (slots_t_inv slots))

#push-options "--fuel 1"
let slots_t_all_nil_inv_lem #t slots = ()
#pop-options

val slots_t_v_all_nil_is_empty_lem
  (#t : Type0) (slots : vec (list_t t)) :
  Lemma (requires (forall (i:nat{i < length slots}). index slots i == ListNil))
  (ensures (slots_t_v slots == []))

#push-options "--fuel 1"
let rec slots_t_v_all_nil_is_empty_lem #t slots =
 match slots with
 | [] -> ()
 | s :: slots' ->
   assert(forall (i:nat{i < length slots'}). index slots' i == index slots (i+1));
   slots_t_v_all_nil_is_empty_lem #t slots';
   assert(slots_t_v slots == list_t_v s @ slots_t_v slots');
   assert(slots_t_v slots == list_t_v s);
   assert(index slots 0 == ListNil)
#pop-options

/// [allocate_slots]
val hash_map_allocate_slots_fwd_lem
  (t : Type0) (slots : vec (list_t t)) (n : usize) :
  Lemma
  (requires (length slots + n <= usize_max))
  (ensures (
   match hash_map_allocate_slots_fwd t slots n with
   | Fail -> False
   | Return slots' ->
     length slots' = length slots + n /\
     // We leave the already allocated slots unchanged
     (forall (i:nat{i < length slots}). index slots' i == index slots i) /\
     // We allocate n additional empty slots
     (forall (i:nat{length slots <= i /\ i < length slots'}). index slots' i == ListNil)))
  (decreases (hash_map_allocate_slots_decreases t slots n))

#push-options "--fuel 1"
let rec hash_map_allocate_slots_fwd_lem t slots n =
  begin match n with
  | 0 -> ()
  | _ ->
    begin match vec_push_back (list_t t) slots ListNil with
    | Fail -> ()
    | Return slots1 ->
      begin match usize_sub n 1 with
      | Fail -> ()
      | Return i ->
        hash_map_allocate_slots_fwd_lem t slots1 i;
        begin match hash_map_allocate_slots_fwd t slots1 i with
        | Fail -> ()
        | Return slots2 ->
          assert(length slots1 = length slots + 1);
          assert(slots1 == slots @ [ListNil]); // Triggers patterns
          assert(index slots1 (length slots) == index [ListNil] 0); // Triggers patterns
          assert(index slots1 (length slots) == ListNil)
        end
      end
    end
  end
#pop-options

(**** new_with_capacity *)
/// Under proper conditions, [new_with_capacity] doesn't fail and returns an empty hash map.
val hash_map_new_with_capacity_fwd_lem
  (t : Type0) (capacity : usize)
  (max_load_dividend : usize) (max_load_divisor : usize) :
  Lemma
  (requires (
    0 < max_load_dividend /\
    max_load_dividend < max_load_divisor /\
    0 < capacity /\
    capacity * max_load_dividend < usize_max))
  (ensures (
    match hash_map_new_with_capacity_fwd t capacity max_load_dividend max_load_divisor with
    | Fail -> False
    | Return hm ->
      // The hash map has the specified capacity - we need to reveal this
      // otherwise the pre of [hash_map_t_find] is not satisfied.
      length hm.hash_map_slots = capacity /\
      // The hash map has 0 values
      hash_map_t_len hm = 0 /\
      // It contains no bindings
      (forall k. hash_map_t_find hm k == None) /\
      // We need this low-level property for the invariant
      (forall(i:nat{i < length hm.hash_map_slots}). index hm.hash_map_slots i == ListNil)))

#push-options "--z3rlimit 50 --fuel 1"
let hash_map_new_with_capacity_fwd_lem (t : Type0) (capacity : usize)
  (max_load_dividend : usize) (max_load_divisor : usize) =
  let v = vec_new (list_t t) in
  assert(length v = 0);
  hash_map_allocate_slots_fwd_lem t v capacity;
  begin match hash_map_allocate_slots_fwd t v capacity with
  | Fail -> assert(False)
  | Return v0 ->
    begin match usize_mul capacity max_load_dividend with
    | Fail -> assert(False)
    | Return i ->
      begin match usize_div i max_load_divisor with
      | Fail -> assert(False)
      | Return i0 ->
          let hm = Mkhash_map_t 0 (max_load_dividend, max_load_divisor) i0 v0 in
          slots_t_all_nil_inv_lem v0
      end
    end
  end
#pop-options

(**** new *)
/// [new] doesn't fail and returns an empty hash map
val hash_map_new_fwd_lem_fun (t : Type0) :
  Lemma
  (ensures (
    match hash_map_new_fwd t with
    | Fail -> False
    | Return hm ->
      // The hash map invariant is satisfied
      hash_map_t_inv hm /\
      // The hash map has 0 values
      hash_map_t_len hm = 0 /\
      // It contains no bindings
      (forall k. hash_map_t_find hm k == None)))

#push-options "--fuel 1"
let hash_map_new_fwd_lem_fun t =
  hash_map_new_with_capacity_fwd_lem t 32 4 5;
  match hash_map_new_with_capacity_fwd t 32 4 5 with
  | Fail -> ()
  | Return hm ->
    slots_t_v_all_nil_is_empty_lem hm.hash_map_slots
#pop-options

(**** clear_slots *)
/// [clear_slots] doesn't fail and simply clears the slots starting at index i
#push-options "--fuel 1"
let rec hash_map_clear_slots_fwd_back_lem
  (t : Type0) (slots : vec (list_t t)) (i : usize) :
  Lemma
  (ensures (
    match hash_map_clear_slots_fwd_back t slots i with
    | Fail -> False
    | Return slots' ->
      // The length is preserved
      length slots' == length slots /\
      // The slots before i are left unchanged
      (forall (j:nat{j < i /\ j < length slots}). index slots' j == index slots j) /\
      // The slots after i are set to ListNil
      (forall (j:nat{i <= j /\ j < length slots}). index slots' j == ListNil)))
  (decreases (hash_map_clear_slots_decreases t slots i))
  =
  let i0 = vec_len (list_t t) slots in
  let b = i < i0 in
  if b
  then
    begin match vec_index_mut_back (list_t t) slots i ListNil with
    | Fail -> ()
    | Return v ->
      begin match usize_add i 1 with
      | Fail -> ()
      | Return i1 ->
        hash_map_clear_slots_fwd_back_lem t v i1;
        begin match hash_map_clear_slots_fwd_back t v i1 with
        | Fail -> ()
        | Return slots1 ->
          assert(length slots1 == length slots);
          assert(forall (j:nat{i+1 <= j /\ j < length slots}). index slots1 j == ListNil);
          assert(index slots1 i == ListNil)
        end
      end
    end
  else ()
#pop-options

(**** clear *)
/// [clear] doesn't fail and turns the hash map into an empty map
val hash_map_clear_fwd_back_lem_fun
  (t : Type0) (self : hash_map_t t) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_clear_fwd_back t self with
    | Fail -> False
    | Return hm ->
      // The hash map invariant is satisfied
      hash_map_t_inv hm /\
      // The hash map has 0 values
      hash_map_t_len hm = 0 /\
      // It contains no bindings
      (forall k. hash_map_t_find hm k == None)))

// Being lazy: fuel 1 helps a lot...
#push-options "--fuel 1"
let hash_map_clear_fwd_back_lem_fun t self =
  let p = self.hash_map_max_load_factor in
  let i = self.hash_map_max_load in
  let v = self.hash_map_slots in
  hash_map_clear_slots_fwd_back_lem t v 0;
  begin match hash_map_clear_slots_fwd_back t v 0 with
  | Fail -> ()
  | Return slots1 ->
    slots_t_v_all_nil_is_empty_lem slots1;
    let hm1 = Mkhash_map_t 0 p i slots1 in
    assert(hash_map_t_base_inv hm1);
    assert(hash_map_t_inv hm1);
    assert(hash_map_t_is_al hm1 [])
  end
#pop-options

(**** len *)

/// [len]: we link it to a non-failing function.
/// Rk.: we might want to make an analysis to not use an error monad to translate
/// functions which statically can't fail.
val hash_map_len_fwd_lem (t : Type0) (self : hash_map_t t) :
  Lemma (
    match hash_map_len_fwd t self with
    | Fail -> False
    | Return l -> l = hash_map_t_len self)

let hash_map_len_fwd_lem t self = ()


(**** insert_in_list *)

/// [insert_in_list_fwd]: returns true iff the key is not in the list (functional version)
val hash_map_insert_in_list_fwd_lem
  (t : Type0) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (ensures (
    match hash_map_insert_in_list_fwd t key value ls with
    | Fail -> False
    | Return b ->
      b <==> (slot_t_find key ls == None)))
  (decreases (hash_map_insert_in_list_decreases t key value ls))

#push-options "--fuel 1"
let rec hash_map_insert_in_list_fwd_lem t key value ls =
  begin match ls with
  | ListCons ckey cvalue ls0 ->
    let b = ckey = key in
    if b
    then ()
    else
      begin
      hash_map_insert_in_list_fwd_lem t key value ls0;
      match hash_map_insert_in_list_fwd t key value ls0 with
      | Fail -> ()
      | Return b0 -> ()
      end
  | ListNil ->
    assert(list_t_v ls == []);
    assert_norm(find (same_key #t key) [] == None)
  end
#pop-options

(*
/// [insert_in_list]
// TODO: remove
val hash_map_insert_in_list_back_lem
  (t : Type0) (len : usize{len > 0}) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (requires (slot_t_inv len (hash_mod_key key len) ls))
  (ensures (
    match hash_map_insert_in_list_back t key value ls with
    | Fail -> False
    | Return ls' ->
      // The invariant is preserved
      slot_t_inv len (hash_mod_key key len) ls' /\
      // [key] maps to [value]
      slot_t_find key ls' == Some value /\
      // The other bindings are preserved
      (forall k'. k' <> key ==> slot_t_find k' ls' == slot_t_find k' ls) /\
      // The length is incremented, iff we inserted a new key
      (match slot_t_find key ls with
       | None ->
         list_t_v ls' == list_t_v ls @ [(key,value)] /\
         list_t_len ls' = list_t_len ls + 1
       | Some _ ->
         list_t_v ls' == find_update (same_key key) (list_t_v ls) (key,value) /\
         list_t_len ls' = list_t_len ls)))
  (decreases (hash_map_insert_in_list_decreases t key value ls))

// I suffered a bit below, but as usual, for the wrong reasons: quantifiers in F*
// are really too painful to work with...
#push-options "--z3rlimit 200 --fuel 1"
let rec hash_map_insert_in_list_back_lem t len key value ls =
  let h = hash_mod_key key len in
  begin match ls with
  | ListCons ckey cvalue ls0 ->
    let b = ckey = key in
    if b
    then
      begin
      let ls1 = ListCons ckey value ls0 in
      let ls_hash_key_lem, ls_not_same_keys_lem = slot_t_inv_to_funs len h ls in
      let ls1_hash_key_lem : slot_t_inv_hash_key_f len h ls1 =
        fun j -> if j = 0 then () else ls_hash_key_lem j
      in
      let ls1_not_same_keys_lem : slot_t_inv_not_same_keys_f h ls1 =
        fun j k -> ls_not_same_keys_lem j k
      in
      slot_t_inv_from_funs_lem len h ls1 ls1_hash_key_lem ls1_not_same_keys_lem;
      assert(slot_t_inv len (hash_mod_key key len) ls1)
      end
    else
      begin
      let ls_hash_key_lem, ls_not_same_keys_lem = slot_t_inv_to_funs len h ls in
      let ls0_hash_key_lem : slot_t_inv_hash_key_f len h ls0 =
        fun j -> ls_hash_key_lem (j + 1)
      in
      let ls0_not_same_keys_lem : slot_t_inv_not_same_keys_f h ls0 =
        fun j k -> ls_not_same_keys_lem (j + 1) (k + 1)
      in
      slot_t_inv_from_funs_lem len h ls0 ls0_hash_key_lem ls0_not_same_keys_lem;
      assert(slot_t_inv len (hash_mod_key key len) ls0);
      hash_map_insert_in_list_back_lem t len key value ls0;
      match hash_map_insert_in_list_back t key value ls0 with
      | Fail -> ()
      | Return l ->
        let ls1 = ListCons ckey cvalue l in
        let l_hash_key_lem, l_not_same_keys_lem = slot_t_inv_to_funs len h l in
        let ls1_hash_key_lem : slot_t_inv_hash_key_f len h ls1 =
          fun j ->
          if j = 0 then
            begin
            ls_hash_key_lem 0;
            assert(hash_mod_key (fst (list_t_index ls1 j)) len = h)
            end
          else l_hash_key_lem (j - 1)
        in
        (* Disjunction on whether we added an element or not *)
        begin match slot_t_find key ls0 with
        | None ->
          (* We added an element *)        
          assert(list_t_v l == list_t_v ls0 @ [(key,value)]);
  //        assert(list_t_v ls1 == list_t_v ls @ [(key,value)]);
          let ls1_not_same_keys_lem : slot_t_inv_not_same_keys_f h ls1 =
            fun j k ->
            if 0 < j then
              l_not_same_keys_lem (j-1) (k-1)
            else //if k < list_t_len ls then
              begin
//              assert_norm(length [(key,value)] = 1);
              assert(list_t_index ls1 j == (ckey, cvalue));
              assert(list_t_v ls1 == (ckey, cvalue) :: list_t_v l);
              assert(list_t_index ls1 k == list_t_index l (k-1));
//              index_append_lem (list_t_v ls0) [(key,value)] (j-1);
              index_append_lem (list_t_v ls0) [(key,value)] (k-1);
              if k < list_t_len l then
                begin
                assert(list_t_index ls1 k == list_t_index ls0 (k-1));
                admit()
                end
              else
                admit()
              end
          in
          slot_t_inv_from_funs_lem len h ls1 ls1_hash_key_lem ls1_not_same_keys_lem
        | _ ->
          (* We simply updated a binding *)
          admit()
        end
      end
  | ListNil ->
    let ls0 = ListCons key value ListNil in
    assert_norm(list_t_len ls0 == 1);
    let ls0_hash_key_lem : slot_t_inv_hash_key_f len h ls0 =
      fun j -> ()
    in
    let ls0_not_same_keys_lem : slot_t_inv_not_same_keys_f h ls0 =
      fun j k -> ()
    in
    slot_t_inv_from_funs_lem len h ls0 ls0_hash_key_lem ls0_not_same_keys_lem
  end
#pop-options
*)

(**** insert_no_resize *)

(*val hash_map_insert_no_resize_fwd_back_lem
  (t : Type0) (self : hash_map_t t) (key : usize) (value : t) :
  Lemma (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_insert_no_resize_fwd_back t self key value with
    | Fail ->
      (* If we fail, it is necessarily because:
       * - we tried to add a new *key* (there was no binding for the key)
       * - the [num_entries] counter is already saturaed *)
      hash_map_t_find self key == None /\
      hash_map_t_len self = usize_max
    | Return hm ->
      // The invariant is preserved
      hash_map_t_inv hm /\
      // [key] maps to [value]
      hash_map_t_find hm key == Some value /\
      // The other bindings are preserved
      (forall k'. k' <> key ==> hash_map_t_find hm k' == hash_map_t_find self k') /\
      // The length is incremented, iff we inserted a new key
      (match hash_map_t_find self key with
       | None -> hash_map_t_len hm = hash_map_t_len hm + 1
       | Some _ -> hash_map_t_len hm = hash_map_t_len hm)))

let hash_map_insert_no_resize_fwd_back_lem t self key value =
  begin match hash_key_fwd key with
  | Fail -> ()
  | Return i ->
    let i0 = self.hash_map_num_entries in
    let p = self.hash_map_max_load_factor in
    let i1 = self.hash_map_max_load in
    let v = self.hash_map_slots in
    let i2 = vec_len (list_t t) v in
    begin match usize_rem i i2 with
    | Fail -> ()
    | Return hash_mod ->
      begin match vec_index_mut_fwd (list_t t) v hash_mod with
      | Fail -> ()
      | Return l ->
        begin
        hash_map_insert_in_list_fwd_lem t key value l;
        match hash_map_insert_in_list_fwd t key value l with
        | Fail -> ()
        | Return b ->
          if b
          then
            begin match usize_add i0 1 with
            | Fail ->
              assert(slot_t_find key l == None);
              assert(hash_map_t_len self = usize_max);
              ()
            | Return i3 ->
              assert(l == index v hash_mod);
              slots_t_inv_to_fun v hash_mod;
              assert(slot_t_inv hash_mod (index v hash_mod));
              assert(slot_t_inv (hash_key key) l);
              hash_map_insert_in_list_back_lem t key value l;
              begin match hash_map_insert_in_list_back t key value l with
              | Fail -> admit()
              | Return l0 ->
                begin match vec_index_mut_back (list_t t) v hash_mod l0 with
                | Fail -> admit()
                | Return v0 ->
                  let self0 = Mkhash_map_t i3 p i1 v0 in admit() //Return self0
                end
              end
            end
          else
            begin match hash_map_insert_in_list_back t key value l with
            | Fail -> admit()
            | Return l0 ->
              begin match vec_index_mut_back (list_t t) v hash_mod l0 with
              | Fail -> admit()
              | Return v0 ->
                let self0 = Mkhash_map_t i0 p i1 v0 in admit() //Return self0
              end
            end
        end
      end
    end
  end*)

/// The proofs about [insert_in_list] backward are easier to do in several steps:
/// extrinsic proofs to the rescue!
/// Rk.: those proofs actually caused a lot of trouble because:
/// - F* is extremely bad at reasoning with quantifiers, which is made worse by
///   the fact we are blind when making proofs. This forced us to be extremely
///   careful about the way we wrote our specs/invariants (by writing "functional"
///   specs and invariants, mostly, so as not to manipulate quantifiers)
/// - we can't easily prove intermediate results which require a recursive proofs
///   inside of other proofs, meaning that whenever we need such a result we need
///   to write an intermediate lemma, which is extremely cumbersome.
/// Note that in a theorem prover with tactics, most of the below proof would have
/// been extremely straightforward. In particular, we wouldn't have needed to think
/// much about the invariants, nor to cut the proofs into very small, modular lemmas.

/// [insert_in_list]: if the key is not in the map, appends a new bindings (functional version)
val hash_map_insert_in_list_back_lem_append_fun
  (t : Type0) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (requires (
    find (same_key key) (list_t_v ls) == None))
  (ensures (
    match hash_map_insert_in_list_back t key value ls with
    | Fail -> False
    | Return ls' ->
      list_t_v ls' == list_t_v ls @ [(key,value)]))
  (decreases (hash_map_insert_in_list_decreases t key value ls))

#push-options "--fuel 1"
let rec hash_map_insert_in_list_back_lem_append_fun t key value ls =
  begin match ls with
  | ListCons ckey cvalue ls0 ->
    let b = ckey = key in
    if b
    then ()
    else
      begin
      hash_map_insert_in_list_back_lem_append_fun t key value ls0;
      match hash_map_insert_in_list_back t key value ls0 with
      | Fail -> ()
      | Return l -> ()
      end
  | ListNil -> ()
  end
#pop-options

/// [insert_in_list]: if the key is in the map, we update the binding (functional version)
val hash_map_insert_in_list_back_lem_update_fun
  (t : Type0) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (requires (
    Some? (find (same_key key) (list_t_v ls))))
  (ensures (
    match hash_map_insert_in_list_back t key value ls with
    | Fail -> False
    | Return ls' ->
      list_t_v ls' == find_update (same_key key) (list_t_v ls) (key,value)))
  (decreases (hash_map_insert_in_list_decreases t key value ls))

#push-options "--fuel 1"
let rec hash_map_insert_in_list_back_lem_update_fun t key value ls =
  begin match ls with
  | ListCons ckey cvalue ls0 ->
    let b = ckey = key in
    if b
    then ()
    else
      begin
      hash_map_insert_in_list_back_lem_update_fun t key value ls0;
      match hash_map_insert_in_list_back t key value ls0 with
      | Fail -> ()
      | Return l -> ()
      end
  | ListNil -> ()
  end
#pop-options

/// Auxiliary lemmas
/// Reasoning about the result of [insert_in_list], converted to a "regular" list.
/// Note that in F* we can't have recursive proofs inside of other proofs, contrary
/// to Coq, which makes it a bit cumbersome to prove auxiliary results like the
/// following ones...

val slot_t_v_for_all_binding_neq_append_lem
  (t : Type0) (key : usize) (value : t) (ls : list (binding t)) (b : binding t) :
  Lemma
  (requires (
    fst b <> key /\
    for_all (binding_neq b) ls /\
    slot_t_v_find key ls == None))
  (ensures (
    for_all (binding_neq b) (ls @ [(key,value)])))

#push-options "--fuel 1"
let rec slot_t_v_for_all_binding_neq_append_lem t key value ls b =
  match ls with
  | [] -> ()
  | (ck, cv) :: cls ->
    slot_t_v_for_all_binding_neq_append_lem t key value cls b
#pop-options

val slot_t_v_inv_not_find_append_end_inv_lem
  (t : Type0) (len : usize{len > 0}) (key : usize) (value : t) (ls : list (binding t)) :
  Lemma
  (requires (
    slot_t_v_inv len (hash_mod_key key len) ls /\
    slot_t_v_find key ls == None))
  (ensures (
    let ls' = ls @ [(key,value)] in
    slot_t_v_inv len (hash_mod_key key len) ls' /\
    (slot_t_v_find key ls' == Some value) /\
    (forall k'. k' <> key ==> slot_t_v_find k' ls' == slot_t_v_find k' ls)))

#push-options "--fuel 1"
let rec slot_t_v_inv_not_find_append_end_inv_lem t len key value ls =
  match ls with
  | [] -> ()
  | (ck, cv) :: cls ->
    slot_t_v_inv_not_find_append_end_inv_lem t len key value cls;
    let h = hash_mod_key key len in
    let ls' = ls @ [(key,value)] in
    assert(for_all (same_hash_mod_key len h) ls');
    slot_t_v_for_all_binding_neq_append_lem t key value cls (ck, cv);
    assert(pairwise_rel binding_neq ls');
    assert(slot_t_v_inv len h ls')
#pop-options

/// [insert_in_list]: if the key is not in the map, appends a new bindings (quantifiers)
val hash_map_insert_in_list_back_lem_append
  (t : Type0) (len : usize{len > 0}) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (requires (
    slot_t_inv len (hash_mod_key key len) ls /\
    find (same_key key) (list_t_v ls) == None))
  (ensures (
    match hash_map_insert_in_list_back t key value ls with
    | Fail -> False
    | Return ls' ->
      list_t_v ls' == list_t_v ls @ [(key,value)] /\
      // The invariant is preserved
      slot_t_inv len (hash_mod_key key len) ls' /\
      // [key] maps to [value]
      slot_t_find key ls' == Some value /\
      // The other bindings are preserved
      (forall k'. k' <> key ==> slot_t_find k' ls' == slot_t_find k' ls)))

let hash_map_insert_in_list_back_lem_append t len key value ls =
  hash_map_insert_in_list_back_lem_append_fun t key value ls;
  match hash_map_insert_in_list_back t key value ls with
  | Fail -> ()
  | Return ls' ->
    assert(list_t_v ls' == list_t_v ls @ [(key,value)]);
    slot_t_v_inv_not_find_append_end_inv_lem t len key value (list_t_v ls)

(*
(**** insert_no_resize *)

/// Same as for [insert_in_list]: we do the proofs in several, modular steps.
/// The strategy is to study the two disjoint cases:
/// - the key is already in the map (we update the binding)
/// - the key is not in the map (we add a binding)
///
/// We gradually prove that the resulting map, in the two cases, can be seen
/// as the result of:
/// - filtering the bindings for the key we want to insert
/// - pushing the new binding at the front
///
/// We then prove a less "functional" variant of the result, which states that,
/// after the insertion:
/// - [key] maps to [value]
/// - forall key' <> key, the binding is unchanged
/// 
/// This way, we have a consistent, high-level description of the insertion.
///
/// Rk.: with multimaps the high-level spec would be even simpler: we would push
/// an element to the front of the list.

/// [insert_no_resize]: if the key is in the map, we succeed and update the binding.
val hash_map_insert_no_resize_fwd_back_lem_update
  (t : Type0) (self : hash_map_t t) (key : usize) (value : t) :
  Lemma
  (requires (
    hash_map_t_inv self /\
    // The key is in the map
    Some? (find (same_key key) (hash_map_t_v self))))
  (ensures (
    match hash_map_insert_no_resize_fwd_back t self key value with
    | Fail -> False
    | Return hm ->
      // The invariant is preserved
      hash_map_t_inv hm /\
      // The map has been updated
      hash_map_t_v hm == find_update (same_key key) (hash_map_t_v self) (key,value)))

let hash_map_insert_no_resize_fwd_back_lem_update t self key value =
  begin match hash_key_fwd key with
  | Fail -> ()
  | Return i ->
    let i0 = self.hash_map_num_entries in
    let p = self.hash_map_max_load_factor in
    let i1 = self.hash_map_max_load in
    let v = self.hash_map_slots in
    let i2 = vec_len (list_t t) v in
    begin match usize_rem i i2 with
    | Fail -> ()
    | Return hash_mod ->
      begin match vec_index_mut_fwd (list_t t) v hash_mod with
      | Fail -> ()
      | Return l ->
        // The key must be in the slot - TODO: update invariant
        assume(Some? (find (same_key key) (list_t_v l)));
        hash_map_insert_in_list_fwd_lem t key value l;
        begin match hash_map_insert_in_list_fwd t key value l with
        | Fail -> ()
        | Return b ->
          assert(not b);
          if b then assert(False)
          else
            begin
            hash_map_insert_in_list_back_lem_update t key value l;
            match hash_map_insert_in_list_back t key value l with
            | Fail -> ()
            | Return l0 ->
              begin
              match vec_index_mut_back (list_t t) v hash_mod l0 with
              | Fail -> ()
              | Return v0 ->
                let hm1 = Mkhash_map_t i0 p i1 v0 in
                assume(hash_map_t_inv hm1);
                assume(hash_map_t_v hm1 == find_update (same_key key) (hash_map_t_v self) (key,value))
              end
            end
        end
      end
    end
  end


/// [insert_in_list]: inserting a binding is equivalent to:
/// - filtering the list
/// - pushing the binding to the front

