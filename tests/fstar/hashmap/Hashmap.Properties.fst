(** Properties about the hashmap *)
module Hashmap.Properties
open Primitives
open FStar.List.Tot
open FStar.Mul
open Hashmap.Types
open Hashmap.Clauses
open Hashmap.Funs

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

let _align_fsti = ()

/// The proofs:
/// ===========
/// 
/// The proof strategy is to do exactly as with Low* proofs (we initially tried to
/// prove more properties in one go, but it was a mistake):
/// - prove that, under some preconditions, the low-level functions translated
///   from Rust refine some higher-level functions
/// - do functional proofs about those high-level functions to prove interesting
///   properties about the hash map operations, and invariant preservation
/// - combine everything
///
/// The fact that we work in a pure setting allows us to be more modular than when
/// working with effects. For instance we can do a case disjunction (see the proofs
/// for insert, which study the cases where the key is already/not in the hash map
/// in separate proofs - we had initially tried to do them in one step: it is doable
/// but requires some work, and the F* response time quickly becomes annoying while
/// making progress, so we split them). We can also easily prove a refinement lemma,
/// study the model, *then* combine those to also prove that the low-level function
/// preserves the invariants, rather than do everything at once as is usually the
/// case when doing intrinsic proofs with effects (I remember that having to prove
/// invariants in one go *and* a refinement step, even small, can be extremely
/// difficult in Low*).


(*** Utilities *)

/// We need many small helpers and lemmas, mostly about lists (and the ones we list
/// here are not in the standard F* library).

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

val index_map_lem (#a #b: Type0) (f : a -> Tot b) (ls : list a)
  (i : nat{i < length ls}) :
  Lemma (
    index (map f ls) i == f (index ls i))
  [SMTPat (index (map f ls) i)]

#push-options "--fuel 1"
let rec index_map_lem #a #b f ls i =
  match ls with
  | [] -> ()
  | x :: ls' ->
    if i = 0 then ()
    else index_map_lem f ls' (i-1)
#pop-options

val for_all_append (#a : Type0) (f : a -> Tot bool) (ls0 ls1 : list a) :
  Lemma (for_all f (ls0 @ ls1) = (for_all f ls0 && for_all f ls1))

#push-options "--fuel 1"
let rec for_all_append #a f ls0 ls1 =
  match ls0 with
  | [] -> ()
  | x :: ls0' ->
    for_all_append f ls0' ls1
#pop-options

/// Filter a list, stopping after we removed one element
val filter_one (#a : Type) (f : a -> bool) (ls : list a) : list a

let rec filter_one #a f ls =
  match ls with
  | [] -> []
  | x :: ls' -> if f x then x :: filter_one f ls' else ls'

val find_append (#a : Type) (f : a -> bool) (ls0 ls1 : list a) :
  Lemma (
    find f (ls0 @ ls1) ==
    begin match find f ls0 with
    | Some x -> Some x
    | None -> find f ls1
    end)

#push-options "--fuel 1"
let rec find_append #a f ls0 ls1 =
  match ls0 with
  | [] -> ()
  | x :: ls0' ->
    if f x then
    begin
      assert(ls0 @ ls1 == x :: (ls0' @ ls1));
      assert(find f (ls0 @ ls1) == find f (x :: (ls0' @ ls1)));
      // Why do I have to do this?! Is it because of subtyping??
      assert(
        match find f (ls0 @ ls1) with
        | Some x' -> x' == x
        | None -> False)
    end
    else find_append f ls0' ls1
#pop-options

val length_flatten_update :
     #a:Type
  -> ls:list (list a)
  -> i:nat{i < length ls}
  -> x:list a ->
  Lemma (
    // We want this property:
    // ```
    // length (flatten (list_update ls i x)) =
    //   length (flatten ls) - length (index ls i) + length x
    // ```
    length (flatten (list_update ls i x)) + length (index ls i) =
    length (flatten ls) + length x)

#push-options "--fuel 1"
let rec length_flatten_update #a ls i x =
  match ls with
  | x' :: ls' ->
    assert(flatten ls == x' @ flatten ls'); // Triggers patterns
    assert(length (flatten ls) == length x' + length (flatten ls'));
    if i = 0 then
      begin
      let ls1 = x :: ls' in
      assert(list_update ls i x == ls1);
      assert(flatten ls1 == x @ flatten ls'); // Triggers patterns
      assert(length (flatten ls1) == length x + length (flatten ls'));
      ()
      end
    else
      begin
      length_flatten_update ls' (i-1) x;
      let ls1 = x' :: list_update ls' (i-1) x in
      assert(flatten ls1 == x' @ flatten (list_update ls' (i-1) x)) // Triggers patterns
      end
#pop-options

val length_flatten_index :
     #a:Type
  -> ls:list (list a)
  -> i:nat{i < length ls} ->
  Lemma (
    length (flatten ls) >= length (index ls i))

#push-options "--fuel 1"
let rec length_flatten_index #a ls i =
  match ls with
  | x' :: ls' ->
    assert(flatten ls == x' @ flatten ls'); // Triggers patterns
    assert(length (flatten ls) == length x' + length (flatten ls'));
    if i = 0 then ()
    else length_flatten_index ls' (i-1)
#pop-options

val forall_index_equiv_list_for_all
  (#a : Type) (pred : a -> Tot bool) (ls : list a) :
  Lemma ((forall (i:nat{i < length ls}). pred (index ls i)) <==> for_all pred ls)

#push-options "--fuel 1"
let rec forall_index_equiv_list_for_all pred ls =
  match ls with
  | [] -> ()
  | x :: ls' ->
    assert(forall (i:nat{i < length ls'}). index ls' i == index ls (i+1));
    assert(forall (i:nat{0 < i /\ i < length ls}). index ls i == index ls' (i-1));
    assert(index ls 0 == x);
    forall_index_equiv_list_for_all pred ls'
#pop-options

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

val pairwise_rel : #a:Type -> pred:(a -> a -> Tot bool) -> ls:list a -> Tot bool
let rec pairwise_rel #a pred ls =
  match ls with
  | [] -> true
  | x :: ls' ->
    for_all (pred x) ls' && pairwise_rel pred ls' 

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

(*** Lemmas about Primitives *)
/// TODO: move those lemmas

// TODO: rename to 'insert'?
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

val map_list_update_lem
  (#a #b: Type0) (f : a -> Tot b)
  (ls : list a) (i : nat{i < length ls}) (x : a) :
  Lemma (list_update (map f ls) i (f x) == map f (list_update ls i x))
  [SMTPat (list_update (map f ls) i (f x))]

#push-options "--fuel 1"
let rec map_list_update_lem #a #b f ls i x =
  match ls with
  | x' :: ls' ->
    if i = 0 then ()
    else map_list_update_lem f ls' (i-1) x
#pop-options

(*** Invariants, models *)

(**** Internals *)
/// The following invariants, models, representation functions... are mostly
/// for the purpose of the proofs.

let is_pos_usize (n : nat) : Type0 = 0 < n /\ n <= usize_max
type pos_usize = x:usize{x > 0}

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

type slot_s (t : Type0) = list (binding t)
type slots_s (t : Type0) = list (slot_s t)

type slot_t (t : Type0) = list_t t
let slot_t_v #t = list_t_v #t

/// Representation function for the slots.
let slots_t_v (#t : Type0) (slots : slots_t t) : slots_s t =
  map slot_t_v slots

/// Representation function for the slots, seen as an associative list.
let slots_t_al_v (#t : Type0) (slots : slots_t t) : assoc_list t =
  flatten (map list_t_v slots)

/// High-level type for the hash-map, seen as a list of associative lists (one
/// list per slot). This is the representation we use most, internally. Note that
/// we later introduce a [map_s] representation, which is the one used in the
/// lemmas shown to the user.
type hash_map_s t = list (slot_s t)

// TODO: why not always have the condition on the length?
// 'nes': "non-empty slots"
type hash_map_s_nes (t : Type0) : Type0 =
  hm:hash_map_s t{is_pos_usize (length hm)}

/// Representation function for [hash_map_t] as a list of slots
let hash_map_t_v (#t : Type0) (hm : hash_map_t t) : hash_map_s t =
  map list_t_v hm.hash_map_slots

/// Representation function for [hash_map_t] as an associative list
let hash_map_t_al_v (#t : Type0) (hm : hash_map_t t) : assoc_list t =
  flatten (hash_map_t_v hm)

// 'nes': "non-empty slots"
type hash_map_t_nes (t : Type0) : Type0 =
  hm:hash_map_t t{is_pos_usize (length hm.hash_map_slots)}

let hash_key (k : key) : hash =
  Return?.v (hash_key_fwd k)

let hash_mod_key (k : key) (len : usize{len > 0}) : hash =
  (hash_key k) % len

let not_same_key (#t : Type0) (k : key) (b : binding t) : bool = fst b <> k
let same_key (#t : Type0) (k : key) (b : binding t) : bool = fst b = k

// We take a [nat] instead of a [hash] on purpose
let same_hash_mod_key (#t : Type0) (len : usize{len > 0}) (h : nat) (b : binding t) : bool =
  hash_mod_key (fst b) len = h

let binding_neq (#t : Type0) (b0 b1 : binding t) : bool = fst b0 <> fst b1

let hash_map_t_len_s (#t : Type0) (hm : hash_map_t t) : nat =
  hm.hash_map_num_entries

let assoc_list_find (#t : Type0) (k : key) (slot : assoc_list t) : option t =
  match find (same_key k) slot with
  | None -> None
  | Some (_, v) -> Some v

let slot_s_find (#t : Type0) (k : key) (slot : list (binding t)) : option t =
  assoc_list_find k slot

let slot_t_find_s (#t : Type0) (k : key) (slot : list_t t) : option t =
  slot_s_find k (slot_t_v slot)

// This is a simpler version of the "find" function, which captures the essence
// of what happens and operates on [hash_map_s].
let hash_map_s_find
  (#t : Type0) (hm : hash_map_s_nes t)
  (k : key) : option t =
  let i = hash_mod_key k (length hm) in
  let slot = index hm i in
  slot_s_find k slot

let hash_map_s_len
  (#t : Type0) (hm : hash_map_s t) :
  nat =
  length (flatten hm)

// Same as above, but operates on [hash_map_t]
// Note that we don't reuse the above function on purpose: converting to a
// [hash_map_s] then looking up an element is not the same as what we
// wrote below.
let hash_map_t_find_s
  (#t : Type0) (hm : hash_map_t t{length hm.hash_map_slots > 0}) (k : key) : option t =
  let slots = hm.hash_map_slots in
  let i = hash_mod_key k (length slots) in
  let slot = index slots i in
  slot_t_find_s k slot

/// Invariants for the slots

let slot_s_inv
  (#t : Type0) (len : usize{len > 0}) (i : usize) (slot : list (binding t)) : bool =
  // All the bindings are in the proper slot
  for_all (same_hash_mod_key len i) slot &&
  // All the keys are pairwise distinct
  pairwise_rel binding_neq slot

let slot_t_inv (#t : Type0) (len : usize{len > 0}) (i : usize) (slot : list_t t) : bool =
  slot_s_inv len i (slot_t_v slot)

let slots_s_inv (#t : Type0) (slots : slots_s t{length slots <= usize_max}) : Type0 =
  forall(i:nat{i < length slots}).
  {:pattern index slots i}
  slot_s_inv (length slots) i (index slots i)

// At some point we tried to rewrite this in terms of [slots_s_inv]. However it
// made a lot of proofs fail because those proofs relied on the [index_map_lem]
// pattern. We tried writing others lemmas with patterns (like [slots_s_inv]
// implies [slots_t_inv]) but it didn't succeed, so we keep things as they are.
let slots_t_inv (#t : Type0) (slots : slots_t t{length slots <= usize_max}) : Type0 =
  forall(i:nat{i < length slots}).
  {:pattern index slots i}
  slot_t_inv (length slots) i (index slots i)

let hash_map_s_inv (#t : Type0) (hm : hash_map_s t) : Type0 =
  length hm <= usize_max /\
  length hm > 0 /\
  slots_s_inv hm

/// Base invariant for the hashmap (the complete invariant can be temporarily
/// broken between the moment we inserted an element and the moment we resize)
let hash_map_t_base_inv (#t : Type0) (hm : hash_map_t t) : Type0 =
  let al = hash_map_t_al_v hm in
  // [num_entries] correctly tracks the number of entries in the table
  // Note that it gives us that the length of the slots array is <= usize_max:
  // [> length <= usize_max
  // (because hash_map_num_entries has type `usize`)
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
  capacity * dividend >= divisor /\
  hm.hash_map_max_load = (capacity * dividend) / divisor
  end

/// We often need to frame some values
let hash_map_t_same_params (#t : Type0) (hm0 hm1 : hash_map_t t) : Type0 =
  length hm0.hash_map_slots = length hm1.hash_map_slots /\
  hm0.hash_map_max_load = hm1.hash_map_max_load /\
  hm0.hash_map_max_load_factor = hm1.hash_map_max_load_factor

/// The following invariants, etc. are meant to be revealed to the user through
/// the .fsti.

/// Invariant for the hashmap
let hash_map_t_inv (#t : Type0) (hm : hash_map_t t) : Type0 =
  // Base invariant
  hash_map_t_base_inv hm /\
  // The hash map is either: not overloaded, or we can't resize it
  begin
  let (dividend, divisor) = hm.hash_map_max_load_factor in
  hm.hash_map_num_entries <= hm.hash_map_max_load
  || length hm.hash_map_slots * 2 * dividend > usize_max
  end

(*** .fsti *)
/// We reveal slightly different version of the above functions to the user

let len_s (#t : Type0) (hm : hash_map_t t) : nat = hash_map_t_len_s hm

/// This version doesn't take any precondition (contrary to [hash_map_t_find_s])
let find_s (#t : Type0) (hm : hash_map_t t) (k : key) : option t =
  if length hm.hash_map_slots = 0 then None
  else hash_map_t_find_s hm k

(*** Overloading *)

let hash_map_not_overloaded_lem #t hm = ()

(*** allocate_slots *)

/// Auxiliary lemma
val slots_t_all_nil_inv_lem
  (#t : Type0) (slots : vec (list_t t){length slots <= usize_max}) :
  Lemma (requires (forall (i:nat{i < length slots}). index slots i == ListNil))
  (ensures (slots_t_inv slots))

#push-options "--fuel 1"
let slots_t_all_nil_inv_lem #t slots = ()
#pop-options

val slots_t_al_v_all_nil_is_empty_lem
  (#t : Type0) (slots : vec (list_t t)) :
  Lemma (requires (forall (i:nat{i < length slots}). index slots i == ListNil))
  (ensures (slots_t_al_v slots == []))

#push-options "--fuel 1"
let rec slots_t_al_v_all_nil_is_empty_lem #t slots =
 match slots with
 | [] -> ()
 | s :: slots' ->
   assert(forall (i:nat{i < length slots'}). index slots' i == index slots (i+1));
   slots_t_al_v_all_nil_is_empty_lem #t slots';
   assert(slots_t_al_v slots == list_t_v s @ slots_t_al_v slots');
   assert(slots_t_al_v slots == list_t_v s);
   assert(index slots 0 == ListNil)
#pop-options

/// [allocate_slots]
val hash_map_allocate_slots_fwd_lem
  (t : Type0) (slots : vec (list_t t)) (n : usize) :
  Lemma
  (requires (length slots + n <= usize_max))
  (ensures (
   match hash_map_allocate_slots_fwd t slots n with
   | Fail _ -> False
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
    | Fail _ -> ()
    | Return slots1 ->
      begin match usize_sub n 1 with
      | Fail _ -> ()
      | Return i ->
        hash_map_allocate_slots_fwd_lem t slots1 i;
        begin match hash_map_allocate_slots_fwd t slots1 i with
        | Fail _ -> ()
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

(*** new_with_capacity *)
/// Under proper conditions, [new_with_capacity] doesn't fail and returns an empty hash map.
val hash_map_new_with_capacity_fwd_lem
  (t : Type0) (capacity : usize)
  (max_load_dividend : usize) (max_load_divisor : usize) :
  Lemma
  (requires (
    0 < max_load_dividend /\
    max_load_dividend < max_load_divisor /\
    0 < capacity /\
    capacity * max_load_dividend >= max_load_divisor /\
    capacity * max_load_dividend <= usize_max))
  (ensures (
    match hash_map_new_with_capacity_fwd t capacity max_load_dividend max_load_divisor with
    | Fail _ -> False
    | Return hm ->
      // The hash map invariant is satisfied
      hash_map_t_inv hm /\
      // The parameters are correct
      hm.hash_map_max_load_factor = (max_load_dividend, max_load_divisor) /\
      hm.hash_map_max_load = (capacity * max_load_dividend) / max_load_divisor /\
      // The hash map has the specified capacity - we need to reveal this
      // otherwise the pre of [hash_map_t_find_s] is not satisfied.
      length hm.hash_map_slots = capacity /\
      // The hash map has 0 values
      hash_map_t_len_s hm = 0 /\
      // It contains no bindings
      (forall k. hash_map_t_find_s hm k == None) /\
      // We need this low-level property for the invariant
      (forall(i:nat{i < length hm.hash_map_slots}). index hm.hash_map_slots i == ListNil)))

#push-options "--z3rlimit 50 --fuel 1"
let hash_map_new_with_capacity_fwd_lem (t : Type0) (capacity : usize)
  (max_load_dividend : usize) (max_load_divisor : usize) =
  let v = vec_new (list_t t) in
  assert(length v = 0);
  hash_map_allocate_slots_fwd_lem t v capacity;
  begin match hash_map_allocate_slots_fwd t v capacity with
  | Fail _ -> assert(False)
  | Return v0 ->
    begin match usize_mul capacity max_load_dividend with
    | Fail _ -> assert(False)
    | Return i ->
      begin match usize_div i max_load_divisor with
      | Fail _ -> assert(False)
      | Return i0 ->
          let hm = Mkhash_map_t 0 (max_load_dividend, max_load_divisor) i0 v0 in
          slots_t_all_nil_inv_lem v0;
          slots_t_al_v_all_nil_is_empty_lem hm.hash_map_slots
      end
    end
  end
#pop-options

(*** new *)

/// [new] doesn't fail and returns an empty hash map
val hash_map_new_fwd_lem_aux (t : Type0) :
  Lemma
  (ensures (
    match hash_map_new_fwd t with
    | Fail _ -> False
    | Return hm ->
      // The hash map invariant is satisfied
      hash_map_t_inv hm /\
      // The hash map has 0 values
      hash_map_t_len_s hm = 0 /\
      // It contains no bindings
      (forall k. hash_map_t_find_s hm k == None)))

#push-options "--fuel 1"
let hash_map_new_fwd_lem_aux t =
  hash_map_new_with_capacity_fwd_lem t 32 4 5;
  match hash_map_new_with_capacity_fwd t 32 4 5 with
  | Fail _ -> ()
  | Return hm -> ()
#pop-options

/// The lemma we reveal in the .fsti
let hash_map_new_fwd_lem t = hash_map_new_fwd_lem_aux t

(*** clear_slots *)
/// [clear_slots] doesn't fail and simply clears the slots starting at index i
#push-options "--fuel 1"
let rec hash_map_clear_slots_fwd_back_lem
  (t : Type0) (slots : vec (list_t t)) (i : usize) :
  Lemma
  (ensures (
    match hash_map_clear_slots_fwd_back t slots i with
    | Fail _ -> False
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
    | Fail _ -> ()
    | Return v ->
      begin match usize_add i 1 with
      | Fail _ -> ()
      | Return i1 ->
        hash_map_clear_slots_fwd_back_lem t v i1;
        begin match hash_map_clear_slots_fwd_back t v i1 with
        | Fail _ -> ()
        | Return slots1 ->
          assert(length slots1 == length slots);
          assert(forall (j:nat{i+1 <= j /\ j < length slots}). index slots1 j == ListNil);
          assert(index slots1 i == ListNil)
        end
      end
    end
  else ()
#pop-options

(*** clear *)
/// [clear] doesn't fail and turns the hash map into an empty map
val hash_map_clear_fwd_back_lem_aux
  (#t : Type0) (self : hash_map_t t) :
  Lemma
  (requires (hash_map_t_base_inv self))
  (ensures (
    match hash_map_clear_fwd_back t self with
    | Fail _ -> False
    | Return hm ->
      // The hash map invariant is satisfied
      hash_map_t_base_inv hm /\
      // We preserved the parameters
      hash_map_t_same_params hm self /\
      // The hash map has 0 values
      hash_map_t_len_s hm = 0 /\
      // It contains no bindings
      (forall k. hash_map_t_find_s hm k == None)))

// Being lazy: fuel 1 helps a lot...
#push-options "--fuel 1"
let hash_map_clear_fwd_back_lem_aux #t self =
  let p = self.hash_map_max_load_factor in
  let i = self.hash_map_max_load in
  let v = self.hash_map_slots in
  hash_map_clear_slots_fwd_back_lem t v 0;
  begin match hash_map_clear_slots_fwd_back t v 0 with
  | Fail _ -> ()
  | Return slots1 ->
    slots_t_al_v_all_nil_is_empty_lem slots1;
    let hm1 = Mkhash_map_t 0 p i slots1 in
    assert(hash_map_t_base_inv hm1);
    assert(hash_map_t_inv hm1)
  end
#pop-options

let hash_map_clear_fwd_back_lem #t self = hash_map_clear_fwd_back_lem_aux #t self

(*** len *)

/// [len]: we link it to a non-failing function.
/// Rk.: we might want to make an analysis to not use an error monad to translate
/// functions which statically can't fail.
let hash_map_len_fwd_lem #t self = ()


(*** insert_in_list *)

(**** insert_in_list'fwd *)

/// [insert_in_list_fwd]: returns true iff the key is not in the list (functional version)
val hash_map_insert_in_list_fwd_lem
  (t : Type0) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (ensures (
    match hash_map_insert_in_list_fwd t key value ls with
    | Fail _ -> False
    | Return b ->
      b <==> (slot_t_find_s key ls == None)))
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
      | Fail _ -> ()
      | Return b0 -> ()
      end
  | ListNil ->
    assert(list_t_v ls == []);
    assert_norm(find (same_key #t key) [] == None)
  end
#pop-options

(**** insert_in_list'back *)

/// The proofs about [insert_in_list] backward are easier to do in several steps:
/// extrinsic proofs to the rescue!
/// We first prove that [insert_in_list] refines the function we wrote above, then
/// use this function to prove the invariants, etc.

/// We write a helper which "captures" what [insert_in_list] does.
/// We then reason about this helper to prove the high-level properties we want
/// (functional properties, preservation of invariants, etc.).
let hash_map_insert_in_list_s
  (#t : Type0) (key : usize) (value : t) (ls : list (binding t)) :
  list (binding t) =
  // Check if there is already a binding for the key
  match find (same_key key) ls with
  | None ->
    // No binding: append the binding to the end
    ls @ [(key,value)]
  | Some _ ->
    // There is already a binding: update it
    find_update (same_key key) ls (key,value)

/// [insert_in_list]: if the key is not in the map, appends a new bindings (functional version)
val hash_map_insert_in_list_back_lem_append_s
  (t : Type0) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (requires (
    slot_t_find_s key ls == None))
  (ensures (
    match hash_map_insert_in_list_back t key value ls with
    | Fail _ -> False
    | Return ls' ->
      list_t_v ls' == list_t_v ls @ [(key,value)]))
  (decreases (hash_map_insert_in_list_decreases t key value ls))

#push-options "--fuel 1"
let rec hash_map_insert_in_list_back_lem_append_s t key value ls =
  begin match ls with
  | ListCons ckey cvalue ls0 ->
    let b = ckey = key in
    if b
    then ()
    else
      begin
      hash_map_insert_in_list_back_lem_append_s t key value ls0;
      match hash_map_insert_in_list_back t key value ls0 with
      | Fail _ -> ()
      | Return l -> ()
      end
  | ListNil -> ()
  end
#pop-options

/// [insert_in_list]: if the key is in the map, we update the binding (functional version)
val hash_map_insert_in_list_back_lem_update_s
  (t : Type0) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (requires (
    Some? (find (same_key key) (list_t_v ls))))
  (ensures (
    match hash_map_insert_in_list_back t key value ls with
    | Fail _ -> False
    | Return ls' ->
      list_t_v ls' == find_update (same_key key) (list_t_v ls) (key,value)))
  (decreases (hash_map_insert_in_list_decreases t key value ls))

#push-options "--fuel 1"
let rec hash_map_insert_in_list_back_lem_update_s t key value ls =
  begin match ls with
  | ListCons ckey cvalue ls0 ->
    let b = ckey = key in
    if b
    then ()
    else
      begin
      hash_map_insert_in_list_back_lem_update_s t key value ls0;
      match hash_map_insert_in_list_back t key value ls0 with
      | Fail _ -> ()
      | Return l -> ()
      end
  | ListNil -> ()
  end
#pop-options

/// Put everything together
val hash_map_insert_in_list_back_lem_s
  (t : Type0) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (ensures (
    match hash_map_insert_in_list_back t key value ls with
    | Fail _ -> False
    | Return ls' ->
      list_t_v ls' == hash_map_insert_in_list_s key value (list_t_v ls)))

let hash_map_insert_in_list_back_lem_s t key value ls =
  match find (same_key key) (list_t_v ls) with
  | None -> hash_map_insert_in_list_back_lem_append_s t key value ls
  | Some _ -> hash_map_insert_in_list_back_lem_update_s t key value ls

(**** Invariants of insert_in_list_s *)

/// Auxiliary lemmas
/// We work on [hash_map_insert_in_list_s], the "high-level" version of [insert_in_list'back].
///
/// Note that in F* we can't have recursive proofs inside of other proofs, contrary
/// to Coq, which makes it a bit cumbersome to prove auxiliary results like the
/// following ones...

(** Auxiliary lemmas: append case *)

val slot_t_v_for_all_binding_neq_append_lem
  (t : Type0) (key : usize) (value : t) (ls : list (binding t)) (b : binding t) :
  Lemma
  (requires (
    fst b <> key /\
    for_all (binding_neq b) ls /\
    slot_s_find key ls == None))
  (ensures (
    for_all (binding_neq b) (ls @ [(key,value)])))

#push-options "--fuel 1"
let rec slot_t_v_for_all_binding_neq_append_lem t key value ls b =
  match ls with
  | [] -> ()
  | (ck, cv) :: cls ->
    slot_t_v_for_all_binding_neq_append_lem t key value cls b
#pop-options

val slot_s_inv_not_find_append_end_inv_lem
  (t : Type0) (len : usize{len > 0}) (key : usize) (value : t) (ls : list (binding t)) :
  Lemma
  (requires (
    slot_s_inv len (hash_mod_key key len) ls /\
    slot_s_find key ls == None))
  (ensures (
    let ls' = ls @ [(key,value)] in
    slot_s_inv len (hash_mod_key key len) ls' /\
    (slot_s_find key ls' == Some value) /\
    (forall k'. k' <> key ==> slot_s_find k' ls' == slot_s_find k' ls)))

#push-options "--fuel 1"
let rec slot_s_inv_not_find_append_end_inv_lem t len key value ls =
  match ls with
  | [] -> ()
  | (ck, cv) :: cls ->
    slot_s_inv_not_find_append_end_inv_lem t len key value cls;
    let h = hash_mod_key key len in
    let ls' = ls @ [(key,value)] in
    assert(for_all (same_hash_mod_key len h) ls');
    slot_t_v_for_all_binding_neq_append_lem t key value cls (ck, cv);
    assert(pairwise_rel binding_neq ls');
    assert(slot_s_inv len h ls')
#pop-options

/// [insert_in_list]: if the key is not in the map, appends a new bindings
val hash_map_insert_in_list_s_lem_append
  (t : Type0) (len : usize{len > 0}) (key : usize) (value : t) (ls : list (binding t)) :
  Lemma
  (requires (
    slot_s_inv len (hash_mod_key key len) ls /\
    slot_s_find key ls == None))
  (ensures (
    let ls' = hash_map_insert_in_list_s key value ls in
    ls' == ls @ [(key,value)] /\
    // The invariant is preserved
    slot_s_inv len (hash_mod_key key len) ls' /\
    // [key] maps to [value]
    slot_s_find key ls' == Some value /\
    // The other bindings are preserved
    (forall k'. k' <> key ==> slot_s_find k' ls' == slot_s_find k' ls)))

let hash_map_insert_in_list_s_lem_append t len key value ls =
  slot_s_inv_not_find_append_end_inv_lem t len key value ls

/// [insert_in_list]: if the key is not in the map, appends a new bindings (quantifiers)
/// Rk.: we don't use this lemma.
/// TODO: remove?
val hash_map_insert_in_list_back_lem_append
  (t : Type0) (len : usize{len > 0}) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (requires (
    slot_t_inv len (hash_mod_key key len) ls /\
    slot_t_find_s key ls == None))
  (ensures (
    match hash_map_insert_in_list_back t key value ls with
    | Fail _ -> False
    | Return ls' ->
      list_t_v ls' == list_t_v ls @ [(key,value)] /\
      // The invariant is preserved
      slot_t_inv len (hash_mod_key key len) ls' /\
      // [key] maps to [value]
      slot_t_find_s key ls' == Some value /\
      // The other bindings are preserved
      (forall k'. k' <> key ==> slot_t_find_s k' ls' == slot_t_find_s k' ls)))

let hash_map_insert_in_list_back_lem_append t len key value ls =
  hash_map_insert_in_list_back_lem_s t key value ls;
  hash_map_insert_in_list_s_lem_append t len key value (list_t_v ls)

(** Auxiliary lemmas: update case *)

val slot_s_find_update_for_all_binding_neq_append_lem
  (t : Type0) (key : usize) (value : t) (ls : list (binding t)) (b : binding t) :
  Lemma
  (requires (
    fst b <> key /\
    for_all (binding_neq b) ls))
  (ensures (
    let ls' = find_update (same_key key) ls (key, value) in
    for_all (binding_neq b) ls'))

#push-options "--fuel 1"
let rec slot_s_find_update_for_all_binding_neq_append_lem t key value ls b =
  match ls with
  | [] -> ()
  | (ck, cv) :: cls ->
    slot_s_find_update_for_all_binding_neq_append_lem t key value cls b
#pop-options

/// Annoying auxiliary lemma we have to prove because there is no way to reason
/// properly about closures.
/// I'm really enjoying my time.
val for_all_binding_neq_value_indep
  (#t : Type0) (key : key) (v0 v1 : t) (ls : list (binding t)) :
  Lemma (for_all (binding_neq (key,v0)) ls = for_all (binding_neq (key,v1)) ls)

#push-options "--fuel 1"
let rec for_all_binding_neq_value_indep #t key v0 v1 ls =
  match ls with
  | [] -> ()
  | _ :: ls' -> for_all_binding_neq_value_indep #t key v0 v1 ls'
#pop-options

val slot_s_inv_find_append_end_inv_lem
  (t : Type0) (len : usize{len > 0}) (key : usize) (value : t) (ls : list (binding t)) :
  Lemma
  (requires (
    slot_s_inv len (hash_mod_key key len) ls /\
    Some? (slot_s_find key ls)))
  (ensures (
    let ls' = find_update (same_key key) ls (key, value) in
    slot_s_inv len (hash_mod_key key len) ls' /\
    (slot_s_find key ls' == Some value) /\
    (forall k'. k' <> key ==> slot_s_find k' ls' == slot_s_find k' ls)))

#push-options "--z3rlimit 50 --fuel 1"
let rec slot_s_inv_find_append_end_inv_lem t len key value ls =
  match ls with
  | [] -> ()
  | (ck, cv) :: cls ->
    let h = hash_mod_key key len in
    let ls' = find_update (same_key key) ls (key, value) in
    if ck = key then
      begin
      assert(ls' == (ck,value) :: cls);
      assert(for_all (same_hash_mod_key len h) ls');
      // For pairwise_rel: binding_neq (ck, value) is actually independent
      // of `value`. Slightly annoying to prove in F*...
      assert(for_all (binding_neq (ck,cv)) cls);
      for_all_binding_neq_value_indep key cv value cls;
      assert(for_all (binding_neq (ck,value)) cls);
      assert(pairwise_rel binding_neq ls');
      assert(slot_s_inv len (hash_mod_key key len) ls')
      end
    else
      begin
      slot_s_inv_find_append_end_inv_lem t len key value cls;
      assert(for_all (same_hash_mod_key len h) ls');
      slot_s_find_update_for_all_binding_neq_append_lem t key value cls (ck, cv);
      assert(pairwise_rel binding_neq ls');
      assert(slot_s_inv len h ls')
      end
#pop-options

/// [insert_in_list]: if the key is in the map, update the bindings
val hash_map_insert_in_list_s_lem_update
  (t : Type0) (len : usize{len > 0}) (key : usize) (value : t) (ls : list (binding t)) :
  Lemma
  (requires (
    slot_s_inv len (hash_mod_key key len) ls /\
    Some? (slot_s_find key ls)))
  (ensures (
    let ls' = hash_map_insert_in_list_s key value ls in
    ls' == find_update (same_key key) ls (key,value) /\
    // The invariant is preserved
    slot_s_inv len (hash_mod_key key len) ls' /\
    // [key] maps to [value]
    slot_s_find key ls' == Some value /\
    // The other bindings are preserved
    (forall k'. k' <> key ==> slot_s_find k' ls' == slot_s_find k' ls)))

let hash_map_insert_in_list_s_lem_update t len key value ls =
  slot_s_inv_find_append_end_inv_lem t len key value ls


/// [insert_in_list]: if the key is in the map, update the bindings
/// TODO: not used: remove?
val hash_map_insert_in_list_back_lem_update
  (t : Type0) (len : usize{len > 0}) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (requires (
    slot_t_inv len (hash_mod_key key len) ls /\
    Some? (slot_t_find_s key ls)))
  (ensures (
    match hash_map_insert_in_list_back t key value ls with
    | Fail _ -> False
    | Return ls' ->
      let als = list_t_v ls in
      list_t_v ls' == find_update (same_key key) als (key,value) /\
      // The invariant is preserved
      slot_t_inv len (hash_mod_key key len) ls' /\
      // [key] maps to [value]
      slot_t_find_s key ls' == Some value /\
      // The other bindings are preserved
      (forall k'. k' <> key ==> slot_t_find_s k' ls' == slot_t_find_s k' ls)))

let hash_map_insert_in_list_back_lem_update t len key value ls =
  hash_map_insert_in_list_back_lem_s t key value ls;
  hash_map_insert_in_list_s_lem_update t len key value (list_t_v ls)

(** Final lemmas about [insert_in_list] *)

/// High-level version
val hash_map_insert_in_list_s_lem
  (t : Type0) (len : usize{len > 0}) (key : usize) (value : t) (ls : list (binding t)) :
  Lemma
  (requires (
    slot_s_inv len (hash_mod_key key len) ls))
  (ensures (
    let ls' = hash_map_insert_in_list_s key value ls in
    // The invariant is preserved
    slot_s_inv len (hash_mod_key key len) ls' /\
    // [key] maps to [value]
    slot_s_find key ls' == Some value /\
    // The other bindings are preserved
    (forall k'. k' <> key ==> slot_s_find k' ls' == slot_s_find k' ls) /\
    // The length is incremented, iff we inserted a new key
    (match slot_s_find key ls with
     | None -> length ls' = length ls + 1
     | Some _ -> length ls' = length ls)))

let hash_map_insert_in_list_s_lem t len key value ls =
  match slot_s_find key ls with
  | None ->
    assert_norm(length [(key,value)] = 1);
    hash_map_insert_in_list_s_lem_append t len key value ls
  | Some _ ->
    hash_map_insert_in_list_s_lem_update t len key value ls

/// [insert_in_list]
/// TODO: not used: remove?
val hash_map_insert_in_list_back_lem
  (t : Type0) (len : usize{len > 0}) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (requires (slot_t_inv len (hash_mod_key key len) ls))
  (ensures (
    match hash_map_insert_in_list_back t key value ls with
    | Fail _ -> False
    | Return ls' ->
      // The invariant is preserved
      slot_t_inv len (hash_mod_key key len) ls' /\
      // [key] maps to [value]
      slot_t_find_s key ls' == Some value /\
      // The other bindings are preserved
      (forall k'. k' <> key ==> slot_t_find_s k' ls' == slot_t_find_s k' ls) /\
      // The length is incremented, iff we inserted a new key
      (match slot_t_find_s key ls with
       | None ->
         list_t_v ls' == list_t_v ls @ [(key,value)] /\
         list_t_len ls' = list_t_len ls + 1
       | Some _ ->
         list_t_v ls' == find_update (same_key key) (list_t_v ls) (key,value) /\
         list_t_len ls' = list_t_len ls)))
  (decreases (hash_map_insert_in_list_decreases t key value ls))

let hash_map_insert_in_list_back_lem t len key value ls =
  hash_map_insert_in_list_back_lem_s t key value ls;
  hash_map_insert_in_list_s_lem t len key value (list_t_v ls)

(*** insert_no_resize *)

(**** Refinement proof *)
/// Same strategy as for [insert_in_list]: we introduce a high-level version of
/// the function, and reason about it.
/// We work on [hash_map_s] (we use a higher-level view of the hash-map, but
/// not too high).

/// A high-level version of insert, which doesn't check if the table is saturated
let hash_map_insert_no_fail_s
  (#t : Type0) (hm : hash_map_s_nes t)
  (key : usize) (value : t) :
  hash_map_s t =
  let len = length hm in
  let i = hash_mod_key key len in
  let slot = index hm i in
  let slot' = hash_map_insert_in_list_s key value slot in
  let hm' = list_update hm i slot' in
  hm'

// TODO: at some point I used hash_map_s_nes and it broke proofs...x
let hash_map_insert_no_resize_s
  (#t : Type0) (hm : hash_map_s_nes t)
  (key : usize) (value : t) :
  result (hash_map_s t) =
  // Check if the table is saturated (too many entries, and we need to insert one)
  let num_entries = length (flatten hm) in
  if None? (hash_map_s_find hm key) && num_entries = usize_max then Fail Failure
  else Return (hash_map_insert_no_fail_s hm key value)

/// Prove that [hash_map_insert_no_resize_s] is refined by
/// [hash_map_insert_no_resize'fwd_back]
val hash_map_insert_no_resize_fwd_back_lem_s
  (t : Type0) (self : hash_map_t t) (key : usize) (value : t) :
  Lemma
  (requires (
    hash_map_t_base_inv self /\
    hash_map_s_len (hash_map_t_v self) = hash_map_t_len_s self))
  (ensures (
    begin
    match hash_map_insert_no_resize_fwd_back t self key value,
          hash_map_insert_no_resize_s (hash_map_t_v self) key value
    with
    | Fail _, Fail _ -> True
    | Return hm, Return hm_v ->
      hash_map_t_base_inv hm /\
      hash_map_t_same_params hm self /\
      hash_map_t_v hm == hm_v /\
      hash_map_s_len hm_v == hash_map_t_len_s hm
    | _ -> False
    end))

let hash_map_insert_no_resize_fwd_back_lem_s t self key value =
  begin match hash_key_fwd key with
  | Fail _ -> ()
  | Return i ->
    let i0 = self.hash_map_num_entries in
    let p = self.hash_map_max_load_factor in
    let i1 = self.hash_map_max_load in
    let v = self.hash_map_slots in
    let i2 = vec_len (list_t t) v in
    let len = length v in
    begin match usize_rem i i2 with
    | Fail _ -> ()
    | Return hash_mod ->
      begin match vec_index_mut_fwd (list_t t) v hash_mod with
      | Fail _ -> ()
      | Return l ->
        begin
        // Checking that: list_t_v (index ...) == index (hash_map_t_v ...) ...
        assert(list_t_v l == index (hash_map_t_v self) hash_mod);
        hash_map_insert_in_list_fwd_lem t key value l;
        match hash_map_insert_in_list_fwd t key value l with
        | Fail _ -> ()
        | Return b ->
          assert(b = None? (slot_s_find key (list_t_v l)));
          hash_map_insert_in_list_back_lem t len key value l;
          if b
          then
            begin match usize_add i0 1 with
            | Fail _ -> ()
            | Return i3 ->
              begin
              match hash_map_insert_in_list_back t key value l with
              | Fail _ -> ()
              | Return l0 ->
                begin match vec_index_mut_back (list_t t) v hash_mod l0 with
                | Fail _ -> ()
                | Return v0 ->
                  let self_v = hash_map_t_v self in
                  let hm = Mkhash_map_t i3 p i1 v0 in
                  let hm_v = hash_map_t_v hm in
                  assert(hm_v == list_update self_v hash_mod (list_t_v l0));
                  assert_norm(length [(key,value)] = 1);
                  assert(length (list_t_v l0) = length (list_t_v l) + 1);
                  length_flatten_update self_v hash_mod (list_t_v l0);
                  assert(hash_map_s_len hm_v = hash_map_t_len_s hm)
                end
              end
            end
          else
            begin
            match hash_map_insert_in_list_back t key value l with
            | Fail _ -> ()
            | Return l0 ->
              begin match vec_index_mut_back (list_t t) v hash_mod l0 with
              | Fail _ -> ()
              | Return v0 ->
                let self_v = hash_map_t_v self in
                let hm = Mkhash_map_t i0 p i1 v0 in
                let hm_v = hash_map_t_v hm in
                assert(hm_v == list_update self_v hash_mod (list_t_v l0));
                assert(length (list_t_v l0) = length (list_t_v l));
                length_flatten_update self_v hash_mod (list_t_v l0);
                assert(hash_map_s_len hm_v = hash_map_t_len_s hm)
              end
            end
        end
      end
    end
  end

(**** insert_{no_fail,no_resize}: invariants *)

let hash_map_s_updated_binding
  (#t : Type0) (hm : hash_map_s_nes t)
  (key : usize) (opt_value : option t) (hm' : hash_map_s_nes t) : Type0 =
  // [key] maps to [value]
  hash_map_s_find hm' key == opt_value /\
  // The other bindings are preserved
  (forall k'. k' <> key ==> hash_map_s_find hm' k' == hash_map_s_find hm k')

let insert_post (#t : Type0) (hm : hash_map_s_nes t)
  (key : usize) (value : t) (hm' : hash_map_s_nes t) : Type0 =
  // The invariant is preserved
  hash_map_s_inv hm' /\
  // [key] maps to [value] and the other bindings are preserved
  hash_map_s_updated_binding hm key (Some value) hm' /\
  // The length is incremented, iff we inserted a new key
  (match hash_map_s_find hm key with
   | None -> hash_map_s_len hm' = hash_map_s_len hm + 1
   | Some _ -> hash_map_s_len hm' = hash_map_s_len hm)

val hash_map_insert_no_fail_s_lem
  (#t : Type0) (hm : hash_map_s_nes t)
  (key : usize) (value : t) :
  Lemma
  (requires (hash_map_s_inv hm))
  (ensures (
    let hm' = hash_map_insert_no_fail_s hm key value in
    insert_post hm key value hm'))

let hash_map_insert_no_fail_s_lem #t hm key value =
  let len = length hm in
  let i = hash_mod_key key len in
  let slot = index hm i in
  hash_map_insert_in_list_s_lem t len key value slot;
  let slot' = hash_map_insert_in_list_s key value slot in
  length_flatten_update hm i slot'

val hash_map_insert_no_resize_s_lem
  (#t : Type0) (hm : hash_map_s_nes t)
  (key : usize) (value : t) :
  Lemma
  (requires (hash_map_s_inv hm))
  (ensures (
    match hash_map_insert_no_resize_s hm key value with
    | Fail _ ->
      // Can fail only if we need to create a new binding in
      // an already saturated map
      hash_map_s_len hm = usize_max /\
      None? (hash_map_s_find hm key)
    | Return hm' ->
      insert_post hm key value hm'))

let hash_map_insert_no_resize_s_lem #t hm key value =
  let num_entries = length (flatten hm) in
  if None? (hash_map_s_find hm key) && num_entries = usize_max then ()
  else hash_map_insert_no_fail_s_lem hm key value


(**** find after insert *)
/// Lemmas about what happens if we call [find] after an insertion

val hash_map_insert_no_resize_s_get_same_lem
  (#t : Type0) (hm : hash_map_s t)
  (key : usize) (value : t) :
  Lemma (requires (hash_map_s_inv hm))
  (ensures (
    match hash_map_insert_no_resize_s hm key value with
    | Fail _ -> True
    | Return hm' ->
      hash_map_s_find hm' key == Some value))

let hash_map_insert_no_resize_s_get_same_lem #t hm key value =
  let num_entries = length (flatten hm) in
  if None? (hash_map_s_find hm key) && num_entries = usize_max then ()
  else
    begin
    let hm' = Return?.v (hash_map_insert_no_resize_s hm key value) in
    let len = length hm in
    let i = hash_mod_key key len in
    let slot = index hm i in
    hash_map_insert_in_list_s_lem t len key value slot
   end

val hash_map_insert_no_resize_s_get_diff_lem
  (#t : Type0) (hm : hash_map_s t)
  (key : usize) (value : t) (key' : usize{key' <> key}) :
  Lemma (requires (hash_map_s_inv hm))
  (ensures (
    match hash_map_insert_no_resize_s hm key value with
    | Fail _ -> True
    | Return hm' ->
      hash_map_s_find hm' key' == hash_map_s_find hm key'))

let hash_map_insert_no_resize_s_get_diff_lem #t hm key value key' =
  let num_entries = length (flatten hm) in
  if None? (hash_map_s_find hm key) && num_entries = usize_max then ()
  else
    begin
    let hm' = Return?.v (hash_map_insert_no_resize_s hm key value) in
    let len = length hm in
    let i = hash_mod_key key len in
    let slot = index hm i in
    hash_map_insert_in_list_s_lem t len key value slot;
    let i' = hash_mod_key key' len in
    if i <> i' then ()
    else
      begin
      ()
      end
   end


(*** move_elements_from_list *)

/// Having a great time here: if we use `result (hash_map_s_res t)` as the
/// return type for [hash_map_move_elements_from_list_s] instead of having this
/// awkward match, the proof of [hash_map_move_elements_fwd_back_lem_refin] fails.
/// I guess it comes from F*'s poor subtyping.
/// Followingly, I'm not taking any chance and using [result_hash_map_s]
/// everywhere.
type result_hash_map_s_nes (t : Type0) : Type0 =
  res:result (hash_map_s t) {
    match res with
    | Fail _ -> True
    | Return hm -> is_pos_usize (length hm)
  }

let rec hash_map_move_elements_from_list_s
  (#t : Type0) (hm : hash_map_s_nes t)
  (ls : slot_s t) :
  // Do *NOT* use `result (hash_map_s t)`
  Tot (result_hash_map_s_nes t)
  (decreases ls) =
  match ls with
  | [] -> Return hm
  | (key, value) :: ls' ->
    match hash_map_insert_no_resize_s hm key value with
    | Fail e -> Fail e
    | Return hm' ->
      hash_map_move_elements_from_list_s hm' ls'

/// Refinement lemma
val hash_map_move_elements_from_list_fwd_back_lem
  (t : Type0) (ntable : hash_map_t_nes t) (ls : list_t t) :
  Lemma (requires (hash_map_t_base_inv ntable))
  (ensures (
    match hash_map_move_elements_from_list_fwd_back t ntable ls,
          hash_map_move_elements_from_list_s (hash_map_t_v ntable) (slot_t_v ls)
    with
    | Fail _, Fail _ -> True
    | Return hm', Return hm_v ->
      hash_map_t_base_inv hm' /\
      hash_map_t_v hm' == hm_v /\
      hash_map_t_same_params hm' ntable
    | _ -> False))
  (decreases (hash_map_move_elements_from_list_decreases t ntable ls))

#push-options "--fuel 1"
let rec hash_map_move_elements_from_list_fwd_back_lem t ntable ls =
  begin match ls with
  | ListCons k v tl ->
    assert(list_t_v ls == (k, v) :: list_t_v tl);
    let ls_v = list_t_v ls in
    let (_,_) :: tl_v = ls_v in
    hash_map_insert_no_resize_fwd_back_lem_s t ntable k v;
    begin match hash_map_insert_no_resize_fwd_back t ntable k v with
    | Fail _ -> ()
    | Return h ->
      let h_v = Return?.v (hash_map_insert_no_resize_s (hash_map_t_v ntable) k v) in
      assert(hash_map_t_v h == h_v);
      hash_map_move_elements_from_list_fwd_back_lem t h tl;
      begin match hash_map_move_elements_from_list_fwd_back t h tl with
      | Fail _ -> ()
      | Return h0 -> ()
      end
    end
  | ListNil -> ()
  end
#pop-options

(*** move_elements *)

(**** move_elements: refinement 0 *)
/// The proof for [hash_map_move_elements_fwd_back_lem_refin] broke so many times
/// (while it is supposed to be super simple!) that we decided to add one refinement
/// level, to really do things step by step...
/// Doing this refinement layer made me notice that maybe the problem came from
/// the fact that at some point we have to prove `list_t_v ListNil == []`: I
/// added the corresponding assert to help Z3 and everything became stable.
/// I finally didn't use this "simple" refinement lemma, but I still keep it here
/// because it allows for easy comparisons with [hash_map_move_elements_s].

/// [hash_map_move_elements_fwd] refines this function, which is actually almost
/// the same (just a little bit shorter and cleaner, and has a pre).
///
/// The way I wrote the high-level model is the following:
/// - I copy-pasted the definition of [hash_map_move_elements_fwd], wrote the
///   signature which links this new definition to [hash_map_move_elements_fwd] and
///   checked that the proof passed
/// - I gradually simplified it, while making sure the proof still passes
#push-options "--fuel 1"
let rec hash_map_move_elements_s_simpl
  (t : Type0) (ntable : hash_map_t t)
  (slots : vec (list_t t))
  (i : usize{i <= length slots /\ length slots <= usize_max}) :
  Pure (result ((hash_map_t t) & (vec (list_t t))))
  (requires (True))
  (ensures (fun res ->
    match res, hash_map_move_elements_fwd_back t ntable slots i with
    | Fail _, Fail _ -> True
    | Return (ntable1, slots1), Return (ntable2, slots2) ->
      ntable1 == ntable2 /\
      slots1 == slots2
    | _ -> False))
  (decreases (hash_map_move_elements_decreases t ntable slots i))
  =
  if i < length slots
  then
    let slot = index slots i in
    begin match hash_map_move_elements_from_list_fwd_back t ntable slot with
    | Fail e -> Fail e
    | Return hm' ->
      let slots' = list_update slots i ListNil in
      hash_map_move_elements_s_simpl t hm' slots' (i+1)
    end
  else Return (ntable, slots)
#pop-options

(**** move_elements: refinement 1 *)
/// We prove a second refinement lemma: calling [move_elements] refines a function
/// which, for every slot, moves the element out of the slot. This first model is
/// almost exactly the translated function, it just uses `list` instead of `list_t`.

// Note that we ignore the returned slots (we thus don't return a pair:
// only the new hash map in which we moved the elements from the slots):
// this returned value is not used.
let rec hash_map_move_elements_s
  (#t : Type0) (hm : hash_map_s_nes t)
  (slots : slots_s t) (i : usize{i <= length slots /\ length slots <= usize_max}) :
  Tot (result_hash_map_s_nes t)
  (decreases (length slots - i)) =
  let len = length slots in
  if i < len then
    begin
    let slot = index slots i in
    match hash_map_move_elements_from_list_s hm slot with
    | Fail e -> Fail e
    | Return hm' ->
      let slots' = list_update slots i [] in
      hash_map_move_elements_s hm' slots' (i+1)
    end
  else Return hm

val hash_map_move_elements_fwd_back_lem_refin
  (t : Type0) (ntable : hash_map_t t)
  (slots : vec (list_t t)) (i : usize{i <= length slots}) :
  Lemma
  (requires (
    hash_map_t_base_inv ntable))
  (ensures (
    match hash_map_move_elements_fwd_back t ntable slots i,
          hash_map_move_elements_s (hash_map_t_v ntable) (slots_t_v slots) i
    with
    | Fail _, Fail _ -> True // We will prove later that this is not possible
    | Return (ntable', _), Return ntable'_v ->
      hash_map_t_base_inv ntable' /\
      hash_map_t_v ntable' == ntable'_v /\
      hash_map_t_same_params ntable' ntable
    | _ -> False))
 (decreases (length slots - i))

// This proof was super unstable for some reasons.
// 
// For instance, using the [hash_map_s_nes] type abbreviation
// in some of the above definitions led to a failure (while it was just a type
// abbreviation: the signatures were the same if we unfolded this type). This
// behaviour led me to the hypothesis that maybe it made F*'s type inference
// end up with a different result, which combined with its poor support for
// subtyping made the proof failed.
//
// However, later, unwrapping a definition led to another failure.
// 
// I thus tried to manually unfold some postconditions because it
// seemed to work for [hash_map_move_elements_fwd_back_lem] but it didn't
// succeed.
//
// I tried to increase the ifuel to 2, 3: it didn't work, and I fell back to
// other methods. Finally out of angriness I swiched the ifuel to 4 for no
// specific reason: everything worked fine.
// 
// I have *no clue* why 4 is the magic number. Also: it fails if I remove
// the unfolded postconditions (meaning I would probably need to increase
// the ifuel to unreasonable amounts).
//
// Finally, as I had succeeded in fixing the proof, I thought that maybe the
// initial problem with the type abbreviations was fixed: I thus tried to use
// them. Of course, it made the proof fail again, and this time no ifuel setting
// seemed to work.
//
// At this point I was just fed up and leave things as they were, without trying
// to cleanup the previous definitions.
//
// Finally, even later it broke, again, at which point I had no choice but to
// introduce an even simpler refinement proof (with [hash_map_move_elements_s_simpl]).
// Doing this allowed me to see that maybe the problem came from the fact that
// Z3 had to prove that `list_t_v ListNil == []` at some point, so I added the
// corresponding assertion and miraculously everything becamse stable... I then
// removed all the postconditions I had manually instanciated and inserted in
// the proof, and which took a lot of place.
// I still have no clue why `ifuel 4` made it work earlier.
//
// The terrible thing is that this refinement proof is conceptually super simple:
// - there are maybe two arithmetic proofs, which are directly solved by the
//   precondition
// - we need to prove the call to [hash_map_move_elements_from_list_fwd_back]
//   refines its model: this is proven by another refinement lemma we proved above
// - there is the recursive call (trivial)
#restart-solver
#push-options "--fuel 1"
let rec hash_map_move_elements_fwd_back_lem_refin t ntable slots i =
  assert(hash_map_t_base_inv ntable);
  let i0 = vec_len (list_t t) slots in
  let b = i < i0 in
  if b
  then
    begin match vec_index_mut_fwd (list_t t) slots i with
    | Fail _ -> ()
    | Return l ->
      let l0 = mem_replace_fwd (list_t t) l ListNil in
      assert(l0 == l);
      hash_map_move_elements_from_list_fwd_back_lem t ntable l0;
      begin match hash_map_move_elements_from_list_fwd_back t ntable l0 with
      | Fail _ -> ()
      | Return h ->
        let l1 = mem_replace_back (list_t t) l ListNil in
        assert(l1 == ListNil);
        assert(slot_t_v #t ListNil == []); // THIS IS IMPORTANT
        begin match vec_index_mut_back (list_t t) slots i l1 with
        | Fail _ -> ()
        | Return v ->
          begin match usize_add i 1 with
          | Fail _ -> ()
          | Return i1 ->
            hash_map_move_elements_fwd_back_lem_refin t h v i1;
            begin match hash_map_move_elements_fwd_back t h v i1 with
            | Fail _ ->
              assert(Fail? (hash_map_move_elements_fwd_back t ntable slots i));
              ()
            | Return (ntable', v0) -> ()
            end
          end
        end
      end
    end
  else ()
#pop-options


(**** move_elements: refinement 2 *)
/// We prove a second refinement lemma: calling [move_elements] refines a function
/// which moves every binding of the hash map seen as *one* associative list
/// (and not a list of lists).

/// [ntable] is the hash map to which we move the elements
/// [slots] is the current hash map, from which we remove the elements, and seen
///         as a "flat" associative list (and not a list of lists)
/// This is actually exactly [hash_map_move_elements_from_list_s]...
let rec hash_map_move_elements_s_flat
  (#t : Type0) (ntable : hash_map_s_nes t)
  (slots : assoc_list t) :
  Tot (result_hash_map_s_nes t)
  (decreases slots) =
  match slots with
  | [] -> Return ntable
  | (k,v) :: slots' ->
    match hash_map_insert_no_resize_s ntable k v with
    | Fail e -> Fail e
    | Return ntable' ->
      hash_map_move_elements_s_flat ntable' slots'

/// The refinment lemmas
/// First, auxiliary helpers.

/// Flatten a list of lists, starting at index i
val flatten_i :
     #a:Type
  -> l:list (list a)
  -> i:nat{i <= length l}
  -> Tot (list a) (decreases (length l - i))

let rec flatten_i l i =
  if i < length l then
    index l i @ flatten_i l (i+1)
  else []

let _ = assert(let l = [1;2] in l == hd l :: tl l)

val flatten_i_incr :
     #a:Type
  -> l:list (list a)
  -> i:nat{Cons? l /\ i+1 <= length l} ->
  Lemma
  (ensures (
    (**) assert_norm(length (hd l :: tl l) == 1 + length (tl l));
    flatten_i l (i+1) == flatten_i (tl l) i))
  (decreases (length l - (i+1)))

#push-options "--fuel 1"
let rec flatten_i_incr l i =
  let x :: tl = l in
  if i + 1 < length l then
    begin
    assert(flatten_i l (i+1) == index l (i+1) @ flatten_i l (i+2));
    flatten_i_incr l (i+1);
    assert(flatten_i l (i+2) == flatten_i tl (i+1));
    assert(index l (i+1) == index tl i)
    end
  else ()
#pop-options

val flatten_0_is_flatten :
     #a:Type
  -> l:list (list a) ->
  Lemma
  (ensures (flatten_i l 0 == flatten l))

#push-options "--fuel 1"
let rec flatten_0_is_flatten #a l =
  match l with
  | [] -> ()
  | x :: l' ->
    flatten_i_incr l 0;
    flatten_0_is_flatten l'
#pop-options

/// Auxiliary lemma
val flatten_nil_prefix_as_flatten_i :
     #a:Type
  -> l:list (list a)
  -> i:nat{i <= length l} ->
  Lemma (requires (forall (j:nat{j < i}). index l j == []))
  (ensures (flatten l == flatten_i l i))

#push-options "--fuel 1"
let rec flatten_nil_prefix_as_flatten_i #a l i =
  if i = 0 then flatten_0_is_flatten l
  else
    begin
    let x :: l' = l in
    assert(index l 0 == []);
    assert(x == []);
    assert(flatten l == flatten l');
    flatten_i_incr l (i-1);
    assert(flatten_i l i == flatten_i l' (i-1));
    assert(forall (j:nat{j < length l'}). index l' j == index l (j+1));
    flatten_nil_prefix_as_flatten_i l' (i-1);
    assert(flatten l' == flatten_i l' (i-1))
    end
#pop-options

/// The proof is trivial, the functions are the same.
/// Just keeping two definitions to allow changes...
val hash_map_move_elements_from_list_s_as_flat_lem
  (#t : Type0) (hm : hash_map_s_nes t)
  (ls : slot_s t) :
  Lemma
  (ensures (
    hash_map_move_elements_from_list_s hm ls ==
    hash_map_move_elements_s_flat hm ls))
  (decreases ls)

#push-options "--fuel 1"
let rec hash_map_move_elements_from_list_s_as_flat_lem #t hm ls =
  match ls with
  | [] -> ()
  | (key, value) :: ls' ->
    match hash_map_insert_no_resize_s hm key value with
    | Fail _ -> ()
    | Return hm' ->
      hash_map_move_elements_from_list_s_as_flat_lem hm' ls'
#pop-options

/// Composition of two calls to [hash_map_move_elements_s_flat]
let hash_map_move_elements_s_flat_comp
  (#t : Type0) (hm : hash_map_s_nes t) (slot0 slot1 : slot_s t) :
  Tot (result_hash_map_s_nes t) =
  match hash_map_move_elements_s_flat hm slot0 with
  | Fail e -> Fail e
  | Return hm1 -> hash_map_move_elements_s_flat hm1 slot1

/// High-level desc:
/// move_elements (move_elements hm slot0) slo1 == move_elements hm (slot0 @ slot1)
val hash_map_move_elements_s_flat_append_lem
  (#t : Type0) (hm : hash_map_s_nes t) (slot0 slot1 : slot_s t) :
  Lemma
  (ensures (
    match hash_map_move_elements_s_flat_comp hm slot0 slot1,
          hash_map_move_elements_s_flat hm (slot0 @ slot1)
    with
    | Fail _, Fail _ -> True
    | Return hm1, Return hm2 -> hm1 == hm2
    | _ -> False))
  (decreases (slot0))

#push-options "--fuel 1"
let rec hash_map_move_elements_s_flat_append_lem #t hm slot0 slot1 =
  match slot0 with
  | [] -> ()
  | (k,v) :: slot0' ->
    match hash_map_insert_no_resize_s hm k v with
    | Fail _ -> ()
    | Return hm' ->
      hash_map_move_elements_s_flat_append_lem hm' slot0' slot1
#pop-options

val flatten_i_same_suffix (#a : Type) (l0 l1 : list (list a)) (i : nat) :
  Lemma
  (requires (
    i <= length l0 /\
    length l0 = length l1 /\
    (forall (j:nat{i <= j /\ j < length l0}). index l0 j == index l1 j)))
  (ensures (flatten_i l0 i == flatten_i l1 i))
  (decreases (length l0 - i))

#push-options "--fuel 1"
let rec flatten_i_same_suffix #a l0 l1 i =
  if i < length l0 then
    flatten_i_same_suffix l0 l1 (i+1)
  else ()
#pop-options

/// Refinement lemma:
/// [hash_map_move_elements_s] refines [hash_map_move_elements_s_flat]
/// (actually the functions are equal on all inputs).
val hash_map_move_elements_s_lem_refin_flat
  (#t : Type0) (hm : hash_map_s_nes t)
  (slots : slots_s t)
  (i : nat{i <= length slots /\ length slots <= usize_max}) :
  Lemma
  (ensures (
    match hash_map_move_elements_s hm slots i,
          hash_map_move_elements_s_flat hm (flatten_i slots i)
    with
    | Fail _, Fail _ -> True
    | Return hm, Return hm' -> hm == hm'
    | _ -> False))
  (decreases (length slots - i))

#push-options "--fuel 1"
let rec hash_map_move_elements_s_lem_refin_flat #t hm slots i =
  let len = length slots in
  if i < len then
    begin
    let slot = index slots i in
    hash_map_move_elements_from_list_s_as_flat_lem hm slot;
    match hash_map_move_elements_from_list_s hm slot with
    | Fail _ ->
      assert(flatten_i slots i == slot @ flatten_i slots (i+1));
      hash_map_move_elements_s_flat_append_lem hm slot (flatten_i slots (i+1));
      assert(Fail? (hash_map_move_elements_s_flat hm (flatten_i slots i)))
    | Return hm' ->
      let slots' = list_update slots i [] in
      flatten_i_same_suffix slots slots' (i+1);
      hash_map_move_elements_s_lem_refin_flat hm' slots' (i+1);
      hash_map_move_elements_s_flat_append_lem hm slot (flatten_i slots' (i+1));
      ()
    end
  else ()
#pop-options

let assoc_list_inv (#t : Type0) (al : assoc_list t) : Type0 =
  // All the keys are pairwise distinct
  pairwise_rel binding_neq al

let disjoint_hm_al_on_key
  (#t : Type0) (hm : hash_map_s_nes t) (al : assoc_list t) (k : key) : Type0 =
  match hash_map_s_find hm k, assoc_list_find k al with
  | Some _, None
  | None, Some _
  | None, None -> True
  | Some _, Some _ -> False

/// Playing a dangerous game here: using forall quantifiers
let disjoint_hm_al (#t : Type0) (hm : hash_map_s_nes t) (al : assoc_list t) : Type0 =
  forall (k:key). disjoint_hm_al_on_key hm al k

let find_in_union_hm_al
  (#t : Type0) (hm : hash_map_s_nes t) (al : assoc_list t) (k : key) :
  option t =
  match hash_map_s_find hm k with
  | Some b -> Some b
  | None -> assoc_list_find k al

/// Auxiliary lemma
val for_all_binding_neq_find_lem (#t : Type0) (k : key) (v : t) (al : assoc_list t) :
  Lemma (requires (for_all (binding_neq (k,v)) al))
  (ensures (assoc_list_find k al == None))

#push-options "--fuel 1"
let rec for_all_binding_neq_find_lem #t k v al =
  match al with
  | [] -> ()
  | b :: al' -> for_all_binding_neq_find_lem k v al'
#pop-options

val hash_map_move_elements_s_flat_lem
  (#t : Type0) (hm : hash_map_s_nes t) (al : assoc_list t) :
  Lemma
  (requires (
    // Invariants
    hash_map_s_inv hm /\
    assoc_list_inv al /\
    // The two are disjoint
    disjoint_hm_al hm al /\
    // We can add all the elements to the hashmap
    hash_map_s_len hm + length al <= usize_max))
  (ensures (
    match hash_map_move_elements_s_flat hm al with
    | Fail _ -> False // We can't fail
    | Return hm' ->
      // The invariant is preserved
      hash_map_s_inv hm' /\
      // The new hash map is the union of the two maps
      (forall (k:key). hash_map_s_find hm' k == find_in_union_hm_al hm al k) /\
      hash_map_s_len hm' = hash_map_s_len hm + length al))
  (decreases al)

#restart-solver
#push-options "--z3rlimit 200 --fuel 1"
let rec hash_map_move_elements_s_flat_lem #t hm al =
  match al with
  | [] -> ()
  | (k,v) :: al' ->
    hash_map_insert_no_resize_s_lem hm k v;
    match hash_map_insert_no_resize_s hm k v with
    | Fail _ -> ()
    | Return hm' ->
      assert(hash_map_s_inv hm');
      assert(assoc_list_inv al');
      let disjoint_lem (k' : key) :
        Lemma (disjoint_hm_al_on_key hm' al' k')
        [SMTPat (disjoint_hm_al_on_key hm' al' k')] =
        if k' = k then
          begin
          assert(hash_map_s_find hm' k' == Some v);
          for_all_binding_neq_find_lem k v al';
          assert(assoc_list_find k' al' == None)
          end
        else
          begin
          assert(hash_map_s_find hm' k' == hash_map_s_find hm k');
          assert(assoc_list_find k' al' == assoc_list_find k' al)
          end
      in
      assert(disjoint_hm_al hm' al');
      assert(hash_map_s_len hm' + length al' <= usize_max);
      hash_map_move_elements_s_flat_lem hm' al'
#pop-options

/// We need to prove that the invariants on the "low-level" representations of
/// the hash map imply the invariants on the "high-level" representations.

val slots_t_inv_implies_slots_s_inv
  (#t : Type0) (slots : slots_t t{length slots <= usize_max}) :
  Lemma (requires (slots_t_inv slots))
  (ensures (slots_s_inv (slots_t_v slots)))

let slots_t_inv_implies_slots_s_inv #t slots =
  // Ok, works fine: this lemma was useless.
  // Problem is: I can never really predict for sure with F*...
  ()

val hash_map_t_base_inv_implies_hash_map_s_inv
  (#t : Type0) (hm : hash_map_t t) :
  Lemma (requires (hash_map_t_base_inv hm))
  (ensures (hash_map_s_inv (hash_map_t_v hm)))

let hash_map_t_base_inv_implies_hash_map_s_inv #t hm = () // same as previous

/// Introducing a "partial" version of the hash map invariant, which operates on
/// a suffix of the hash map.
let partial_hash_map_s_inv
  (#t : Type0) (len : usize{len > 0}) (offset : usize)
  (hm : hash_map_s t{offset + length hm <= usize_max}) : Type0 =
  forall(i:nat{i < length hm}). {:pattern index hm i} slot_s_inv len (offset + i) (index hm i)

/// Auxiliary lemma.
/// If a binding comes from a slot i, then its key is different from the keys
/// of the bindings in the other slots (because the hashes of the keys are distinct).
val binding_in_previous_slot_implies_neq
  (#t : Type0) (len : usize{len > 0})
  (i : usize) (b : binding t)
  (offset : usize{i < offset})
  (slots : hash_map_s t{offset + length slots <= usize_max}) :
  Lemma
  (requires (
    // The binding comes from a slot not in [slots]
    hash_mod_key (fst b) len = i /\
    // The slots are the well-formed suffix of a hash map
    partial_hash_map_s_inv len offset slots))
  (ensures (
    for_all (binding_neq b) (flatten slots)))
  (decreases slots)

#push-options "--z3rlimit 100 --fuel 1"
let rec binding_in_previous_slot_implies_neq #t len i b offset slots =
  match slots with
  | [] -> ()
  | s :: slots' ->
    assert(slot_s_inv len offset (index slots 0)); // Triggers patterns
    assert(slot_s_inv len offset s);
    // Proving TARGET. We use quantifiers.
    assert(for_all (same_hash_mod_key len offset) s);
    forall_index_equiv_list_for_all (same_hash_mod_key len offset) s;
    assert(forall (i:nat{i < length s}). same_hash_mod_key len offset (index s i));
    let aux (i:nat{i < length s}) :
      Lemma
      (requires (same_hash_mod_key len offset (index s i)))
      (ensures (binding_neq b (index s i)))
      [SMTPat (index s i)] = ()
    in
    assert(forall (i:nat{i < length s}). binding_neq b (index s i));
    forall_index_equiv_list_for_all (binding_neq b) s;
    assert(for_all (binding_neq b) s); // TARGET
    //
    assert(forall (i:nat{i < length slots'}). index slots' i == index slots (i+1)); // Triggers instantiations
    binding_in_previous_slot_implies_neq len i b (offset+1) slots';
    for_all_append (binding_neq b) s (flatten slots')    
#pop-options

val partial_hash_map_s_inv_implies_assoc_list_lem
  (#t : Type0) (len : usize{len > 0}) (offset : usize)
  (hm : hash_map_s t{offset + length hm <= usize_max}) :
  Lemma
  (requires (
    partial_hash_map_s_inv len offset hm))
  (ensures (assoc_list_inv (flatten hm)))
  (decreases (length hm + length (flatten hm)))

#push-options "--fuel 1"
let rec partial_hash_map_s_inv_implies_assoc_list_lem #t len offset hm =
  match hm with
  | [] -> ()
  | slot :: hm' ->
    assert(flatten hm == slot @ flatten hm');
    assert(forall (i:nat{i < length hm'}). index hm' i == index hm (i+1)); // Triggers instantiations
    match slot with
    | [] ->
      assert(flatten hm == flatten hm');
      assert(partial_hash_map_s_inv len (offset+1) hm'); // Triggers instantiations
      partial_hash_map_s_inv_implies_assoc_list_lem len (offset+1) hm'
    | x :: slot' ->
      assert(flatten (slot' :: hm') == slot' @ flatten hm');
      let hm'' = slot' :: hm' in
      assert(forall (i:nat{0 < i /\ i < length hm''}). index hm'' i == index hm i); // Triggers instantiations
      assert(forall (i:nat{0 < i /\ i < length hm''}). slot_s_inv len (offset + i) (index hm'' i));
      assert(index hm 0 == slot); // Triggers instantiations
      assert(slot_s_inv len offset slot);
      assert(slot_s_inv len offset slot');
      assert(partial_hash_map_s_inv len offset hm'');
      partial_hash_map_s_inv_implies_assoc_list_lem len offset (slot' :: hm');
      // Proving that the key in `x` is different from all the other keys in
      // the flattened map
      assert(for_all (binding_neq x) slot');
      for_all_append (binding_neq x) slot' (flatten hm');
      assert(partial_hash_map_s_inv len (offset+1) hm');
      binding_in_previous_slot_implies_neq #t len offset x (offset+1) hm';
      assert(for_all (binding_neq x) (flatten hm'));
      assert(for_all (binding_neq x) (flatten (slot' :: hm')))
#pop-options

val hash_map_s_inv_implies_assoc_list_lem
  (#t : Type0) (hm : hash_map_s t) :
  Lemma (requires (hash_map_s_inv hm))
  (ensures (assoc_list_inv (flatten hm)))

let hash_map_s_inv_implies_assoc_list_lem #t hm =
  partial_hash_map_s_inv_implies_assoc_list_lem (length hm) 0 hm

val hash_map_t_base_inv_implies_assoc_list_lem
  (#t : Type0) (hm : hash_map_t t):
  Lemma (requires (hash_map_t_base_inv hm))
  (ensures (assoc_list_inv (hash_map_t_al_v hm)))

let hash_map_t_base_inv_implies_assoc_list_lem #t hm =
  hash_map_s_inv_implies_assoc_list_lem (hash_map_t_v hm)

/// For some reason, we can't write the below [forall] directly in the [ensures]
/// clause of the next lemma: it makes Z3 fails even with a huge rlimit.
/// I have no idea what's going on.
let hash_map_is_assoc_list
  (#t : Type0) (ntable : hash_map_t t{length ntable.hash_map_slots > 0})
  (al : assoc_list t) : Type0 =
  (forall (k:key). hash_map_t_find_s ntable k == assoc_list_find k al)

let partial_hash_map_s_find
  (#t : Type0) (len : usize{len > 0}) (offset : usize)
  (hm : hash_map_s_nes t{offset + length hm = len})
  (k : key{hash_mod_key k len >= offset}) : option t =
  let i = hash_mod_key k len in
  let slot = index hm (i - offset) in
  slot_s_find k slot

val not_same_hash_key_not_found_in_slot
  (#t : Type0) (len : usize{len > 0})
  (k : key)
  (i : usize)
  (slot : slot_s t) :
  Lemma
  (requires (
    hash_mod_key k len <> i /\
    slot_s_inv len i slot))
  (ensures (slot_s_find k slot == None))

#push-options "--fuel 1"
let rec not_same_hash_key_not_found_in_slot #t len k i slot =
  match slot with
  | [] -> ()
  | (k',v) :: slot' -> not_same_hash_key_not_found_in_slot len k i slot'
#pop-options

/// Small variation of [binding_in_previous_slot_implies_neq]: if the hash of
/// a key links it to a previous slot, it can't be found in the slots after.
val key_in_previous_slot_implies_not_found
  (#t : Type0) (len : usize{len > 0})
  (k : key)
  (offset : usize)
  (slots : hash_map_s t{offset + length slots = len}) :
  Lemma
  (requires (
    // The binding comes from a slot not in [slots]
    hash_mod_key k len < offset /\
    // The slots are the well-formed suffix of a hash map
    partial_hash_map_s_inv len offset slots))
  (ensures (
    assoc_list_find k (flatten slots) == None))
  (decreases slots)

#push-options "--fuel 1"
let rec key_in_previous_slot_implies_not_found #t len k offset slots =
  match slots with
  | [] -> ()
  | slot :: slots' ->
    find_append (same_key k) slot (flatten slots');
    assert(index slots 0 == slot); // Triggers instantiations
    not_same_hash_key_not_found_in_slot #t len k offset slot;
    assert(assoc_list_find k slot == None);
    assert(forall (i:nat{i < length slots'}). index slots' i == index slots (i+1)); // Triggers instantiations
    key_in_previous_slot_implies_not_found len k (offset+1) slots'
#pop-options  

val partial_hash_map_s_is_assoc_list_lem
  (#t : Type0) (len : usize{len > 0}) (offset : usize)
  (hm : hash_map_s_nes t{offset + length hm = len})
  (k : key{hash_mod_key k len >= offset}) :
  Lemma
  (requires (
    partial_hash_map_s_inv len offset hm))
  (ensures (
    partial_hash_map_s_find len offset hm k == assoc_list_find k (flatten hm)))
  (decreases hm)
//  (decreases (length hm + length (flatten hm)))

#push-options "--fuel 1"
let rec partial_hash_map_s_is_assoc_list_lem #t len offset hm k =
  match hm with
  | [] -> ()
  | slot :: hm' ->
    let h = hash_mod_key k len in
    let i = h - offset in
    if i = 0 then
      begin
      // We must look in the current slot
      assert(partial_hash_map_s_find len offset hm k == slot_s_find k slot);
      find_append (same_key k) slot (flatten hm');
      assert(forall (i:nat{i < length hm'}). index hm' i == index hm (i+1)); // Triggers instantiations
      key_in_previous_slot_implies_not_found #t len k (offset+1) hm';
      assert( // Of course, writing `== None` doesn't work...
        match find (same_key k) (flatten hm') with
        | None -> True
        | Some _ -> False);
      assert(
        find (same_key k) (flatten hm) ==
        begin match find (same_key k) slot with
        | Some x -> Some x
        | None -> find (same_key k) (flatten hm')
        end);
      ()
      end
    else
      begin
      // We must ignore the current slot
      assert(partial_hash_map_s_find len offset hm k ==
             partial_hash_map_s_find len (offset+1) hm' k);
      find_append (same_key k) slot (flatten hm');
      assert(index hm 0 == slot); // Triggers instantiations
      not_same_hash_key_not_found_in_slot #t len k offset slot;
      assert(forall (i:nat{i < length hm'}). index hm' i == index hm (i+1)); // Triggers instantiations
      partial_hash_map_s_is_assoc_list_lem #t len (offset+1) hm' k
      end
#pop-options

val hash_map_is_assoc_list_lem (#t : Type0) (hm : hash_map_t t) :
  Lemma (requires (hash_map_t_base_inv hm))
  (ensures (hash_map_is_assoc_list hm (hash_map_t_al_v hm)))

let hash_map_is_assoc_list_lem #t hm =
  let aux (k:key) :
    Lemma (hash_map_t_find_s hm k == assoc_list_find k (hash_map_t_al_v hm))
    [SMTPat (hash_map_t_find_s hm k)] =
    let hm_v = hash_map_t_v hm in
    let len = length hm_v in
    partial_hash_map_s_is_assoc_list_lem #t len 0 hm_v k
  in
  ()

/// The final lemma about [move_elements]: calling it on an empty hash table moves
/// all the elements to this empty table.
val hash_map_move_elements_fwd_back_lem
  (t : Type0) (ntable : hash_map_t t) (slots : vec (list_t t)) :
  Lemma
  (requires (
    let al = flatten (slots_t_v slots) in
    hash_map_t_base_inv ntable /\
    length al <= usize_max /\
    assoc_list_inv al /\
    // The table is empty
    hash_map_t_len_s ntable = 0 /\
    (forall (k:key). hash_map_t_find_s ntable k  == None)))
  (ensures (
    let al = flatten (slots_t_v slots) in
    match hash_map_move_elements_fwd_back t ntable slots 0,
          hash_map_move_elements_s_flat (hash_map_t_v ntable) al
    with
    | Return (ntable', _), Return ntable'_v ->
      // The invariant is preserved
      hash_map_t_base_inv ntable' /\
      // We preserved the parameters
      hash_map_t_same_params ntable' ntable /\
      // The table has the same number of slots
      length ntable'.hash_map_slots = length ntable.hash_map_slots /\
      // The count is good
      hash_map_t_len_s ntable' = length al /\
      // The table can be linked to its model (we need this only to reveal
      // "pretty" functional lemmas to the user in the fsti - so that we
      // can write lemmas with SMT patterns - this is very F* specific)
      hash_map_t_v ntable' == ntable'_v /\
      // The new table contains exactly all the bindings from the slots
      // Rk.: see the comment for [hash_map_is_assoc_list]
      hash_map_is_assoc_list ntable' al
    | _ -> False // We can only succeed
    ))

// Weird, dirty things happen below.
// Manually unfolding some postconditions allowed to make the proof pass,
// and also revealed the reason why some proofs failed with "Unknown assertion
// failed" (resulting in the call to [flatten_0_is_flatten] for instance).
// I think manually unfolding the postconditions allowed to account for the
// lack of ifuel (this kind of proofs is annoying, really).
#restart-solver
#push-options "--z3rlimit 100"
let hash_map_move_elements_fwd_back_lem t ntable slots =
  let ntable_v = hash_map_t_v ntable in
  let slots_v = slots_t_v slots in
  let al = flatten slots_v in
  hash_map_move_elements_fwd_back_lem_refin t ntable slots 0;
  begin
  match hash_map_move_elements_fwd_back t ntable slots 0,
        hash_map_move_elements_s ntable_v slots_v 0
  with
  | Fail _, Fail _ -> ()
  | Return (ntable', _), Return ntable'_v ->
    assert(hash_map_t_base_inv ntable');
    assert(hash_map_t_v ntable' == ntable'_v)
  | _ -> assert(False)
  end;
  hash_map_move_elements_s_lem_refin_flat ntable_v slots_v 0;
  begin
  match hash_map_move_elements_s ntable_v slots_v 0,
        hash_map_move_elements_s_flat ntable_v (flatten_i slots_v 0)
  with
  | Fail _, Fail _ -> ()
  | Return hm, Return hm' -> assert(hm == hm')
  | _ -> assert(False)
  end;
  flatten_0_is_flatten slots_v; // flatten_i slots_v 0 == flatten slots_v
  hash_map_move_elements_s_flat_lem ntable_v al;
  match hash_map_move_elements_fwd_back t ntable slots 0,
        hash_map_move_elements_s_flat ntable_v al
  with
  | Return (ntable', _), Return ntable'_v ->
    assert(hash_map_t_base_inv ntable');
    assert(length ntable'.hash_map_slots = length ntable.hash_map_slots);
    assert(hash_map_t_len_s ntable' = length al);
    assert(hash_map_t_v ntable' == ntable'_v);
    assert(hash_map_is_assoc_list ntable' al)
  | _ -> assert(False)
#pop-options

(*** try_resize *)

/// High-level model 1.
/// This is one is slightly "crude": we just simplify a bit the function.

let hash_map_try_resize_s_simpl
  (#t : Type0)
  (hm : hash_map_t t) :
  Pure  (result (hash_map_t t))
  (requires (
    let (divid, divis) = hm.hash_map_max_load_factor in
    divid > 0 /\ divis > 0))
  (ensures (fun _ -> True)) =
  let capacity = length hm.hash_map_slots in
  let (divid, divis) = hm.hash_map_max_load_factor in
  if capacity <= (usize_max / 2) / divid then
    let ncapacity : usize = capacity * 2 in
    begin match hash_map_new_with_capacity_fwd t ncapacity divid divis with
    | Fail e -> Fail e
    | Return ntable ->
      match hash_map_move_elements_fwd_back t ntable hm.hash_map_slots 0 with
      | Fail e -> Fail e
      | Return (ntable', _) ->
        let hm =
          { hm with hash_map_slots = ntable'.hash_map_slots;
                    hash_map_max_load = ntable'.hash_map_max_load }
        in
        Return hm
    end
  else Return hm

// I had made a mistake when writing the above definition: I had used `ntable`
// instead of `ntable'` in the last assignments. Of course, Z3 failed to prove
// the equality `hm1 == hm2`, and as I couldn't spot immediately the mistake,
// I had to resort to the good old "test every field" trick, by replacing
// `hm1 == hm2` with:
//   ```
//    hm1.hash_map_num_entries == hm2.hash_map_num_entries /\
//    hm1.hash_map_max_load_factor == hm2.hash_map_max_load_factor /\
//    hm1.hash_map_max_load == hm2.hash_map_max_load /\
//    hm1.hash_map_slots == hm2.hash_map_slots
//    ```
// Once again, if I had had access to a context, I would have seen the error
// immediately.
val hash_map_try_resize_fwd_back_lem_refin
  (t : Type0) (self : hash_map_t t) :
  Lemma
  (requires (
    let (divid, divis) = self.hash_map_max_load_factor in
    divid > 0 /\ divis > 0))
  (ensures (
    match hash_map_try_resize_fwd_back t self,
          hash_map_try_resize_s_simpl self
    with
    | Fail _, Fail _ -> True
    | Return hm1, Return hm2 -> hm1 == hm2
    | _ -> False))

let hash_map_try_resize_fwd_back_lem_refin t self = ()

/// Isolating arithmetic proofs

let gt_lem0 (n m q : nat) :
  Lemma (requires (m > 0 /\ n > q))
  (ensures (n * m > q * m)) = ()

let ge_lem0 (n m q : nat) :
  Lemma (requires (m > 0 /\ n >= q))
  (ensures (n * m >= q * m)) = ()

let gt_ge_trans (n m p : nat) :
  Lemma (requires (n > m /\ m >= p)) (ensures (n > p)) = ()

let ge_trans (n m p : nat) :
  Lemma (requires (n >= m /\ m >= p)) (ensures (n >= p)) = ()

#push-options "--z3rlimit 200"
let gt_lem1 (n m q : nat) :
  Lemma (requires (m > 0 /\ n > q / m)) (ensures (n * m > q)) =
  assert(n >= q / m + 1);
  ge_lem0 n m (q / m + 1);
  assert(n * m >= (q / m) * m + m)
#pop-options

let gt_lem2 (n m p q : nat) :
  Lemma (requires (m > 0 /\ p > 0 /\ n > (q / m) / p)) (ensures (n * m * p > q)) =
  gt_lem1 n p (q / m);
  assert(n * p > q / m);
  gt_lem1 (n * p) m q

let ge_lem1 (n m q : nat) :
  Lemma (requires (n >= m /\ q > 0))
  (ensures (n / q >= m / q)) =
  FStar.Math.Lemmas.lemma_div_le m n q

#restart-solver
#push-options "--z3rlimit 200"
let times_divid_lem (n m p : pos) : Lemma ((n * m) / p >= n * (m / p))
  =
  FStar.Math.Lemmas.multiply_fractions m p;
  assert(m >= (m / p) * p);
  assert(n * m >= n * (m / p) * p); //
  ge_lem1 (n * m) (n * (m / p) * p) p;
  assert((n * m) / p >= (n * (m / p) * p) / p);
  assert(n * (m / p) * p = (n * (m / p)) * p);
  FStar.Math.Lemmas.cancel_mul_div (n * (m / p)) p;
  assert(((n * (m / p)) * p) / p = n * (m / p))
#pop-options

/// The good old arithmetic proofs and their unstability...
/// At some point I thought it was stable because it worked with `--quake 100`.
/// Of course, it broke the next time I checked the file...
/// It seems things are ok when we check this proof on its own, but not when
/// it is sent at the same time as the one above (though we put #restart-solver!).
/// I also tried `--quake 1/100` to no avail: it seems that when Z3 decides to
/// fail the first one, it fails them all. I inserted #restart-solver before
/// the previous lemma to see if it had an effect (of course not).
val new_max_load_lem
  (len : usize) (capacity : usize{capacity > 0})
  (divid : usize{divid > 0}) (divis : usize{divis > 0}) :
  Lemma
  (requires (
    let max_load = (capacity * divid) / divis in
    let ncapacity = 2 * capacity in
    let nmax_load = (ncapacity * divid) / divis in
    capacity > 0 /\ 0 < divid /\ divid < divis /\
    capacity * divid >= divis /\
    len = max_load + 1))
  (ensures (
    let max_load = (capacity * divid) / divis in
    let ncapacity = 2 * capacity in
    let nmax_load = (ncapacity * divid) / divis in
    len <= nmax_load))

let mul_assoc (a b c : nat) : Lemma (a * b * c == a * (b * c)) = ()

let ge_lem2 (a b c d : nat) : Lemma (requires (a >= b + c /\ c >= d)) (ensures (a >= b + d)) = ()
let ge_div_lem1 (a b : nat) : Lemma (requires (a >= b /\ b > 0)) (ensures (a / b >= 1)) = ()

#restart-solver
#push-options "--z3rlimit 100 --z3cliopt smt.arith.nl=false"
let new_max_load_lem len capacity divid divis =
  FStar.Math.Lemmas.paren_mul_left 2 capacity divid;
  mul_assoc 2 capacity divid;
  // The following assertion often breaks though it is given by the above
  // lemma. I really don't know what to do (I deactivated non-linear
  // arithmetic and added the previous lemma call, moved the assertion up,
  // boosted the rlimit...).
  assert(2 * capacity * divid == 2 * (capacity * divid));
  let max_load = (capacity * divid) / divis in
  let ncapacity = 2 * capacity in
  let nmax_load = (ncapacity * divid) / divis in
  assert(nmax_load = (2 * capacity * divid) / divis);
  times_divid_lem 2 (capacity * divid) divis;
  assert((2 * (capacity * divid)) / divis >= 2 * ((capacity * divid) / divis));
  assert(nmax_load >= 2 * ((capacity * divid) / divis));
  assert(nmax_load >= 2 * max_load);
  assert(nmax_load >= max_load + max_load);
  ge_div_lem1 (capacity * divid) divis;
  ge_lem2 nmax_load max_load max_load 1;
  assert(nmax_load >= max_load + 1)
#pop-options

val hash_map_try_resize_s_simpl_lem (#t : Type0) (hm : hash_map_t t) :
  Lemma
  (requires (
    // The base invariant is satisfied
    hash_map_t_base_inv hm /\
    // However, the "full" invariant is broken, as we call [try_resize]
    // only if the current number of entries is > the max load.
    // 
    // There are two situations:
    // - either we just reached the max load
    // - or we were already saturated and can't resize
    (let (dividend, divisor) = hm.hash_map_max_load_factor in
     hm.hash_map_num_entries == hm.hash_map_max_load + 1 \/
     length hm.hash_map_slots * 2 * dividend > usize_max)
  ))
  (ensures (
    match hash_map_try_resize_s_simpl hm with
    | Fail _ -> False
    | Return hm' ->
      // The full invariant is now satisfied (the full invariant is "base
      // invariant" + the map is not overloaded (or can't be resized because
      // already too big)
      hash_map_t_inv hm' /\
      // It contains the same bindings as the initial map
      (forall (k:key). hash_map_t_find_s hm' k == hash_map_t_find_s hm k)))

#restart-solver
#push-options "--z3rlimit 400"
let hash_map_try_resize_s_simpl_lem #t hm =
  let capacity = length hm.hash_map_slots in
  let (divid, divis) = hm.hash_map_max_load_factor in
  if capacity <= (usize_max / 2) / divid then
    begin
    let ncapacity : usize = capacity * 2 in
    assert(ncapacity * divid <= usize_max);
    assert(hash_map_t_len_s hm = hm.hash_map_max_load + 1);
    new_max_load_lem (hash_map_t_len_s hm) capacity divid divis;
    hash_map_new_with_capacity_fwd_lem t ncapacity divid divis;
    match hash_map_new_with_capacity_fwd t ncapacity divid divis with
    | Fail _ -> ()
    | Return ntable ->
      let slots = hm.hash_map_slots in
      let al = flatten (slots_t_v slots) in
      // Proving that: length al = hm.hash_map_num_entries
      assert(al == flatten (map slot_t_v slots));
      assert(al == flatten (map list_t_v slots));
      assert(hash_map_t_al_v hm == flatten (hash_map_t_v hm));
      assert(hash_map_t_al_v hm == flatten (map list_t_v hm.hash_map_slots));
      assert(al == hash_map_t_al_v hm);
      assert(hash_map_t_base_inv ntable);
      assert(length al = hm.hash_map_num_entries);
      assert(length al <= usize_max);
      hash_map_t_base_inv_implies_assoc_list_lem hm;
      assert(assoc_list_inv al);
      assert(hash_map_t_len_s ntable = 0);
      assert(forall (k:key). hash_map_t_find_s ntable k  == None);
      hash_map_move_elements_fwd_back_lem t ntable hm.hash_map_slots;
      match hash_map_move_elements_fwd_back t ntable hm.hash_map_slots 0 with
      | Fail _ -> ()
      | Return (ntable', _) ->
        hash_map_is_assoc_list_lem hm;
        assert(hash_map_is_assoc_list hm (hash_map_t_al_v hm));
        let hm' =
          { hm with hash_map_slots = ntable'.hash_map_slots;
                    hash_map_max_load = ntable'.hash_map_max_load }
        in
        assert(hash_map_t_base_inv ntable');
        assert(hash_map_t_base_inv hm');
        assert(hash_map_t_len_s hm' = hash_map_t_len_s hm);
        new_max_load_lem (hash_map_t_len_s hm') capacity divid divis;
        assert(hash_map_t_len_s hm' <= hm'.hash_map_max_load); // Requires a lemma
        assert(hash_map_t_inv hm')
    end
  else
    begin
    gt_lem2 capacity 2 divid usize_max;
    assert(capacity * 2 * divid > usize_max)
    end
#pop-options

let hash_map_t_same_bindings  (#t : Type0) (hm hm' : hash_map_t_nes t) : Type0 =
  forall (k:key). hash_map_t_find_s hm k == hash_map_t_find_s hm' k

/// The final lemma about [try_resize]
val hash_map_try_resize_fwd_back_lem (#t : Type0) (hm : hash_map_t t) :
  Lemma
  (requires (
    hash_map_t_base_inv hm /\
    // However, the "full" invariant is broken, as we call [try_resize]
    // only if the current number of entries is > the max load.
    // 
    // There are two situations:
    // - either we just reached the max load
    // - or we were already saturated and can't resize
    (let (dividend, divisor) = hm.hash_map_max_load_factor in
     hm.hash_map_num_entries == hm.hash_map_max_load + 1 \/
     length hm.hash_map_slots * 2 * dividend > usize_max)))
  (ensures (
    match hash_map_try_resize_fwd_back t hm with
    | Fail _ -> False
    | Return hm' ->
      // The full invariant is now satisfied (the full invariant is "base
      // invariant" + the map is not overloaded (or can't be resized because
      // already too big)
      hash_map_t_inv hm' /\
      // The length is the same
      hash_map_t_len_s hm' = hash_map_t_len_s hm /\
      // It contains the same bindings as the initial map
      hash_map_t_same_bindings hm' hm))

let hash_map_try_resize_fwd_back_lem #t hm =
  hash_map_try_resize_fwd_back_lem_refin t hm;
  hash_map_try_resize_s_simpl_lem hm

(*** insert *)

/// The high-level model (very close to the original function: we don't need something
/// very high level, just to clean it a bit)
let hash_map_insert_s
  (#t : Type0) (self : hash_map_t t) (key : usize) (value : t) :
  result (hash_map_t t) =
  match hash_map_insert_no_resize_fwd_back t self key value with
  | Fail e -> Fail e
  | Return hm' ->
    if hash_map_t_len_s hm' > hm'.hash_map_max_load then
      hash_map_try_resize_fwd_back t hm'
    else Return hm'

val hash_map_insert_fwd_back_lem_refin
  (t : Type0) (self : hash_map_t t) (key : usize) (value : t) :
  Lemma (requires True)
  (ensures (
    match hash_map_insert_fwd_back t self key value,
          hash_map_insert_s self key value
    with
    | Fail _, Fail _ -> True
    | Return hm1, Return hm2 -> hm1 == hm2
    | _ -> False))

let hash_map_insert_fwd_back_lem_refin t self key value = ()

/// Helper
let hash_map_insert_fwd_back_bindings_lem
  (t : Type0) (self : hash_map_t_nes t) (key : usize) (value : t)
  (hm' hm'' : hash_map_t_nes t) :
  Lemma
  (requires (
     hash_map_s_updated_binding (hash_map_t_v self) key
                                (Some value) (hash_map_t_v hm') /\
     hash_map_t_same_bindings hm' hm''))
  (ensures (
     hash_map_s_updated_binding (hash_map_t_v self) key
                                (Some value) (hash_map_t_v hm'')))
  = ()

val hash_map_insert_fwd_back_lem_aux
  (#t : Type0) (self : hash_map_t t) (key : usize) (value : t) :
  Lemma (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_insert_fwd_back t self key value with
    | Fail _ ->
      // We can fail only if:
      // - the key is not in the map and we need to add it
      // - we are already saturated
      hash_map_t_len_s self = usize_max /\
      None? (hash_map_t_find_s self key)
    | Return hm' ->
      // The invariant is preserved
      hash_map_t_inv hm' /\
      // [key] maps to [value] and the other bindings are preserved
      hash_map_s_updated_binding (hash_map_t_v self) key (Some value) (hash_map_t_v hm') /\
      // The length is incremented, iff we inserted a new key
      (match hash_map_t_find_s self key with
       | None -> hash_map_t_len_s hm' = hash_map_t_len_s self + 1
       | Some _ -> hash_map_t_len_s hm' = hash_map_t_len_s self)))

#restart-solver
#push-options "--z3rlimit 200"
let hash_map_insert_fwd_back_lem_aux #t self key value =
  hash_map_insert_no_resize_fwd_back_lem_s t self key value;
  hash_map_insert_no_resize_s_lem (hash_map_t_v self) key value;
  match hash_map_insert_no_resize_fwd_back t self key value with
  | Fail _ -> ()
  | Return hm' ->
    // Expanding the post of [hash_map_insert_no_resize_fwd_back_lem_s]
    let self_v = hash_map_t_v self in
    let hm'_v = Return?.v (hash_map_insert_no_resize_s self_v key value) in
    assert(hash_map_t_base_inv hm');
    assert(hash_map_t_same_params hm' self);
    assert(hash_map_t_v hm' == hm'_v);
    assert(hash_map_s_len hm'_v == hash_map_t_len_s hm');
    // Expanding the post of [hash_map_insert_no_resize_s_lem]
    assert(insert_post self_v key value hm'_v);
    // Expanding [insert_post]
    assert(hash_map_s_inv hm'_v);
    assert(
      match hash_map_s_find self_v key with
      | None -> hash_map_s_len hm'_v = hash_map_s_len self_v + 1
      | Some _ -> hash_map_s_len hm'_v = hash_map_s_len self_v);
    if hash_map_t_len_s hm' > hm'.hash_map_max_load then
      begin
      hash_map_try_resize_fwd_back_lem hm';
      // Expanding the post of [hash_map_try_resize_fwd_back_lem]
      let hm'' = Return?.v (hash_map_try_resize_fwd_back t hm') in
      assert(hash_map_t_inv hm'');
      let hm''_v = hash_map_t_v hm'' in
      assert(forall k. hash_map_t_find_s hm'' k == hash_map_t_find_s hm' k);
      assert(hash_map_t_len_s hm'' = hash_map_t_len_s hm'); // TODO
      // Proving the post
      assert(hash_map_t_inv hm'');
      hash_map_insert_fwd_back_bindings_lem t self key value hm' hm'';
      assert(
        match hash_map_t_find_s self key with
         | None -> hash_map_t_len_s hm'' = hash_map_t_len_s self + 1
         | Some _ -> hash_map_t_len_s hm'' = hash_map_t_len_s self)
      end
    else ()
#pop-options

let hash_map_insert_fwd_back_lem #t self key value =
  hash_map_insert_fwd_back_lem_aux #t self key value

(*** contains_key *)

(**** contains_key_in_list *)

val hash_map_contains_key_in_list_fwd_lem
  (#t : Type0) (key : usize) (ls : list_t t) :
  Lemma
  (ensures (
    match hash_map_contains_key_in_list_fwd t key ls with
    | Fail _ -> False
    | Return b ->
      b = Some? (slot_t_find_s key ls)))


#push-options "--fuel 1"
let rec hash_map_contains_key_in_list_fwd_lem #t key ls =
  match ls with
  | ListCons ckey x ls0 ->
    let b = ckey = key in
    if b
    then ()
    else
      begin
      hash_map_contains_key_in_list_fwd_lem key ls0;
      match hash_map_contains_key_in_list_fwd t key ls0 with
      | Fail _ -> ()
      | Return b0 -> ()
      end
  | ListNil -> ()
#pop-options

(**** contains_key *)

val hash_map_contains_key_fwd_lem_aux
  (#t : Type0) (self : hash_map_t_nes t) (key : usize) :
  Lemma
  (ensures (
    match hash_map_contains_key_fwd t self key with
    | Fail _ -> False
    | Return b -> b = Some? (hash_map_t_find_s self key)))

let hash_map_contains_key_fwd_lem_aux #t self key =
  begin match hash_key_fwd key with
  | Fail _ -> ()
  | Return i ->
    let v = self.hash_map_slots in
    let i0 = vec_len (list_t t) v in
    begin match usize_rem i i0 with
    | Fail _ -> ()
    | Return hash_mod ->
      begin match vec_index_fwd (list_t t) v hash_mod with
      | Fail _ -> ()
      | Return l ->
        hash_map_contains_key_in_list_fwd_lem key l;
        begin match hash_map_contains_key_in_list_fwd t key l with
        | Fail _ -> ()
        | Return b -> ()
        end
      end
    end
  end

/// The lemma in the .fsti
let hash_map_contains_key_fwd_lem #t self key =
  hash_map_contains_key_fwd_lem_aux #t self key

(*** get *)

(**** get_in_list *)

val hash_map_get_in_list_fwd_lem
  (#t : Type0) (key : usize) (ls : list_t t) :
  Lemma
  (ensures (
    match hash_map_get_in_list_fwd t key ls, slot_t_find_s key ls with
    | Fail _, None -> True
    | Return x, Some x' -> x == x'
    | _ -> False))

#push-options "--fuel 1"
let rec hash_map_get_in_list_fwd_lem #t key ls =
  begin match ls with
  | ListCons ckey cvalue ls0 ->
    let b = ckey = key in
    if b
    then ()
    else
      begin
      hash_map_get_in_list_fwd_lem key ls0;
      match hash_map_get_in_list_fwd t key ls0 with
      | Fail _ -> ()
      | Return x -> ()
      end
  | ListNil -> ()
  end
#pop-options

(**** get *)

val hash_map_get_fwd_lem_aux
  (#t : Type0) (self : hash_map_t_nes t) (key : usize) :
  Lemma
  (ensures (
    match hash_map_get_fwd t self key, hash_map_t_find_s self key with
    | Fail _, None -> True
    | Return x, Some x' -> x == x'
    | _ -> False))

let hash_map_get_fwd_lem_aux #t self key =
  begin match hash_key_fwd key with
  | Fail _ -> ()
  | Return i ->
    let v = self.hash_map_slots in
    let i0 = vec_len (list_t t) v in
    begin match usize_rem i i0 with
    | Fail _ -> ()
    | Return hash_mod ->
      begin match vec_index_fwd (list_t t) v hash_mod with
      | Fail _ -> ()
      | Return l ->
        begin
        hash_map_get_in_list_fwd_lem key l;
        match hash_map_get_in_list_fwd t key l with
        | Fail _ -> ()
        | Return x -> ()
        end
      end
    end
  end

/// .fsti
let hash_map_get_fwd_lem #t self key = hash_map_get_fwd_lem_aux #t self key

(*** get_mut'fwd *)


(**** get_mut_in_list'fwd *)

val hash_map_get_mut_in_list_fwd_lem
  (#t : Type0) (key : usize) (ls : list_t t) :
  Lemma
  (ensures (
    match hash_map_get_mut_in_list_fwd t key ls, slot_t_find_s key ls with
    | Fail _, None -> True
    | Return x, Some x' -> x == x'
    | _ -> False))

#push-options "--fuel 1"
let rec hash_map_get_mut_in_list_fwd_lem #t key ls =
  begin match ls with
  | ListCons ckey cvalue ls0 ->
    let b = ckey = key in
    if b
    then ()
    else
      begin
      hash_map_get_mut_in_list_fwd_lem key ls0;
      match hash_map_get_mut_in_list_fwd t key ls0 with
      | Fail _ -> ()
      | Return x -> ()
      end
  | ListNil -> ()
  end
#pop-options

(**** get_mut'fwd *)

val hash_map_get_mut_fwd_lem_aux
  (#t : Type0) (self : hash_map_t_nes t) (key : usize) :
  Lemma
  (ensures (
    match hash_map_get_mut_fwd t self key, hash_map_t_find_s self key with
    | Fail _, None -> True
    | Return x, Some x' -> x == x'
    | _ -> False))

let hash_map_get_mut_fwd_lem_aux #t self key =
  begin match hash_key_fwd key with
  | Fail _ -> ()
  | Return i ->
    let v = self.hash_map_slots in
    let i0 = vec_len (list_t t) v in
    begin match usize_rem i i0 with
    | Fail _ -> ()
    | Return hash_mod ->
      begin match vec_index_fwd (list_t t) v hash_mod with
      | Fail _ -> ()
      | Return l ->
        begin
        hash_map_get_mut_in_list_fwd_lem key l;
        match hash_map_get_mut_in_list_fwd t key l with
        | Fail _ -> ()
        | Return x -> ()
        end
      end
    end
  end

let hash_map_get_mut_fwd_lem #t self key =
  hash_map_get_mut_fwd_lem_aux #t self key

(*** get_mut'back *)

(**** get_mut_in_list'back *)

val hash_map_get_mut_in_list_back_lem
  (#t : Type0) (key : usize) (ls : list_t t) (ret : t) :
  Lemma
  (requires (Some? (slot_t_find_s key ls)))
  (ensures (
    match hash_map_get_mut_in_list_back t key ls ret with
    | Fail _ -> False
    | Return ls' -> list_t_v ls' == find_update (same_key key) (list_t_v ls) (key,ret)
    | _ -> False))

#push-options "--fuel 1"
let rec hash_map_get_mut_in_list_back_lem #t key ls ret =
  begin match ls with
  | ListCons ckey cvalue ls0 ->
    let b = ckey = key in
    if b
    then let ls1 = ListCons ckey ret ls0 in ()
    else
      begin
      hash_map_get_mut_in_list_back_lem key ls0 ret;
      match hash_map_get_mut_in_list_back t key ls0 ret with
      | Fail _ -> ()
      | Return l -> let ls1 = ListCons ckey cvalue l in ()
      end
  | ListNil -> ()
  end
#pop-options

(**** get_mut'back *)

/// Refinement lemma
val hash_map_get_mut_back_lem_refin
  (#t : Type0) (self : hash_map_t t{length self.hash_map_slots > 0})
  (key : usize) (ret : t) :
  Lemma
  (requires (Some? (hash_map_t_find_s self key)))
  (ensures (
    match hash_map_get_mut_back t self key ret with
    | Fail _ -> False
    | Return hm' ->
      hash_map_t_v hm' == hash_map_insert_no_fail_s (hash_map_t_v self) key ret))

let hash_map_get_mut_back_lem_refin #t self key ret =
  begin match hash_key_fwd key with
  | Fail _ -> ()
  | Return i ->
    let i0 = self.hash_map_num_entries in
    let p = self.hash_map_max_load_factor in
    let i1 = self.hash_map_max_load in
    let v = self.hash_map_slots in
    let i2 = vec_len (list_t t) v in
    begin match usize_rem i i2 with
    | Fail _ -> ()
    | Return hash_mod ->
      begin match vec_index_mut_fwd (list_t t) v hash_mod with
      | Fail _ -> ()
      | Return l ->
        begin
        hash_map_get_mut_in_list_back_lem key l ret;
        match hash_map_get_mut_in_list_back t key l ret with
        | Fail _ -> ()
        | Return l0 ->
          begin match vec_index_mut_back (list_t t) v hash_mod l0 with
          | Fail _ -> ()
          | Return v0 -> let self0 = Mkhash_map_t i0 p i1 v0 in ()
          end
        end
      end
    end
  end

/// Final lemma
val hash_map_get_mut_back_lem_aux
  (#t : Type0) (hm : hash_map_t t)
  (key : usize) (ret : t) :
  Lemma
  (requires (
    hash_map_t_inv hm /\
    Some? (hash_map_t_find_s hm key)))
  (ensures (
    match hash_map_get_mut_back t hm key ret with
    | Fail _ -> False
    | Return hm' ->
      // Functional spec
      hash_map_t_v hm' == hash_map_insert_no_fail_s (hash_map_t_v hm) key ret /\
     // The invariant is preserved
     hash_map_t_inv hm' /\
     // The length is preserved
     hash_map_t_len_s hm' = hash_map_t_len_s hm /\
     // [key] maps to [value]
     hash_map_t_find_s hm' key == Some ret /\
     // The other bindings are preserved
     (forall k'. k' <> key ==> hash_map_t_find_s hm' k' == hash_map_t_find_s hm k')))

let hash_map_get_mut_back_lem_aux #t hm key ret =
  let hm_v = hash_map_t_v hm in
  hash_map_get_mut_back_lem_refin hm key ret;
  match hash_map_get_mut_back t hm key ret with
  | Fail _ -> assert(False)
  | Return hm' ->
    hash_map_insert_no_fail_s_lem hm_v key ret

/// .fsti
let hash_map_get_mut_back_lem #t hm key ret = hash_map_get_mut_back_lem_aux hm key ret

(*** remove'fwd *)

val hash_map_remove_from_list_fwd_lem
  (#t : Type0) (key : usize) (ls : list_t t) :
  Lemma
  (ensures (
    match hash_map_remove_from_list_fwd t key ls with
    | Fail _ -> False
    | Return opt_x ->
      opt_x == slot_t_find_s key ls /\
      (Some? opt_x ==> length (slot_t_v ls) > 0)))

#push-options "--fuel 1"
let rec hash_map_remove_from_list_fwd_lem #t key ls =
  begin match ls with
  | ListCons ckey x tl ->
    let b = ckey = key in
    if b
    then
      let mv_ls = mem_replace_fwd (list_t t) (ListCons ckey x tl) ListNil in
      begin match mv_ls with
      | ListCons i cvalue tl0 -> ()
      | ListNil -> ()
      end
    else
      begin
      hash_map_remove_from_list_fwd_lem key tl;
      match hash_map_remove_from_list_fwd t key tl with
      | Fail _ -> ()
      | Return opt -> ()
      end
  | ListNil -> ()
  end
#pop-options

val hash_map_remove_fwd_lem_aux
  (#t : Type0) (self : hash_map_t t) (key : usize) :
  Lemma
  (requires (
    // We need the invariant to prove that upon decrementing the entries counter,
    // the counter doesn't become negative
    hash_map_t_inv self))
  (ensures (
    match hash_map_remove_fwd t self key with
    | Fail _ -> False
    | Return opt_x -> opt_x == hash_map_t_find_s self key))

let hash_map_remove_fwd_lem_aux #t self key =
  begin match hash_key_fwd key with
  | Fail _ -> ()
  | Return i ->
    let i0 = self.hash_map_num_entries in
    let v = self.hash_map_slots in
    let i1 = vec_len (list_t t) v in
    begin match usize_rem i i1 with
    | Fail _ -> ()
    | Return hash_mod ->
      begin match vec_index_mut_fwd (list_t t) v hash_mod with
      | Fail _ -> ()
      | Return l ->
        begin
        hash_map_remove_from_list_fwd_lem key l;
        match hash_map_remove_from_list_fwd t key l with
        | Fail _ -> ()
        | Return x ->
          begin match x with
          | None -> ()
          | Some x0 ->
            begin
            assert(l == index v hash_mod);
            assert(length (list_t_v #t l) > 0);
            length_flatten_index (hash_map_t_v self) hash_mod;
            match usize_sub i0 1 with
            | Fail _ -> ()
            | Return _ -> ()
            end
          end
        end
      end
    end
  end

/// .fsti
let hash_map_remove_fwd_lem #t self key = hash_map_remove_fwd_lem_aux #t self key

(*** remove'back *)

(**** Refinement proofs *)

/// High-level model for [remove_from_list'back]
let hash_map_remove_from_list_s
  (#t : Type0) (key : usize) (ls : slot_s t) :
  slot_s t =
  filter_one (not_same_key key) ls

/// Refinement lemma
val hash_map_remove_from_list_back_lem_refin
  (#t : Type0) (key : usize) (ls : list_t t) :
  Lemma
  (ensures (
    match hash_map_remove_from_list_back t key ls with
    | Fail _ -> False
    | Return ls' ->
      list_t_v ls' == hash_map_remove_from_list_s key (list_t_v ls) /\
      // The length is decremented, iff the key was in the slot
      (let len = length (list_t_v ls) in
       let len' = length (list_t_v ls') in
       match slot_s_find key (list_t_v ls) with
       | None -> len = len'
       | Some _ -> len = len' + 1)))

#push-options "--fuel 1"
let rec hash_map_remove_from_list_back_lem_refin #t key ls =
  begin match ls with
  | ListCons ckey x tl ->
    let b = ckey = key in
    if b
    then
      let mv_ls = mem_replace_fwd (list_t t) (ListCons ckey x tl) ListNil in
      begin match mv_ls with
      | ListCons i cvalue tl0 -> ()
      | ListNil -> ()
      end
    else
      begin
      hash_map_remove_from_list_back_lem_refin key tl;
      match hash_map_remove_from_list_back t key tl with
      | Fail _ -> ()
      | Return l -> let ls0 = ListCons ckey x l in ()
      end
  | ListNil -> ()
  end
#pop-options

/// High-level model for [remove_from_list'back]
let hash_map_remove_s
  (#t : Type0) (self : hash_map_s_nes t) (key : usize) :
  hash_map_s t =
  let len = length self in
  let hash = hash_mod_key key len in
  let slot = index self hash in
  let slot' = hash_map_remove_from_list_s key slot in
  list_update self hash slot'

/// Refinement lemma
val hash_map_remove_back_lem_refin
  (#t : Type0) (self : hash_map_t_nes t) (key : usize) :
  Lemma
  (requires (
    // We need the invariant to prove that upon decrementing the entries counter,
    // the counter doesn't become negative
    hash_map_t_inv self))
  (ensures (
    match hash_map_remove_back t self key with
    | Fail _ -> False
    | Return hm' ->
      hash_map_t_same_params hm' self /\
      hash_map_t_v hm' == hash_map_remove_s (hash_map_t_v self) key /\
      // The length is decremented iff the key was in the map
      (let len = hash_map_t_len_s self in
       let len' = hash_map_t_len_s hm' in
       match hash_map_t_find_s self key with
       | None -> len = len'
       | Some _ -> len = len' + 1)))

let hash_map_remove_back_lem_refin #t self key =
  begin match hash_key_fwd key with
  | Fail _ -> ()
  | Return i ->
    let i0 = self.hash_map_num_entries in
    let p = self.hash_map_max_load_factor in
    let i1 = self.hash_map_max_load in
    let v = self.hash_map_slots in
    let i2 = vec_len (list_t t) v in
    begin match usize_rem i i2 with
    | Fail _ -> ()
    | Return hash_mod ->
      begin match vec_index_mut_fwd (list_t t) v hash_mod with
      | Fail _ -> ()
      | Return l ->
        begin
        hash_map_remove_from_list_fwd_lem key l;
        match hash_map_remove_from_list_fwd t key l with
        | Fail _ -> ()
        | Return x ->
          begin match x with
          | None ->
            begin
            hash_map_remove_from_list_back_lem_refin key l;
            match hash_map_remove_from_list_back t key l with
            | Fail _ -> ()
            | Return l0 ->
              begin
              length_flatten_update (slots_t_v v) hash_mod (list_t_v l0);
              match vec_index_mut_back (list_t t) v hash_mod l0 with
              | Fail _ -> ()
              | Return v0 -> ()
              end
            end
          | Some x0 ->
            begin
            assert(l == index v hash_mod);
            assert(length (list_t_v #t l) > 0);
            length_flatten_index (hash_map_t_v self) hash_mod;
            match usize_sub i0 1 with
            | Fail _ -> ()
            | Return i3 ->
              begin
              hash_map_remove_from_list_back_lem_refin key l;
              match hash_map_remove_from_list_back t key l with
              | Fail _ -> ()
              | Return l0 ->
                begin
                length_flatten_update (slots_t_v v) hash_mod (list_t_v l0);
                match vec_index_mut_back (list_t t) v hash_mod l0 with
                | Fail _ -> ()
                | Return v0 -> ()
                end
              end
            end
          end
        end
      end
    end
  end

(**** Invariants, high-level properties *)

val hash_map_remove_from_list_s_lem
  (#t : Type0) (k : usize) (slot : slot_s t) (len : usize{len > 0}) (i : usize) :
  Lemma
  (requires (slot_s_inv len i slot))
  (ensures (
    let slot' = hash_map_remove_from_list_s k slot in
    slot_s_inv len i slot' /\
    slot_s_find k slot' == None /\
    (forall (k':key{k' <> k}). slot_s_find k' slot' == slot_s_find k' slot) /\
    // This postcondition is necessary to prove that the invariant is preserved
    // in the recursive calls. This allows us to do the proof in one go.
    (forall (b:binding t). for_all (binding_neq b) slot ==> for_all (binding_neq b) slot')
  ))

#push-options "--fuel 1"
let rec hash_map_remove_from_list_s_lem #t key slot len i =
  match slot with
  | [] -> ()
  | (k',v) :: slot' ->
    if k' <> key then
      begin
      hash_map_remove_from_list_s_lem key slot' len i;
      let slot'' = hash_map_remove_from_list_s key slot' in
      assert(for_all (same_hash_mod_key len i) ((k',v)::slot''));
      assert(for_all (binding_neq (k',v)) slot'); // Triggers instanciation
      assert(for_all (binding_neq (k',v)) slot'')
      end
    else
      begin
      assert(for_all (binding_neq (k',v)) slot');
      for_all_binding_neq_find_lem key v slot'
      end
#pop-options

val hash_map_remove_s_lem
  (#t : Type0) (self : hash_map_s_nes t) (key : usize) :
  Lemma
  (requires (hash_map_s_inv self))
  (ensures (
    let hm' = hash_map_remove_s self key in
    // The invariant is preserved
    hash_map_s_inv hm' /\
    // We updated the binding
    hash_map_s_updated_binding self key None hm'))

let hash_map_remove_s_lem #t self key =
  let len = length self in
  let hash = hash_mod_key key len in
  let slot = index self hash in
  hash_map_remove_from_list_s_lem key slot len hash;
  let slot' = hash_map_remove_from_list_s key slot in
  let hm' = list_update self hash slot' in
  assert(hash_map_s_inv self)

/// Final lemma about [remove'back]
val hash_map_remove_back_lem_aux
  (#t : Type0) (self : hash_map_t t) (key : usize) :
  Lemma
  (requires (hash_map_t_inv self))
  (ensures (
    match hash_map_remove_back t self key with
    | Fail _ -> False
    | Return hm' ->
      hash_map_t_inv self /\
      hash_map_t_same_params hm' self /\
      // We updated the binding
      hash_map_s_updated_binding (hash_map_t_v self) key None (hash_map_t_v hm') /\
      hash_map_t_v hm' == hash_map_remove_s (hash_map_t_v self) key /\
      // The length is decremented iff the key was in the map
      (let len = hash_map_t_len_s self in
       let len' = hash_map_t_len_s hm' in
       match hash_map_t_find_s self key with
       | None -> len = len'
       | Some _ -> len = len' + 1)))

let hash_map_remove_back_lem_aux #t self key =
  hash_map_remove_back_lem_refin self key;
  hash_map_remove_s_lem (hash_map_t_v self) key

/// .fsti
let hash_map_remove_back_lem #t self key =
  hash_map_remove_back_lem_aux #t self key
