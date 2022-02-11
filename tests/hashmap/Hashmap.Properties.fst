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

/// The proofs actually caused a lot more trouble than expected, because:
/// - we are blind when doing the proofs. After a very intensive use of F* I got
///   used to it meaning I can *do* proofs in F*, but it still takes me a tremendous
///   amout of energy to visualize the context in my head and, for instance,
///   properly instantiate the lemmas or insert the necessary assertions in the code.
///   I actually often write assertions that I assume just to *check* that those
///   assertions make the proofs pass and are thus indeed the ones I want to prove,
///   which is something very specific to working with F*.
/// - F* is extremely bad at reasoning with quantifiers, which is made worse by
///   the fact we are blind when making proofs. This forced me to be extremely
///   careful about the way I wrote the specs/invariants (by writing "functional"
///   specs and invariants, mostly, so as not to manipulate quantifiers)
/// - F* doesn't encode closures properly, the result being that it is very
///   awkward to reason about functions like `map` or `find`, because we have
///   to introduce auxiliary definitions for the parameters we give to those
///   functions (if we use anonymous lambda functions, we're screwed by the
///   encoding).
/// - we can't easily prove intermediate results which require a recursive proofs
///   inside of other proofs, meaning that whenever we need such a result we need
///   to write an intermediate lemma, which is extremely cumbersome.
///
/// The result is that I had to poor a lot more thinking than I expected in the below
/// proofs, in particular to:
/// - write invariants and specs that I could *manage* in F*
/// - subdivide all the theorems into very small, modular lemmas that I could reason
///   about independently, in a small context, and with quick responses from F*.
/// 
/// Note that in a theorem prover with tactics, most of the below proof would have
/// been extremely straightforward.


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

val length_flatten_update :
     #a:Type
  -> ls:list (list a)
  -> i:nat{i < length ls}
  -> x:list a ->
  Lemma (
    // length (flatten (list_update ls i x)) =
    //   length (flatten ls) - length (index ls i) + length x
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
    for_all (pred x) ls' && pairwise_rel pred ls' 

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
/// TODO: remove?
let slots_t_v (#t : Type0) (slots : slots_t t) : assoc_list t =
  flatten (map list_t_v slots)

// TODO: use more
type slot_s (t : Type0) = list (binding t)
type slots_s (t : Type0) = list (slot_s t)

// TODO: use more
type slot_t (t : Type0) = list_t t
let slot_t_v (#t : Type0) (slot : slot_t t) : slot_s t = list_t_v slot

/// High-level type for the hash-map, seen as a list of associative lists (one
/// list per slot)
type hash_map_slots_s t = list (slot_s t)

/// High-level type for the hash-map, seen as a an associative list
type hash_map_s t = assoc_list t

/// Representation function for [hash_map_t] as a list of slots
let hash_map_t_slots_v (#t : Type0) (hm : hash_map_t t) : hash_map_slots_s t =
  map list_t_v hm.hash_map_slots

/// Representation function for [hash_map_t]
let hash_map_t_v (#t : Type0) (hm : hash_map_t t) : hash_map_s t =
  flatten (hash_map_t_slots_v hm)

// TODO: move
let is_pos_usize (n : nat) : Type0 = 0 < n /\ n <= usize_max

// 'ne': "non-empty slots"
// TODO: use more
type hash_map_t_nes (t : Type0) : Type0 =
  hm:hash_map_t t{is_pos_usize (length hm.hash_map_slots)}

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

let hash_map_t_mem_s (#t : Type0) (hm : hash_map_t t) (k : key) : bool =
  existsb (same_key k) (hash_map_t_v hm)

let hash_map_t_len_s (#t : Type0) (hm : hash_map_t t) : nat =
  hm.hash_map_num_entries

let slot_find (#t : Type0) (k : key) (slot : list (binding t)) : option t =
  match find (same_key k) slot with
  | None -> None
  | Some (_, v) -> Some v

let slot_t_find_s (#t : Type0) (k : key) (slot : list_t t) : option t =
  match find (same_key k) (list_t_v slot) with
  | None -> None
  | Some (_, v) -> Some v

// This is a simpler version of the "find" function, which captures the essence
// of what happens and operates on [hash_map_slots_s].
// TODO: useful?
let hash_map_slots_s_find
  (#t : Type0) (hm : hash_map_slots_s t{length hm <= usize_max /\ length hm > 0})
  (k : key) : option t =
  let i = hash_mod_key k (length hm) in
  let slot = index hm i in
  slot_find k slot

let hash_map_slots_s_len
  (#t : Type0) (hm : hash_map_slots_s t{length hm <= usize_max /\ length hm > 0}) :
  nat =
  length (flatten hm)

// Same as above, but operates on [hash_map_t]
// Note that we don't reuse the above function on purpose: converting to a
// [hash_map_slots_s] then looking up an element is not the same as what we
// wrote below.
let hash_map_t_find_s
  (#t : Type0) (hm : hash_map_t t{length hm.hash_map_slots > 0}) (k : key) : option t =
  let slots = hm.hash_map_slots in
  let i = hash_mod_key k (length slots) in
  let slot = index slots i in
  slot_t_find_s k slot

(*let hash_map_t_find_s (#t : Type0) (hm : hash_map_t t) (k : key) : option t =
 match find (same_key k) (hash_map_t_v hm) with
 | None -> None
 | Some (_, v) -> Some v*)

/// Auxiliary function stating that two associative lists are "equivalent"
let assoc_list_equiv (#t : Type0) (al0 al1 : assoc_list t) : Type0 =
  // All the bindings in al0 can be found in al1
  for_allP (has_same_binding al1) al0 /\
  // And the reverse is true
  for_allP (has_same_binding al0) al1

(*
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
*)

(**)

/// Invariants for the slots

let slot_s_inv
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

let slots_s_inv (#t : Type0) (slots : slots_s t{length slots <= usize_max}) : Type0 =
  forall(i:nat{i < length slots}).
  {:pattern index slots i}
  slot_s_inv (length slots) i (index slots i)

let slots_t_inv (#t : Type0) (slots : slots_t t{length slots <= usize_max}) : Type0 =
  forall(i:nat{i < length slots}).
  {:pattern index slots i}
  slot_t_inv (length slots) i (index slots i)

(*
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
*)

// TODO: hash_map_slots -> hash_map_slots_s
let hash_map_slots_s_inv (#t : Type0) (hm : hash_map_slots_s t) : Type0 =
  length hm <= usize_max /\
  length hm > 0 /\
  slots_s_inv hm

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
  hash_map_t_base_inv hm
  // The hash map is either: not overloaded, or we can't resize it
//  (hm.hash_map_num_entries <= hm.hash_map_max_load
//   || length hm.hash_map_slots * 2 > usize_max)

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

(*** allocate_slots *)

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
    capacity * max_load_dividend < usize_max))
  (ensures (
    match hash_map_new_with_capacity_fwd t capacity max_load_dividend max_load_divisor with
    | Fail -> False
    | Return hm ->
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

(*** new *)
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
      hash_map_t_len_s hm = 0 /\
      // It contains no bindings
      (forall k. hash_map_t_find_s hm k == None)))

#push-options "--fuel 1"
let hash_map_new_fwd_lem_fun t =
  hash_map_new_with_capacity_fwd_lem t 32 4 5;
  match hash_map_new_with_capacity_fwd t 32 4 5 with
  | Fail -> ()
  | Return hm ->
    slots_t_v_all_nil_is_empty_lem hm.hash_map_slots
#pop-options

(*** clear_slots *)
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

(*** clear *)
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
      hash_map_t_len_s hm = 0 /\
      // It contains no bindings
      (forall k. hash_map_t_find_s hm k == None)))

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

(*** len *)

/// [len]: we link it to a non-failing function.
/// Rk.: we might want to make an analysis to not use an error monad to translate
/// functions which statically can't fail.
val hash_map_len_fwd_lem (t : Type0) (self : hash_map_t t) :
  Lemma (
    match hash_map_len_fwd t self with
    | Fail -> False
    | Return l -> l = hash_map_t_len_s self)

let hash_map_len_fwd_lem t self = ()


(*** insert_in_list *)

(**** insert_in_list'fwd *)

/// [insert_in_list_fwd]: returns true iff the key is not in the list (functional version)
val hash_map_insert_in_list_fwd_lem
  (t : Type0) (key : usize) (value : t) (ls : list_t t) :
  Lemma
  (ensures (
    match hash_map_insert_in_list_fwd t key value ls with
    | Fail -> False
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
      | Fail -> ()
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
    | Fail -> False
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
      | Fail -> ()
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
    | Fail -> False
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
      | Fail -> ()
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
    | Fail -> False
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
    slot_find key ls == None))
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
    slot_find key ls == None))
  (ensures (
    let ls' = ls @ [(key,value)] in
    slot_s_inv len (hash_mod_key key len) ls' /\
    (slot_find key ls' == Some value) /\
    (forall k'. k' <> key ==> slot_find k' ls' == slot_find k' ls)))

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
    slot_find key ls == None))
  (ensures (
    let ls' = hash_map_insert_in_list_s key value ls in
    ls' == ls @ [(key,value)] /\
    // The invariant is preserved
    slot_s_inv len (hash_mod_key key len) ls' /\
    // [key] maps to [value]
    slot_find key ls' == Some value /\
    // The other bindings are preserved
    (forall k'. k' <> key ==> slot_find k' ls' == slot_find k' ls)))

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
    | Fail -> False
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

val slot_find_update_for_all_binding_neq_append_lem
  (t : Type0) (key : usize) (value : t) (ls : list (binding t)) (b : binding t) :
  Lemma
  (requires (
    fst b <> key /\
    for_all (binding_neq b) ls))
  (ensures (
    let ls' = find_update (same_key key) ls (key, value) in
    for_all (binding_neq b) ls'))

#push-options "--fuel 1"
let rec slot_find_update_for_all_binding_neq_append_lem t key value ls b =
  match ls with
  | [] -> ()
  | (ck, cv) :: cls ->
    slot_find_update_for_all_binding_neq_append_lem t key value cls b
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
    Some? (slot_find key ls)))
  (ensures (
    let ls' = find_update (same_key key) ls (key, value) in
    slot_s_inv len (hash_mod_key key len) ls' /\
    (slot_find key ls' == Some value) /\
    (forall k'. k' <> key ==> slot_find k' ls' == slot_find k' ls)))

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
      slot_find_update_for_all_binding_neq_append_lem t key value cls (ck, cv);
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
    Some? (slot_find key ls)))
  (ensures (
    let ls' = hash_map_insert_in_list_s key value ls in
    ls' == find_update (same_key key) ls (key,value) /\
    // The invariant is preserved
    slot_s_inv len (hash_mod_key key len) ls' /\
    // [key] maps to [value]
    slot_find key ls' == Some value /\
    // The other bindings are preserved
    (forall k'. k' <> key ==> slot_find k' ls' == slot_find k' ls)))

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
    | Fail -> False
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
    slot_find key ls' == Some value /\
    // The other bindings are preserved
    (forall k'. k' <> key ==> slot_find k' ls' == slot_find k' ls) /\
    // The length is incremented, iff we inserted a new key
    (match slot_find key ls with
     | None -> length ls' = length ls + 1
     | Some _ -> length ls' = length ls)))

let hash_map_insert_in_list_s_lem t len key value ls =
  match slot_find key ls with
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
    | Fail -> False
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
/// We work on [hash_map_slots_s] (we use a higher-level view of the hash-map, but
/// not too high).

let hash_map_insert_no_resize_s
  (#t : Type0) (hm : hash_map_slots_s t{length hm <= usize_max /\ length hm > 0})
  (key : usize) (value : t) :
  result (hash_map_slots_s t) =
  // Check if the table is saturated (too many entries, and we need to insert one)
  let num_entries = length (flatten hm) in
  if None? (hash_map_slots_s_find hm key) && num_entries = usize_max then Fail
  else
    begin
    let len = length hm in
    let i = hash_mod_key key len in
    let slot = index hm i in
    let slot' = hash_map_insert_in_list_s key value slot in
    let hm' = list_update hm i slot' in
    Return hm'
    end

/// Prove that [hash_map_insert_no_resize_s] is a refinement of
/// [hash_map_insert_no_resize'fwd_back]
val hash_map_insert_no_resize_fwd_back_lem
  (t : Type0) (self : hash_map_t t) (key : usize) (value : t) :
  Lemma
  (requires (
    hash_map_t_inv self /\
    hash_map_slots_s_len (hash_map_t_slots_v self) = hash_map_t_len_s self))
  (ensures (
    begin
    match hash_map_insert_no_resize_fwd_back t self key value,
          hash_map_insert_no_resize_s (hash_map_t_slots_v self) key value
    with
    | Fail, Fail -> True
    | Return hm, Return hm_v ->
      hash_map_t_slots_v hm == hm_v /\
      hash_map_slots_s_len hm_v = hash_map_t_len_s hm /\
      True
    | _ -> False
    end))

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
        // Checking that: list_t_v (index ...) == index (hash_map_t_slots_v ...) ...
        assert(list_t_v l == index (hash_map_t_slots_v self) hash_mod);
        hash_map_insert_in_list_fwd_lem t key value l;
        match hash_map_insert_in_list_fwd t key value l with
        | Fail -> ()
        | Return b ->
          assert(b = None? (slot_find key (list_t_v l)));
          hash_map_insert_in_list_back_lem_s t key value l;
          if b
          then
            begin match usize_add i0 1 with
            | Fail -> ()
            | Return i3 ->
              begin
              match hash_map_insert_in_list_back t key value l with
              | Fail -> ()
              | Return l0 ->
                begin match vec_index_mut_back (list_t t) v hash_mod l0 with
                | Fail -> ()
                | Return v0 ->
                  let self_v = hash_map_t_slots_v self in
                  let hm = Mkhash_map_t i3 p i1 v0 in
                  let hm_v = hash_map_t_slots_v hm in
                  assert(hm_v == list_update self_v hash_mod (list_t_v l0));
                  assert_norm(length [(key,value)] = 1);
                  assert(length (list_t_v l0) = length (list_t_v l) + 1);
                  length_flatten_update self_v hash_mod (list_t_v l0);
                  assert(hash_map_slots_s_len hm_v = hash_map_t_len_s hm)
                end
              end
            end
          else
            begin
            match hash_map_insert_in_list_back t key value l with
            | Fail -> ()
            | Return l0 ->
              begin match vec_index_mut_back (list_t t) v hash_mod l0 with
              | Fail -> ()
              | Return v0 ->
                let self_v = hash_map_t_slots_v self in
                let hm = Mkhash_map_t i0 p i1 v0 in
                let hm_v = hash_map_t_slots_v hm in
                assert(hm_v == list_update self_v hash_mod (list_t_v l0));
                assert(length (list_t_v l0) = length (list_t_v l));
                length_flatten_update self_v hash_mod (list_t_v l0);
                assert(hash_map_slots_s_len hm_v = hash_map_t_len_s hm)
              end
            end
        end
      end
    end
  end

(**** find after insert *)
/// Lemmas about what happens if we call [find] after an insertion

val hash_map_insert_no_resize_s_get_same_lem
  (#t : Type0) (hm : hash_map_slots_s t)
  (key : usize) (value : t) :
  Lemma (requires (hash_map_slots_s_inv hm))
  (ensures (
    match hash_map_insert_no_resize_s hm key value with
    | Fail -> True
    | Return hm' ->
      hash_map_slots_s_find hm' key == Some value))

let hash_map_insert_no_resize_s_get_same_lem #t hm key value =
  let num_entries = length (flatten hm) in
  if None? (hash_map_slots_s_find hm key) && num_entries = usize_max then ()
  else
    begin
    let hm' = Return?.v (hash_map_insert_no_resize_s hm key value) in
    let len = length hm in
    let i = hash_mod_key key len in
    let slot = index hm i in
    hash_map_insert_in_list_s_lem t len key value slot
   end

val hash_map_insert_no_resize_s_get_diff_lem
  (#t : Type0) (hm : hash_map_slots_s t)
  (key : usize) (value : t) (key' : usize{key' <> key}) :
  Lemma (requires (hash_map_slots_s_inv hm))
  (ensures (
    match hash_map_insert_no_resize_s hm key value with
    | Fail -> True
    | Return hm' ->
      hash_map_slots_s_find hm' key' == hash_map_slots_s_find hm key'))

let hash_map_insert_no_resize_s_get_diff_lem #t hm key value key' =
  let num_entries = length (flatten hm) in
  if None? (hash_map_slots_s_find hm key) && num_entries = usize_max then ()
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

type hash_map_slots_s_res (t : Type0) = res:result (hash_map_slots_s t){
    match res with
    | Fail -> True
    | Return hm -> is_pos_usize (length hm)
  }

let hash_map_move_elements_from_list_s
  (t : Type0) (hm : hash_map_slots_s t{is_pos_usize (length hm)})
  (ls : slot_s t) :
  Tot (hash_map_slots_s_res t) =
  let add_elem (hm_res : hash_map_slots_s_res t) (b : binding t) :
    hash_map_slots_s_res t =
    match hm_res with
    | Fail -> Fail
    | Return hm ->
      let (key,value) = b in
      hash_map_insert_no_resize_s hm key value
  in
  fold_left add_elem (Return hm) ls

/// Refinement lemma
val hash_map_move_elements_from_list_fwd_back_lem
  (t : Type0) (ntable : hash_map_t_nes t) (ls : list_t t) :
  Lemma (requires (hash_map_t_inv ntable))
  (ensures (
    match hash_map_move_elements_from_list_fwd_back t ntable ls,
          hash_map_move_elements_from_list_s t (hash_map_t_slots_v ntable) (slot_t_v ls)
    with
    | Fail, Fail -> True
    | Return hm', Return hm_v ->
      hash_map_t_inv hm' /\
      hash_map_t_slots_v hm' == hm_v
    | _ -> False))
  (decreases (hash_map_move_elements_from_list_decreases t ntable ls))

#push-options "--z3rlimit 100 --fuel 1"
let rec hash_map_move_elements_from_list_fwd_back_lem t ntable ls =
  begin match ls with
  | ListCons k v tl ->
    hash_map_insert_no_resize_fwd_back_lem t ntable k v;
    begin match hash_map_insert_no_resize_fwd_back t ntable k v with
    | Fail -> admit()
    | Return h ->
      hash_map_move_elements_from_list_fwd_back_lem t h tl;
      begin match hash_map_move_elements_from_list_fwd_back t h tl with
      | Fail -> admit()
      | Return h0 -> admit()
      end
    end
  | ListNil -> ()
  end
#pop-options

/// Refinement lemma
val hash_map_move_elements_fwd_back_lem
  (t : Type0) (ntable : hash_map_t t) (slots : vec (list_t t)) (i : usize) :
  Lemma (requires (is_pos_usize (ntable.hash_map_num_entries)))
  (ensures (
    match hash_map_move_elements_fwd_back t ntable slots i,
          hash_map_move_elements_from_list_s t ntable slots 
    with
    | Fail -> 
  ))
  (decreases (hash_map_move_elements_decreases t ntable slots i))

let rec hash_map_move_elements_fwd_back
  (t : Type0) (ntable : hash_map_t t) (slots : vec (list_t t)) (i : usize) :
  Tot (result ((hash_map_t t) & (vec (list_t t))))
  (decreases (hash_map_move_elements_decreases t ntable slots i))
  =
  let i0 = vec_len (list_t t) slots in
  let b = i < i0 in
  if b
  then
    begin match vec_index_mut_fwd (list_t t) slots i with
    | Fail -> Fail
    | Return l ->
      let l0 = mem_replace_fwd (list_t t) l ListNil in
      begin match hash_map_move_elements_from_list_fwd_back t ntable l0 with
      | Fail -> Fail
      | Return h ->
        let l1 = mem_replace_back (list_t t) l ListNil in
        begin match vec_index_mut_back (list_t t) slots i l1 with
        | Fail -> Fail
        | Return v ->
          begin match usize_add i 1 with
          | Fail -> Fail
          | Return i1 ->
            begin match hash_map_move_elements_fwd_back t h v i1 with
            | Fail -> Fail
            | Return (h0, v0) -> Return (h0, v0)
            end
          end
        end
      end
    end
  else Return (ntable, slots)
