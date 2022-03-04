(** Properties about the hashmap written on disk *)
module HashmapMain.Properties
open Primitives
open HashmapMain.Funs

#set-options "--z3rlimit 50 --fuel 0 --ifuel 1"

/// Below, we focus on the functions to read from disk/write to disk to showcase
/// how such reasoning which mixes opaque functions together with a state-error
/// monad can be performed.

(*** Hypotheses *)

/// [state_v] gives us the hash map currently stored on disk
assume
val state_v : state -> hashmap_hash_map_t u64

/// [serialize] updates the hash map stored on disk
assume
val serialize_lem (hm : hashmap_hash_map_t u64) (st : state) : Lemma (
  match hashmap_utils_serialize_fwd hm st with
  | Fail -> True
  | Return (st', ()) -> state_v st' == hm)
  [SMTPat (hashmap_utils_serialize_fwd hm st)]

/// [deserialize] gives us the hash map stored on disk, without updating it
assume
val deserialize_lem (st : state) : Lemma (
  match hashmap_utils_deserialize_fwd st with
  | Fail -> True
  | Return (st', hm) -> hm == state_v st /\ st' == st)
  [SMTPat (hashmap_utils_deserialize_fwd st)]

(*** Lemmas - auxiliary *)

/// The below proofs are trivial: we just prove that the hashmap insert function
/// doesn't update the state... As F* is made for *intrinsic* proofs, we have
/// to copy-paste the definitions, hence the huge verbosity...

/// We will probably do some analysis in the future to use the proper monad when
/// generating the definitions (no monad if functions can't fail, error monad if
/// they can fail but don't need manipulate the state, etc. in addition to proper
/// lifting).

#push-options "--fuel 1"
let rec hashmap_hash_map_insert_in_list_fwd_lem
  (t : Type0) (key : usize) (value : t) (ls : hashmap_list_t t) (st : state) :
  Lemma
  (ensures (
    match hashmap_hash_map_insert_in_list_fwd t key value ls st with
    | Fail -> True
    | Return (st', _) -> st' == st))
  (decreases (hashmap_hash_map_insert_in_list_decreases t key value ls st))
  =
  begin match ls with
  | HashmapListCons ckey cvalue ls0 ->
    if ckey = key
    then ()
    else
      hashmap_hash_map_insert_in_list_fwd_lem t key value ls0 st
  | HashmapListNil -> ()
  end
#pop-options

#push-options "--fuel 1"
let rec hashmap_hash_map_insert_in_list_back_lem
  (t : Type0) (key : usize) (value : t) (ls : hashmap_list_t t) (st : state) :
  Lemma
  (ensures (
    match hashmap_hash_map_insert_in_list_back t key value ls st with
    | Fail -> True
    | Return (st', _) -> st' == st))
  (decreases (hashmap_hash_map_insert_in_list_decreases t key value ls st))
  =
  begin match ls with
  | HashmapListCons ckey cvalue ls0 ->
    if ckey = key then ()
    else hashmap_hash_map_insert_in_list_back_lem t key value ls0 st
  | HashmapListNil -> ()
  end
#pop-options

let hashmap_hash_map_insert_no_resize_back_lem
  (t : Type0) (self : hashmap_hash_map_t t) (key : usize) (value : t)
  (st : state) :
  Lemma
  (ensures (
    match hashmap_hash_map_insert_no_resize_back t self key value st with
    | Fail -> True
    | Return (st', _) -> st' == st))
  =
  begin match hashmap_hash_key_fwd key st with
  | Fail -> ()
  | Return (st0, i) ->
    let i0 = vec_len (hashmap_list_t t) self.hashmap_hash_map_slots in
    begin match usize_rem i i0 with
    | Fail -> ()
    | Return hash_mod ->
      begin match
        vec_index_mut_fwd (hashmap_list_t t) self.hashmap_hash_map_slots
          hash_mod with
      | Fail -> ()
      | Return l ->
        hashmap_hash_map_insert_in_list_fwd_lem t key value l st0;
        begin match hashmap_hash_map_insert_in_list_fwd t key value l st0 with
        | Fail -> ()
        | Return (st1, b) ->
          if b
          then
            begin match usize_add self.hashmap_hash_map_num_entries 1 with
            | Fail -> ()
            | Return i1 -> hashmap_hash_map_insert_in_list_back_lem t key value l st1
            end
          else hashmap_hash_map_insert_in_list_back_lem t key value l st1
        end
      end
    end
  end

#push-options "--fuel 1"
let rec hashmap_hash_map_allocate_slots_fwd_lem
  (t : Type0) (slots : vec (hashmap_list_t t)) (n : usize) (st : state) :
  Lemma (ensures (
    match hashmap_hash_map_allocate_slots_fwd t slots n st with
    | Fail -> True
    | Return (st', _) -> st' == st))
  (decreases (hashmap_hash_map_allocate_slots_decreases t slots n st))
  =
  begin match n with
  | 0 -> ()
  | _ ->
    begin match vec_push_back (hashmap_list_t t) slots HashmapListNil with
    | Fail -> ()
    | Return v ->
      begin match usize_sub n 1 with
      | Fail ->  ()
      | Return i ->
        hashmap_hash_map_allocate_slots_fwd_lem t v i st 
      end
    end
  end
#pop-options

let hashmap_hash_map_new_with_capacity_fwd_lem
  (t : Type0) (capacity : usize) (max_load_dividend : usize)
  (max_load_divisor : usize) (st : state) :
  Lemma (ensures (
    match hashmap_hash_map_new_with_capacity_fwd t capacity max_load_dividend max_load_divisor st with
    | Fail -> True
    | Return (st', _) -> st' == st))
  =
  let v = vec_new (hashmap_list_t t) in
  hashmap_hash_map_allocate_slots_fwd_lem t v capacity st

#push-options "--fuel 1"
let rec hashmap_hash_map_move_elements_from_list_back_lem
  (t : Type0) (ntable : hashmap_hash_map_t t) (ls : hashmap_list_t t)
  (st : state) :
  Lemma (ensures (
    match hashmap_hash_map_move_elements_from_list_back t ntable ls st with
    | Fail -> True
    | Return (st', _) -> st' == st))
  (decreases (hashmap_hash_map_move_elements_from_list_decreases t ntable ls st))
  =
  begin match ls with
  | HashmapListCons k v tl ->
    hashmap_hash_map_insert_no_resize_back_lem t ntable k v st;
    begin match hashmap_hash_map_insert_no_resize_back t ntable k v st with
    | Fail -> ()
    | Return (st0, hm) ->
      hashmap_hash_map_move_elements_from_list_back_lem t hm tl st0
    end
  | HashmapListNil -> ()
  end
#pop-options

#push-options "--fuel 1"
let rec hashmap_hash_map_move_elements_back_lem
  (t : Type0) (ntable : hashmap_hash_map_t t) (slots : vec (hashmap_list_t t))
  (i : usize) (st : state) :
  Lemma (ensures (
    match hashmap_hash_map_move_elements_back t ntable slots i st with
    | Fail -> True
    | Return (st', _) -> st' == st))
  (decreases (hashmap_hash_map_move_elements_decreases t ntable slots i st))
  =
  let i0 = vec_len (hashmap_list_t t) slots in
  if i < i0
  then
    begin match vec_index_mut_fwd (hashmap_list_t t) slots i with
    | Fail -> ()
    | Return l ->
      let l0 = mem_replace_fwd (hashmap_list_t t) l HashmapListNil in
      hashmap_hash_map_move_elements_from_list_back_lem t ntable l0 st;
      begin match hashmap_hash_map_move_elements_from_list_back t ntable l0 st
        with
      | Fail -> ()
      | Return (st0, hm) ->
        let l1 = mem_replace_back (hashmap_list_t t) l HashmapListNil in
        begin match vec_index_mut_back (hashmap_list_t t) slots i l1 with
        | Fail -> ()
        | Return v ->
          begin match usize_add i 1 with
          | Fail -> ()
          | Return i1 -> hashmap_hash_map_move_elements_back_lem t hm v i1 st0
          end
        end
      end
    end
  else ()
#pop-options

let hashmap_hash_map_try_resize_back_lem
  (t : Type0) (self : hashmap_hash_map_t t) (st : state) :
  Lemma (ensures (
    match hashmap_hash_map_try_resize_back t self st with
    | Fail -> True
    | Return (st', _) -> st' == st))
  =
  let i = vec_len (hashmap_list_t t) self.hashmap_hash_map_slots in
  begin match usize_div 4294967295 2 with
  | Fail -> ()
  | Return n1 ->
    let (i0, i1) = self.hashmap_hash_map_max_load_factor in
    begin match usize_div n1 i0 with
    | Fail -> ()
    | Return i2 ->
      if i <= i2
      then
        begin match usize_mul i 2 with
        | Fail -> ()
        | Return i3 ->
          hashmap_hash_map_new_with_capacity_fwd_lem t i3 i0 i1 st;
          begin match hashmap_hash_map_new_with_capacity_fwd t i3 i0 i1 st with
          | Fail -> ()
          | Return (st0, hm) ->
            hashmap_hash_map_move_elements_back_lem t hm self.hashmap_hash_map_slots 0 st0
          end
        end
      else ()
    end
  end

let hashmap_hash_map_insert_back_lem
  (t : Type0) (self : hashmap_hash_map_t t) (key : usize) (value : t)
  (st : state) :
  Lemma (ensures (
    match hashmap_hash_map_insert_back t self key value st with
    | Fail -> True
    | Return (st', _) -> st' == st))
  [SMTPat (hashmap_hash_map_insert_back t self key value st)]
  =
  hashmap_hash_map_insert_no_resize_back_lem t self key value st;
  begin match hashmap_hash_map_insert_no_resize_back t self key value st with
  | Fail -> ()
  | Return (st0, hm) ->
    begin match hashmap_hash_map_len_fwd t hm st0 with
    | Fail -> ()
    | Return (st1, i) ->
      if i > hm.hashmap_hash_map_max_load
      then
        hashmap_hash_map_try_resize_back_lem t (Mkhashmap_hash_map_t
            hm.hashmap_hash_map_num_entries hm.hashmap_hash_map_max_load_factor
            hm.hashmap_hash_map_max_load hm.hashmap_hash_map_slots) st1
      else ()
    end
  end


(*** Lemmas *)


/// The obvious lemma about [insert_on_disk]: the updated hash map stored on disk
/// is exactly the hash map produced from inserting the binding ([key], [value]
/// in the hash map previously stored on disk.
val insert_on_disk_fwd_lem (key : usize) (value : u64) (st : state) : Lemma (
  match insert_on_disk_fwd key value st with
  | Fail -> True
  | Return (st', ()) ->
    let hm = state_v st in
    match hashmap_hash_map_insert_back u64 hm key value st with
    | Fail -> False
    | Return (_, hm') -> hm' == state_v st')

let insert_on_disk_fwd_lem key value st =
  deserialize_lem st;
  begin match hashmap_utils_deserialize_fwd st with
  | Fail -> ()
  | Return (st0, hm) ->
    hashmap_hash_map_insert_back_lem u64 hm key value st0;
    begin match hashmap_hash_map_insert_back u64 hm key value st0 with
    | Fail -> ()
    | Return (st1, hm0) ->
      serialize_lem hm0 st1;
      begin match hashmap_utils_serialize_fwd hm0 st1 with
      | Fail -> ()
      | Return (st2, _) -> ()
      end
    end
  end
