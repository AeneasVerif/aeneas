(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [hashmap]: function definitions *)
module Hashmap.Funs
open Primitives
include Hashmap.Types
include Hashmap.FunsExternal
include Hashmap.Clauses

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [hashmap::hash_key]:
    Source: 'tests/src/hashmap.rs', lines 38:0-38:32 *)
let hash_key (k : usize) : result usize =
  Ok k

(** [hashmap::{hashmap::HashMap<T>}::allocate_slots]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 63:4-69:5 *)
let rec hashMap_allocate_slots_loop
  (t : Type0) (slots : alloc_vec_Vec (aList_t t)) (n : usize) :
  Tot (result (alloc_vec_Vec (aList_t t)))
  (decreases (hashMap_allocate_slots_loop_decreases t slots n))
  =
  if n > 0
  then
    let* slots1 = alloc_vec_Vec_push (aList_t t) slots AList_Nil in
    let* n1 = usize_sub n 1 in
    hashMap_allocate_slots_loop t slots1 n1
  else Ok slots

(** [hashmap::{hashmap::HashMap<T>}::allocate_slots]:
    Source: 'tests/src/hashmap.rs', lines 63:4-63:78 *)
let hashMap_allocate_slots
  (t : Type0) (slots : alloc_vec_Vec (aList_t t)) (n : usize) :
  result (alloc_vec_Vec (aList_t t))
  =
  hashMap_allocate_slots_loop t slots n

(** [hashmap::{hashmap::HashMap<T>}::new_with_capacity]:
    Source: 'tests/src/hashmap.rs', lines 72:4-76:13 *)
let hashMap_new_with_capacity
  (t : Type0) (capacity : usize) (max_load_dividend : usize)
  (max_load_divisor : usize) :
  result (hashMap_t t)
  =
  let* slots =
    hashMap_allocate_slots t (alloc_vec_Vec_new (aList_t t)) capacity in
  let* i = usize_mul capacity max_load_dividend in
  let* i1 = usize_div i max_load_divisor in
  Ok
    {
      num_entries = 0;
      max_load_factor = (max_load_dividend, max_load_divisor);
      max_load = i1;
      saturated = false;
      slots = slots
    }

(** [hashmap::{hashmap::HashMap<T>}::new]:
    Source: 'tests/src/hashmap.rs', lines 89:4-89:24 *)
let hashMap_new (t : Type0) : result (hashMap_t t) =
  hashMap_new_with_capacity t 32 4 5

(** [hashmap::{hashmap::HashMap<T>}::clear]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 97:8-102:5 *)
let rec hashMap_clear_loop
  (t : Type0) (slots : alloc_vec_Vec (aList_t t)) (i : usize) :
  Tot (result (alloc_vec_Vec (aList_t t)))
  (decreases (hashMap_clear_loop_decreases t slots i))
  =
  let i1 = alloc_vec_Vec_len (aList_t t) slots in
  if i < i1
  then
    let* (_, index_mut_back) =
      alloc_vec_Vec_index_mut (aList_t t) usize
        (core_slice_index_SliceIndexUsizeSliceTInst (aList_t t)) slots i in
    let* i2 = usize_add i 1 in
    let* slots1 = index_mut_back AList_Nil in
    hashMap_clear_loop t slots1 i2
  else Ok slots

(** [hashmap::{hashmap::HashMap<T>}::clear]:
    Source: 'tests/src/hashmap.rs', lines 94:4-94:27 *)
let hashMap_clear (t : Type0) (self : hashMap_t t) : result (hashMap_t t) =
  let* hm = hashMap_clear_loop t self.slots 0 in
  Ok { self with num_entries = 0; slots = hm }

(** [hashmap::{hashmap::HashMap<T>}::len]:
    Source: 'tests/src/hashmap.rs', lines 104:4-104:30 *)
let hashMap_len (t : Type0) (self : hashMap_t t) : result usize =
  Ok self.num_entries

(** [hashmap::{hashmap::HashMap<T>}::insert_in_list]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 111:4-128:5 *)
let rec hashMap_insert_in_list_loop
  (t : Type0) (key : usize) (value : t) (ls : aList_t t) :
  Tot (result (bool & (aList_t t)))
  (decreases (hashMap_insert_in_list_loop_decreases t key value ls))
  =
  begin match ls with
  | AList_Cons ckey cvalue tl ->
    if ckey = key
    then Ok (false, AList_Cons ckey value tl)
    else
      let* (b, tl1) = hashMap_insert_in_list_loop t key value tl in
      Ok (b, AList_Cons ckey cvalue tl1)
  | AList_Nil -> Ok (true, AList_Cons key value AList_Nil)
  end

(** [hashmap::{hashmap::HashMap<T>}::insert_in_list]:
    Source: 'tests/src/hashmap.rs', lines 111:4-111:72 *)
let hashMap_insert_in_list
  (t : Type0) (key : usize) (value : t) (ls : aList_t t) :
  result (bool & (aList_t t))
  =
  hashMap_insert_in_list_loop t key value ls

(** [hashmap::{hashmap::HashMap<T>}::insert_no_resize]:
    Source: 'tests/src/hashmap.rs', lines 131:4-131:54 *)
let hashMap_insert_no_resize
  (t : Type0) (self : hashMap_t t) (key : usize) (value : t) :
  result (hashMap_t t)
  =
  let* hash = hash_key key in
  let i = alloc_vec_Vec_len (aList_t t) self.slots in
  let* hash_mod = usize_rem hash i in
  let* (a, index_mut_back) =
    alloc_vec_Vec_index_mut (aList_t t) usize
      (core_slice_index_SliceIndexUsizeSliceTInst (aList_t t)) self.slots
      hash_mod in
  let* (inserted, a1) = hashMap_insert_in_list t key value a in
  if inserted
  then
    let* i1 = usize_add self.num_entries 1 in
    let* v = index_mut_back a1 in
    Ok { self with num_entries = i1; slots = v }
  else let* v = index_mut_back a1 in Ok { self with slots = v }

(** [hashmap::{hashmap::HashMap<T>}::move_elements_from_list]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 194:4-207:5 *)
let rec hashMap_move_elements_from_list_loop
  (t : Type0) (ntable : hashMap_t t) (ls : aList_t t) :
  Tot (result (hashMap_t t))
  (decreases (hashMap_move_elements_from_list_loop_decreases t ntable ls))
  =
  begin match ls with
  | AList_Cons k v tl ->
    let* ntable1 = hashMap_insert_no_resize t ntable k v in
    hashMap_move_elements_from_list_loop t ntable1 tl
  | AList_Nil -> Ok ntable
  end

(** [hashmap::{hashmap::HashMap<T>}::move_elements_from_list]:
    Source: 'tests/src/hashmap.rs', lines 194:4-194:73 *)
let hashMap_move_elements_from_list
  (t : Type0) (ntable : hashMap_t t) (ls : aList_t t) : result (hashMap_t t) =
  hashMap_move_elements_from_list_loop t ntable ls

(** [hashmap::{hashmap::HashMap<T>}::move_elements]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 182:8-191:5 *)
let rec hashMap_move_elements_loop
  (t : Type0) (ntable : hashMap_t t) (slots : alloc_vec_Vec (aList_t t))
  (i : usize) :
  Tot (result ((hashMap_t t) & (alloc_vec_Vec (aList_t t))))
  (decreases (hashMap_move_elements_loop_decreases t ntable slots i))
  =
  let i1 = alloc_vec_Vec_len (aList_t t) slots in
  if i < i1
  then
    let* (a, index_mut_back) =
      alloc_vec_Vec_index_mut (aList_t t) usize
        (core_slice_index_SliceIndexUsizeSliceTInst (aList_t t)) slots i in
    let (ls, a1) = core_mem_replace (aList_t t) true a AList_Nil in
    let* ntable1 = hashMap_move_elements_from_list t ntable ls in
    let* i2 = usize_add i 1 in
    let* slots1 = index_mut_back a1 in
    hashMap_move_elements_loop t ntable1 slots1 i2
  else Ok (ntable, slots)

(** [hashmap::{hashmap::HashMap<T>}::move_elements]:
    Source: 'tests/src/hashmap.rs', lines 181:4-181:82 *)
let hashMap_move_elements
  (t : Type0) (ntable : hashMap_t t) (slots : alloc_vec_Vec (aList_t t)) :
  result ((hashMap_t t) & (alloc_vec_Vec (aList_t t)))
  =
  hashMap_move_elements_loop t ntable slots 0

(** [hashmap::{hashmap::HashMap<T>}::try_resize]:
    Source: 'tests/src/hashmap.rs', lines 154:4-154:28 *)
let hashMap_try_resize
  (t : Type0) (self : hashMap_t t) : result (hashMap_t t) =
  let capacity = alloc_vec_Vec_len (aList_t t) self.slots in
  let* n1 = usize_div core_usize_max 2 in
  let (i, i1) = self.max_load_factor in
  let* i2 = usize_div n1 i in
  if capacity <= i2
  then
    let* i3 = usize_mul capacity 2 in
    let* ntable = hashMap_new_with_capacity t i3 i i1 in
    let* p = hashMap_move_elements t ntable self.slots in
    let (ntable1, _) = p in
    Ok
      {
        self
          with
          max_load_factor = (i, i1);
          max_load = ntable1.max_load;
          slots = ntable1.slots
      }
  else Ok { self with max_load_factor = (i, i1); saturated = true }

(** [hashmap::{hashmap::HashMap<T>}::insert]:
    Source: 'tests/src/hashmap.rs', lines 143:4-143:48 *)
let hashMap_insert
  (t : Type0) (self : hashMap_t t) (key : usize) (value : t) :
  result (hashMap_t t)
  =
  let* self1 = hashMap_insert_no_resize t self key value in
  let* i = hashMap_len t self1 in
  if i > self1.max_load
  then
    if self1.saturated
    then Ok { self1 with saturated = true }
    else hashMap_try_resize t { self1 with saturated = false }
  else Ok self1

(** [hashmap::{hashmap::HashMap<T>}::contains_key_in_list]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 217:4-230:5 *)
let rec hashMap_contains_key_in_list_loop
  (t : Type0) (key : usize) (ls : aList_t t) :
  Tot (result bool)
  (decreases (hashMap_contains_key_in_list_loop_decreases t key ls))
  =
  begin match ls with
  | AList_Cons ckey _ tl ->
    if ckey = key then Ok true else hashMap_contains_key_in_list_loop t key tl
  | AList_Nil -> Ok false
  end

(** [hashmap::{hashmap::HashMap<T>}::contains_key_in_list]:
    Source: 'tests/src/hashmap.rs', lines 217:4-217:69 *)
let hashMap_contains_key_in_list
  (t : Type0) (key : usize) (ls : aList_t t) : result bool =
  hashMap_contains_key_in_list_loop t key ls

(** [hashmap::{hashmap::HashMap<T>}::contains_key]:
    Source: 'tests/src/hashmap.rs', lines 210:4-210:49 *)
let hashMap_contains_key
  (t : Type0) (self : hashMap_t t) (key : usize) : result bool =
  let* hash = hash_key key in
  let i = alloc_vec_Vec_len (aList_t t) self.slots in
  let* hash_mod = usize_rem hash i in
  let* a =
    alloc_vec_Vec_index (aList_t t) usize
      (core_slice_index_SliceIndexUsizeSliceTInst (aList_t t)) self.slots
      hash_mod in
  hashMap_contains_key_in_list t key a

(** [hashmap::{hashmap::HashMap<T>}::get_in_list]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 235:4-248:5 *)
let rec hashMap_get_in_list_loop
  (t : Type0) (key : usize) (ls : aList_t t) :
  Tot (result t) (decreases (hashMap_get_in_list_loop_decreases t key ls))
  =
  begin match ls with
  | AList_Cons ckey cvalue tl ->
    if ckey = key then Ok cvalue else hashMap_get_in_list_loop t key tl
  | AList_Nil -> Fail Failure
  end

(** [hashmap::{hashmap::HashMap<T>}::get_in_list]:
    Source: 'tests/src/hashmap.rs', lines 235:4-235:71 *)
let hashMap_get_in_list (t : Type0) (key : usize) (ls : aList_t t) : result t =
  hashMap_get_in_list_loop t key ls

(** [hashmap::{hashmap::HashMap<T>}::get]:
    Source: 'tests/src/hashmap.rs', lines 250:4-250:55 *)
let hashMap_get (t : Type0) (self : hashMap_t t) (key : usize) : result t =
  let* hash = hash_key key in
  let i = alloc_vec_Vec_len (aList_t t) self.slots in
  let* hash_mod = usize_rem hash i in
  let* a =
    alloc_vec_Vec_index (aList_t t) usize
      (core_slice_index_SliceIndexUsizeSliceTInst (aList_t t)) self.slots
      hash_mod in
  hashMap_get_in_list t key a

(** [hashmap::{hashmap::HashMap<T>}::get_mut_in_list]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 256:4-265:5 *)
let rec hashMap_get_mut_in_list_loop
  (t : Type0) (ls : aList_t t) (key : usize) :
  Tot (result (t & (t -> result (aList_t t))))
  (decreases (hashMap_get_mut_in_list_loop_decreases t ls key))
  =
  begin match ls with
  | AList_Cons ckey cvalue tl ->
    if ckey = key
    then let back = fun ret -> Ok (AList_Cons ckey ret tl) in Ok (cvalue, back)
    else
      let* (x, back) = hashMap_get_mut_in_list_loop t tl key in
      let back1 =
        fun ret -> let* tl1 = back ret in Ok (AList_Cons ckey cvalue tl1) in
      Ok (x, back1)
  | AList_Nil -> Fail Failure
  end

(** [hashmap::{hashmap::HashMap<T>}::get_mut_in_list]:
    Source: 'tests/src/hashmap.rs', lines 256:4-256:87 *)
let hashMap_get_mut_in_list
  (t : Type0) (ls : aList_t t) (key : usize) :
  result (t & (t -> result (aList_t t)))
  =
  hashMap_get_mut_in_list_loop t ls key

(** [hashmap::{hashmap::HashMap<T>}::get_mut]:
    Source: 'tests/src/hashmap.rs', lines 268:4-268:67 *)
let hashMap_get_mut
  (t : Type0) (self : hashMap_t t) (key : usize) :
  result (t & (t -> result (hashMap_t t)))
  =
  let* hash = hash_key key in
  let i = alloc_vec_Vec_len (aList_t t) self.slots in
  let* hash_mod = usize_rem hash i in
  let* (a, index_mut_back) =
    alloc_vec_Vec_index_mut (aList_t t) usize
      (core_slice_index_SliceIndexUsizeSliceTInst (aList_t t)) self.slots
      hash_mod in
  let* (x, get_mut_in_list_back) = hashMap_get_mut_in_list t a key in
  let back =
    fun ret ->
      let* a1 = get_mut_in_list_back ret in
      let* v = index_mut_back a1 in
      Ok { self with slots = v } in
  Ok (x, back)

(** [hashmap::{hashmap::HashMap<T>}::remove_from_list]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 276:4-302:5 *)
let rec hashMap_remove_from_list_loop
  (t : Type0) (key : usize) (ls : aList_t t) :
  Tot (result ((option t) & (aList_t t)))
  (decreases (hashMap_remove_from_list_loop_decreases t key ls))
  =
  begin match ls with
  | AList_Cons ckey x tl ->
    if ckey = key
    then
      let (mv_ls, _) =
        core_mem_replace (aList_t t) true (AList_Cons ckey x tl) AList_Nil in
      begin match mv_ls with
      | AList_Cons _ cvalue tl1 -> Ok (Some cvalue, tl1)
      | AList_Nil -> Fail Failure
      end
    else
      let* (o, tl1) = hashMap_remove_from_list_loop t key tl in
      Ok (o, AList_Cons ckey x tl1)
  | AList_Nil -> Ok (None, AList_Nil)
  end

(** [hashmap::{hashmap::HashMap<T>}::remove_from_list]:
    Source: 'tests/src/hashmap.rs', lines 276:4-276:70 *)
let hashMap_remove_from_list
  (t : Type0) (key : usize) (ls : aList_t t) :
  result ((option t) & (aList_t t))
  =
  hashMap_remove_from_list_loop t key ls

(** [hashmap::{hashmap::HashMap<T>}::remove]:
    Source: 'tests/src/hashmap.rs', lines 305:4-305:52 *)
let hashMap_remove
  (t : Type0) (self : hashMap_t t) (key : usize) :
  result ((option t) & (hashMap_t t))
  =
  let* hash = hash_key key in
  let i = alloc_vec_Vec_len (aList_t t) self.slots in
  let* hash_mod = usize_rem hash i in
  let* (a, index_mut_back) =
    alloc_vec_Vec_index_mut (aList_t t) usize
      (core_slice_index_SliceIndexUsizeSliceTInst (aList_t t)) self.slots
      hash_mod in
  let* (x, a1) = hashMap_remove_from_list t key a in
  begin match x with
  | None -> let* v = index_mut_back a1 in Ok (None, { self with slots = v })
  | Some x1 ->
    let* i1 = usize_sub self.num_entries 1 in
    let* v = index_mut_back a1 in
    Ok (Some x1, { self with num_entries = i1; slots = v })
  end

(** [hashmap::insert_on_disk]:
    Source: 'tests/src/hashmap.rs', lines 336:0-336:43 *)
let insert_on_disk
  (key : usize) (value : u64) (st : state) : result (state & unit) =
  let* (st1, hm) = utils_deserialize st in
  let* hm1 = hashMap_insert u64 hm key value in
  utils_serialize hm1 st1

(** [hashmap::test1]:
    Source: 'tests/src/hashmap.rs', lines 351:0-351:10 *)
let test1 : result unit =
  let* hm = hashMap_new u64 in
  let* hm1 = hashMap_insert u64 hm 0 42 in
  let* hm2 = hashMap_insert u64 hm1 128 18 in
  let* hm3 = hashMap_insert u64 hm2 1024 138 in
  let* hm4 = hashMap_insert u64 hm3 1056 256 in
  let* i = hashMap_get u64 hm4 128 in
  if i = 18
  then
    let* (_, get_mut_back) = hashMap_get_mut u64 hm4 1024 in
    let* hm5 = get_mut_back 56 in
    let* i1 = hashMap_get u64 hm5 1024 in
    if i1 = 56
    then
      let* (x, hm6) = hashMap_remove u64 hm5 1024 in
      begin match x with
      | None -> Fail Failure
      | Some x1 ->
        if x1 = 56
        then
          let* i2 = hashMap_get u64 hm6 0 in
          if i2 = 42
          then
            let* i3 = hashMap_get u64 hm6 128 in
            if i3 = 18
            then
              let* i4 = hashMap_get u64 hm6 1056 in
              if i4 = 256 then Ok () else Fail Failure
            else Fail Failure
          else Fail Failure
        else Fail Failure
      end
    else Fail Failure
  else Fail Failure

