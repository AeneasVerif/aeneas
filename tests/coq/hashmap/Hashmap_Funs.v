(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [hashmap]: function definitions *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Require Import Hashmap_Types.
Include Hashmap_Types.
Require Import Hashmap_FunsExternal.
Include Hashmap_FunsExternal.
Module Hashmap_Funs.

(** [hashmap::hash_key]:
    Source: 'tests/src/hashmap.rs', lines 38:0-43:1 *)
Definition hash_key (k : usize) : result usize :=
  Ok k.

(** [hashmap::{core::clone::Clone for hashmap::Fraction}#1::clone]:
    Source: 'tests/src/hashmap.rs', lines 45:9-45:14 *)
Definition clonehashmapFraction_clone
  (self : Fraction_t) : result Fraction_t :=
  Ok self
.

(** Trait implementation: [hashmap::{core::clone::Clone for hashmap::Fraction}#1]
    Source: 'tests/src/hashmap.rs', lines 45:9-45:14 *)
Definition core_clone_ClonehashmapFraction : core_clone_Clone Fraction_t := {|
  core_clone_Clone_clone := clonehashmapFraction_clone;
|}.

(** Trait implementation: [hashmap::{core::marker::Copy for hashmap::Fraction}#2]
    Source: 'tests/src/hashmap.rs', lines 45:16-45:20 *)
Definition core_marker_CopyhashmapFraction : core_marker_Copy Fraction_t := {|
  cloneInst := core_clone_ClonehashmapFraction;
|}.

(** [hashmap::{hashmap::HashMap<T>}::allocate_slots]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 70:8-73:9 *)
Fixpoint hashMap_allocate_slots_loop
  {T : Type} (n : nat) (slots : alloc_vec_Vec (AList_t T)) (n1 : usize) :
  result (alloc_vec_Vec (AList_t T))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n2 =>
    if n1 s> 0%usize
    then (
      slots1 <- alloc_vec_Vec_push slots AList_Nil;
      n3 <- usize_sub n1 1%usize;
      hashMap_allocate_slots_loop n2 slots1 n3)
    else Ok slots
  end
.

(** [hashmap::{hashmap::HashMap<T>}::allocate_slots]:
    Source: 'tests/src/hashmap.rs', lines 69:4-75:5 *)
Definition hashMap_allocate_slots
  {T : Type} (n : nat) (slots : alloc_vec_Vec (AList_t T)) (n1 : usize) :
  result (alloc_vec_Vec (AList_t T))
  :=
  hashMap_allocate_slots_loop n slots n1
.

(** [hashmap::{hashmap::HashMap<T>}::new_with_capacity]:
    Source: 'tests/src/hashmap.rs', lines 78:4-89:5 *)
Definition hashMap_new_with_capacity
  (T : Type) (n : nat) (capacity : usize) (max_load_factor : Fraction_t) :
  result (HashMap_t T)
  :=
  slots <- hashMap_allocate_slots n (alloc_vec_Vec_new (AList_t T)) capacity;
  i <- usize_mul capacity max_load_factor.(fraction_dividend);
  i1 <- usize_div i max_load_factor.(fraction_divisor);
  Ok
    {|
      hashMap_num_entries := 0%usize;
      hashMap_max_load_factor := max_load_factor;
      hashMap_max_load := i1;
      hashMap_saturated := false;
      hashMap_slots := slots
    |}
.

(** [hashmap::{hashmap::HashMap<T>}::new]:
    Source: 'tests/src/hashmap.rs', lines 91:4-100:5 *)
Definition hashMap_new (T : Type) (n : nat) : result (HashMap_t T) :=
  hashMap_new_with_capacity T n 32%usize
    {| fraction_dividend := 4%usize; fraction_divisor := 5%usize |}
.

(** [hashmap::{hashmap::HashMap<T>}::clear]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 106:8-109:9 *)
Fixpoint hashMap_clear_loop
  {T : Type} (n : nat) (slots : alloc_vec_Vec (AList_t T)) (i : usize) :
  result (alloc_vec_Vec (AList_t T))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    let i1 := alloc_vec_Vec_len slots in
    if i s< i1
    then (
      p <-
        alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceInst
          (AList_t T)) slots i;
      let (_, index_mut_back) := p in
      i2 <- usize_add i 1%usize;
      let slots1 := index_mut_back AList_Nil in
      hashMap_clear_loop n1 slots1 i2)
    else Ok slots
  end
.

(** [hashmap::{hashmap::HashMap<T>}::clear]:
    Source: 'tests/src/hashmap.rs', lines 102:4-110:5 *)
Definition hashMap_clear
  {T : Type} (n : nat) (self : HashMap_t T) : result (HashMap_t T) :=
  hm <- hashMap_clear_loop n self.(hashMap_slots) 0%usize;
  Ok
    {|
      hashMap_num_entries := 0%usize;
      hashMap_max_load_factor := self.(hashMap_max_load_factor);
      hashMap_max_load := self.(hashMap_max_load);
      hashMap_saturated := self.(hashMap_saturated);
      hashMap_slots := hm
    |}
.

(** [hashmap::{hashmap::HashMap<T>}::len]:
    Source: 'tests/src/hashmap.rs', lines 112:4-114:5 *)
Definition hashMap_len {T : Type} (self : HashMap_t T) : result usize :=
  Ok self.(hashMap_num_entries)
.

(** [hashmap::{hashmap::HashMap<T>}::insert_in_list]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 1:0-135:9 *)
Fixpoint hashMap_insert_in_list_loop
  {T : Type} (n : nat) (key : usize) (value : T) (ls : AList_t T) :
  result (bool * (AList_t T))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | AList_Cons ckey cvalue tl =>
      if ckey s= key
      then Ok (false, AList_Cons ckey value tl)
      else (
        p <- hashMap_insert_in_list_loop n1 key value tl;
        let (b, tl1) := p in
        Ok (b, AList_Cons ckey cvalue tl1))
    | AList_Nil => Ok (true, AList_Cons key value AList_Nil)
    end
  end
.

(** [hashmap::{hashmap::HashMap<T>}::insert_in_list]:
    Source: 'tests/src/hashmap.rs', lines 119:4-136:5 *)
Definition hashMap_insert_in_list
  {T : Type} (n : nat) (key : usize) (value : T) (ls : AList_t T) :
  result (bool * (AList_t T))
  :=
  hashMap_insert_in_list_loop n key value ls
.

(** [hashmap::{hashmap::HashMap<T>}::insert_no_resize]:
    Source: 'tests/src/hashmap.rs', lines 139:4-147:5 *)
Definition hashMap_insert_no_resize
  {T : Type} (n : nat) (self : HashMap_t T) (key : usize) (value : T) :
  result (HashMap_t T)
  :=
  hash <- hash_key key;
  let i := alloc_vec_Vec_len self.(hashMap_slots) in
  hash_mod <- usize_rem hash i;
  p <-
    alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceInst (AList_t
      T)) self.(hashMap_slots) hash_mod;
  let (a, index_mut_back) := p in
  p1 <- hashMap_insert_in_list n key value a;
  let (inserted, a1) := p1 in
  if inserted
  then (
    i1 <- usize_add self.(hashMap_num_entries) 1%usize;
    let v := index_mut_back a1 in
    Ok
      {|
        hashMap_num_entries := i1;
        hashMap_max_load_factor := self.(hashMap_max_load_factor);
        hashMap_max_load := self.(hashMap_max_load);
        hashMap_saturated := self.(hashMap_saturated);
        hashMap_slots := v
      |})
  else
    let v := index_mut_back a1 in
    Ok
      {|
        hashMap_num_entries := self.(hashMap_num_entries);
        hashMap_max_load_factor := self.(hashMap_max_load_factor);
        hashMap_max_load := self.(hashMap_max_load);
        hashMap_saturated := self.(hashMap_saturated);
        hashMap_slots := v
      |}
.

(** [hashmap::{hashmap::HashMap<T>}::move_elements_from_list]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 201:12-208:17 *)
Fixpoint hashMap_move_elements_from_list_loop
  {T : Type} (n : nat) (ntable : HashMap_t T) (ls : AList_t T) :
  result (HashMap_t T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | AList_Cons k v tl =>
      ntable1 <- hashMap_insert_no_resize n1 ntable k v;
      hashMap_move_elements_from_list_loop n1 ntable1 tl
    | AList_Nil => Ok ntable
    end
  end
.

(** [hashmap::{hashmap::HashMap<T>}::move_elements_from_list]:
    Source: 'tests/src/hashmap.rs', lines 198:4-211:5 *)
Definition hashMap_move_elements_from_list
  {T : Type} (n : nat) (ntable : HashMap_t T) (ls : AList_t T) :
  result (HashMap_t T)
  :=
  hashMap_move_elements_from_list_loop n ntable ls
.

(** [hashmap::{hashmap::HashMap<T>}::move_elements]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 187:8-194:9 *)
Fixpoint hashMap_move_elements_loop
  {T : Type} (n : nat) (ntable : HashMap_t T)
  (slots : alloc_vec_Vec (AList_t T)) (i : usize) :
  result ((HashMap_t T) * (alloc_vec_Vec (AList_t T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    let i1 := alloc_vec_Vec_len slots in
    if i s< i1
    then (
      p <-
        alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceInst
          (AList_t T)) slots i;
      let (a, index_mut_back) := p in
      let (ls, a1) := core_mem_replace a AList_Nil in
      ntable1 <- hashMap_move_elements_from_list n1 ntable ls;
      i2 <- usize_add i 1%usize;
      let slots1 := index_mut_back a1 in
      hashMap_move_elements_loop n1 ntable1 slots1 i2)
    else Ok (ntable, slots)
  end
.

(** [hashmap::{hashmap::HashMap<T>}::move_elements]:
    Source: 'tests/src/hashmap.rs', lines 185:4-195:5 *)
Definition hashMap_move_elements
  {T : Type} (n : nat) (ntable : HashMap_t T)
  (slots : alloc_vec_Vec (AList_t T)) :
  result ((HashMap_t T) * (alloc_vec_Vec (AList_t T)))
  :=
  hashMap_move_elements_loop n ntable slots 0%usize
.

(** [hashmap::{hashmap::HashMap<T>}::try_resize]:
    Source: 'tests/src/hashmap.rs', lines 162:4-181:5 *)
Definition hashMap_try_resize
  {T : Type} (n : nat) (self : HashMap_t T) : result (HashMap_t T) :=
  let capacity := alloc_vec_Vec_len self.(hashMap_slots) in
  n1 <- usize_div core_usize_max 2%usize;
  i <- usize_div n1 self.(hashMap_max_load_factor).(fraction_dividend);
  if capacity s<= i
  then (
    i1 <- usize_mul capacity 2%usize;
    ntable <- hashMap_new_with_capacity T n i1 self.(hashMap_max_load_factor);
    p <- hashMap_move_elements n ntable self.(hashMap_slots);
    let (ntable1, _) := p in
    Ok
      {|
        hashMap_num_entries := self.(hashMap_num_entries);
        hashMap_max_load_factor := self.(hashMap_max_load_factor);
        hashMap_max_load := ntable1.(hashMap_max_load);
        hashMap_saturated := self.(hashMap_saturated);
        hashMap_slots := ntable1.(hashMap_slots)
      |})
  else
    Ok
      {|
        hashMap_num_entries := self.(hashMap_num_entries);
        hashMap_max_load_factor := self.(hashMap_max_load_factor);
        hashMap_max_load := self.(hashMap_max_load);
        hashMap_saturated := true;
        hashMap_slots := self.(hashMap_slots)
      |}
.

(** [hashmap::{hashmap::HashMap<T>}::insert]:
    Source: 'tests/src/hashmap.rs', lines 151:4-158:5 *)
Definition hashMap_insert
  {T : Type} (n : nat) (self : HashMap_t T) (key : usize) (value : T) :
  result (HashMap_t T)
  :=
  self1 <- hashMap_insert_no_resize n self key value;
  i <- hashMap_len self1;
  if i s> self1.(hashMap_max_load)
  then
    if self1.(hashMap_saturated)
    then
      Ok
        {|
          hashMap_num_entries := self1.(hashMap_num_entries);
          hashMap_max_load_factor := self1.(hashMap_max_load_factor);
          hashMap_max_load := self1.(hashMap_max_load);
          hashMap_saturated := true;
          hashMap_slots := self1.(hashMap_slots)
        |}
    else
      hashMap_try_resize n
        {|
          hashMap_num_entries := self1.(hashMap_num_entries);
          hashMap_max_load_factor := self1.(hashMap_max_load_factor);
          hashMap_max_load := self1.(hashMap_max_load);
          hashMap_saturated := false;
          hashMap_slots := self1.(hashMap_slots)
        |}
  else Ok self1
.

(** [hashmap::{hashmap::HashMap<T>}::contains_key_in_list]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 1:0-233:9 *)
Fixpoint hashMap_contains_key_in_list_loop
  {T : Type} (n : nat) (key : usize) (ls : AList_t T) : result bool :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | AList_Cons ckey _ tl =>
      if ckey s= key
      then Ok true
      else hashMap_contains_key_in_list_loop n1 key tl
    | AList_Nil => Ok false
    end
  end
.

(** [hashmap::{hashmap::HashMap<T>}::contains_key_in_list]:
    Source: 'tests/src/hashmap.rs', lines 221:4-234:5 *)
Definition hashMap_contains_key_in_list
  {T : Type} (n : nat) (key : usize) (ls : AList_t T) : result bool :=
  hashMap_contains_key_in_list_loop n key ls
.

(** [hashmap::{hashmap::HashMap<T>}::contains_key]:
    Source: 'tests/src/hashmap.rs', lines 214:4-218:5 *)
Definition hashMap_contains_key
  {T : Type} (n : nat) (self : HashMap_t T) (key : usize) : result bool :=
  hash <- hash_key key;
  let i := alloc_vec_Vec_len self.(hashMap_slots) in
  hash_mod <- usize_rem hash i;
  a <-
    alloc_vec_Vec_index (core_slice_index_SliceIndexUsizeSliceInst (AList_t T))
      self.(hashMap_slots) hash_mod;
  hashMap_contains_key_in_list n key a
.

(** [hashmap::{hashmap::HashMap<T>}::get_in_list]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 240:8-248:5 *)
Fixpoint hashMap_get_in_list_loop
  {T : Type} (n : nat) (key : usize) (ls : AList_t T) : result (option T) :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | AList_Cons ckey cvalue tl =>
      if ckey s= key
      then Ok (Some cvalue)
      else hashMap_get_in_list_loop n1 key tl
    | AList_Nil => Ok None
    end
  end
.

(** [hashmap::{hashmap::HashMap<T>}::get_in_list]:
    Source: 'tests/src/hashmap.rs', lines 239:4-248:5 *)
Definition hashMap_get_in_list
  {T : Type} (n : nat) (key : usize) (ls : AList_t T) : result (option T) :=
  hashMap_get_in_list_loop n key ls
.

(** [hashmap::{hashmap::HashMap<T>}::get]:
    Source: 'tests/src/hashmap.rs', lines 250:4-254:5 *)
Definition hashMap_get
  {T : Type} (n : nat) (self : HashMap_t T) (key : usize) :
  result (option T)
  :=
  hash <- hash_key key;
  let i := alloc_vec_Vec_len self.(hashMap_slots) in
  hash_mod <- usize_rem hash i;
  a <-
    alloc_vec_Vec_index (core_slice_index_SliceIndexUsizeSliceInst (AList_t T))
      self.(hashMap_slots) hash_mod;
  hashMap_get_in_list n key a
.

(** [hashmap::{hashmap::HashMap<T>}::get_mut_in_list]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 257:8-265:5 *)
Fixpoint hashMap_get_mut_in_list_loop
  {T : Type} (n : nat) (ls : AList_t T) (key : usize) :
  result ((option T) * (option T -> AList_t T))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | AList_Cons ckey cvalue tl =>
      if ckey s= key
      then
        let back :=
          fun (ret : option T) =>
            let t := match ret with | Some t1 => t1 | _ => cvalue end in
            AList_Cons ckey t tl in
        Ok (Some cvalue, back)
      else (
        p <- hashMap_get_mut_in_list_loop n1 tl key;
        let (o, back) := p in
        let back1 :=
          fun (ret : option T) =>
            let tl1 := back ret in AList_Cons ckey cvalue tl1 in
        Ok (o, back1))
    | AList_Nil =>
      let back := fun (ret : option T) => AList_Nil in Ok (None, back)
    end
  end
.

(** [hashmap::{hashmap::HashMap<T>}::get_mut_in_list]:
    Source: 'tests/src/hashmap.rs', lines 256:4-265:5 *)
Definition hashMap_get_mut_in_list
  {T : Type} (n : nat) (ls : AList_t T) (key : usize) :
  result ((option T) * (option T -> AList_t T))
  :=
  hashMap_get_mut_in_list_loop n ls key
.

(** [hashmap::{hashmap::HashMap<T>}::get_mut]:
    Source: 'tests/src/hashmap.rs', lines 268:4-272:5 *)
Definition hashMap_get_mut
  {T : Type} (n : nat) (self : HashMap_t T) (key : usize) :
  result ((option T) * (option T -> HashMap_t T))
  :=
  hash <- hash_key key;
  let i := alloc_vec_Vec_len self.(hashMap_slots) in
  hash_mod <- usize_rem hash i;
  p <-
    alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceInst (AList_t
      T)) self.(hashMap_slots) hash_mod;
  let (a, index_mut_back) := p in
  p1 <- hashMap_get_mut_in_list n a key;
  let (o, get_mut_in_list_back) := p1 in
  let back :=
    fun (ret : option T) =>
      let a1 := get_mut_in_list_back ret in
      let v := index_mut_back a1 in
      {|
        hashMap_num_entries := self.(hashMap_num_entries);
        hashMap_max_load_factor := self.(hashMap_max_load_factor);
        hashMap_max_load := self.(hashMap_max_load);
        hashMap_saturated := self.(hashMap_saturated);
        hashMap_slots := v
      |} in
  Ok (o, back)
.

(** [hashmap::{hashmap::HashMap<T>}::remove_from_list]: loop 0:
    Source: 'tests/src/hashmap.rs', lines 1:0-299:17 *)
Fixpoint hashMap_remove_from_list_loop
  {T : Type} (n : nat) (key : usize) (ls : AList_t T) :
  result ((option T) * (AList_t T))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | AList_Cons ckey t tl =>
      if ckey s= key
      then
        let (mv_ls, _) := core_mem_replace ls AList_Nil in
        match mv_ls with
        | AList_Cons _ cvalue tl1 => Ok (Some cvalue, tl1)
        | AList_Nil => Fail_ Failure
        end
      else (
        p <- hashMap_remove_from_list_loop n1 key tl;
        let (o, tl1) := p in
        Ok (o, AList_Cons ckey t tl1))
    | AList_Nil => Ok (None, AList_Nil)
    end
  end
.

(** [hashmap::{hashmap::HashMap<T>}::remove_from_list]:
    Source: 'tests/src/hashmap.rs', lines 276:4-302:5 *)
Definition hashMap_remove_from_list
  {T : Type} (n : nat) (key : usize) (ls : AList_t T) :
  result ((option T) * (AList_t T))
  :=
  hashMap_remove_from_list_loop n key ls
.

(** [hashmap::{hashmap::HashMap<T>}::remove]:
    Source: 'tests/src/hashmap.rs', lines 305:4-317:5 *)
Definition hashMap_remove
  {T : Type} (n : nat) (self : HashMap_t T) (key : usize) :
  result ((option T) * (HashMap_t T))
  :=
  hash <- hash_key key;
  let i := alloc_vec_Vec_len self.(hashMap_slots) in
  hash_mod <- usize_rem hash i;
  p <-
    alloc_vec_Vec_index_mut (core_slice_index_SliceIndexUsizeSliceInst (AList_t
      T)) self.(hashMap_slots) hash_mod;
  let (a, index_mut_back) := p in
  p1 <- hashMap_remove_from_list n key a;
  let (x, a1) := p1 in
  match x with
  | None =>
    let v := index_mut_back a1 in
    Ok (None,
      {|
        hashMap_num_entries := self.(hashMap_num_entries);
        hashMap_max_load_factor := self.(hashMap_max_load_factor);
        hashMap_max_load := self.(hashMap_max_load);
        hashMap_saturated := self.(hashMap_saturated);
        hashMap_slots := v
      |})
  | Some _ =>
    i1 <- usize_sub self.(hashMap_num_entries) 1%usize;
    let v := index_mut_back a1 in
    Ok (x,
      {|
        hashMap_num_entries := i1;
        hashMap_max_load_factor := self.(hashMap_max_load_factor);
        hashMap_max_load := self.(hashMap_max_load);
        hashMap_saturated := self.(hashMap_saturated);
        hashMap_slots := v
      |})
  end
.

(** [hashmap::insert_on_disk]:
    Source: 'tests/src/hashmap.rs', lines 336:0-343:1 *)
Definition insert_on_disk
  (n : nat) (key : usize) (value : u64) (st : state) : result (state * unit) :=
  p <- utils_deserialize st;
  let (st1, hm) := p in
  hm1 <- hashMap_insert n hm key value;
  utils_serialize hm1 st1
.

End Hashmap_Funs.
