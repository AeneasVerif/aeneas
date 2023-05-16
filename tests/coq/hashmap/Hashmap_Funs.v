(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [hashmap]: function definitions *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Local Open Scope Primitives_scope.
Require Export Hashmap_Types.
Import Hashmap_Types.
Module Hashmap_Funs.

(** [hashmap::hash_key] *)
Definition hash_key_fwd (k : usize) : result usize :=
  Return k.

(** [hashmap::HashMap::{0}::allocate_slots] *)
Fixpoint hash_map_allocate_slots_loop_fwd
  (T : Type) (n : nat) (slots : vec (List_t T)) (n0 : usize) :
  result (vec (List_t T))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if n0 s> 0%usize
    then (
      slots0 <- vec_push_back (List_t T) slots ListNil;
      n2 <- usize_sub n0 1%usize;
      hash_map_allocate_slots_loop_fwd T n1 slots0 n2)
    else Return slots
  end
.

(** [hashmap::HashMap::{0}::allocate_slots] *)
Definition hash_map_allocate_slots_fwd
  (T : Type) (n : nat) (slots : vec (List_t T)) (n0 : usize) :
  result (vec (List_t T))
  :=
  hash_map_allocate_slots_loop_fwd T n slots n0
.

(** [hashmap::HashMap::{0}::new_with_capacity] *)
Definition hash_map_new_with_capacity_fwd
  (T : Type) (n : nat) (capacity : usize) (max_load_dividend : usize)
  (max_load_divisor : usize) :
  result (Hash_map_t T)
  :=
  let v := vec_new (List_t T) in
  slots <- hash_map_allocate_slots_fwd T n v capacity;
  i <- usize_mul capacity max_load_dividend;
  i0 <- usize_div i max_load_divisor;
  Return
    {|
      Hash_map_num_entries := 0%usize;
      Hash_map_max_load_factor := (max_load_dividend, max_load_divisor);
      Hash_map_max_load := i0;
      Hash_map_slots := slots
    |}
.

(** [hashmap::HashMap::{0}::new] *)
Definition hash_map_new_fwd (T : Type) (n : nat) : result (Hash_map_t T) :=
  hash_map_new_with_capacity_fwd T n 32%usize 4%usize 5%usize
.

(** [hashmap::HashMap::{0}::clear] *)
Fixpoint hash_map_clear_loop_fwd_back
  (T : Type) (n : nat) (slots : vec (List_t T)) (i : usize) :
  result (vec (List_t T))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    let i0 := vec_len (List_t T) slots in
    if i s< i0
    then (
      i1 <- usize_add i 1%usize;
      slots0 <- vec_index_mut_back (List_t T) slots i ListNil;
      hash_map_clear_loop_fwd_back T n0 slots0 i1)
    else Return slots
  end
.

(** [hashmap::HashMap::{0}::clear] *)
Definition hash_map_clear_fwd_back
  (T : Type) (n : nat) (self : Hash_map_t T) : result (Hash_map_t T) :=
  v <- hash_map_clear_loop_fwd_back T n self.(Hash_map_slots) 0%usize;
  Return
    {|
      Hash_map_num_entries := 0%usize;
      Hash_map_max_load_factor := self.(Hash_map_max_load_factor);
      Hash_map_max_load := self.(Hash_map_max_load);
      Hash_map_slots := v
    |}
.

(** [hashmap::HashMap::{0}::len] *)
Definition hash_map_len_fwd (T : Type) (self : Hash_map_t T) : result usize :=
  Return self.(Hash_map_num_entries)
.

(** [hashmap::HashMap::{0}::insert_in_list] *)
Fixpoint hash_map_insert_in_list_loop_fwd
  (T : Type) (n : nat) (key : usize) (value : T) (ls : List_t T) :
  result bool
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey cvalue tl =>
      if ckey s= key
      then Return false
      else hash_map_insert_in_list_loop_fwd T n0 key value tl
    | ListNil => Return true
    end
  end
.

(** [hashmap::HashMap::{0}::insert_in_list] *)
Definition hash_map_insert_in_list_fwd
  (T : Type) (n : nat) (key : usize) (value : T) (ls : List_t T) :
  result bool
  :=
  hash_map_insert_in_list_loop_fwd T n key value ls
.

(** [hashmap::HashMap::{0}::insert_in_list] *)
Fixpoint hash_map_insert_in_list_loop_back
  (T : Type) (n : nat) (key : usize) (value : T) (ls : List_t T) :
  result (List_t T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey cvalue tl =>
      if ckey s= key
      then Return (ListCons ckey value tl)
      else (
        tl0 <- hash_map_insert_in_list_loop_back T n0 key value tl;
        Return (ListCons ckey cvalue tl0))
    | ListNil => let l := ListNil in Return (ListCons key value l)
    end
  end
.

(** [hashmap::HashMap::{0}::insert_in_list] *)
Definition hash_map_insert_in_list_back
  (T : Type) (n : nat) (key : usize) (value : T) (ls : List_t T) :
  result (List_t T)
  :=
  hash_map_insert_in_list_loop_back T n key value ls
.

(** [hashmap::HashMap::{0}::insert_no_resize] *)
Definition hash_map_insert_no_resize_fwd_back
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) (value : T) :
  result (Hash_map_t T)
  :=
  hash <- hash_key_fwd key;
  let i := vec_len (List_t T) self.(Hash_map_slots) in
  hash_mod <- usize_rem hash i;
  l <- vec_index_mut_fwd (List_t T) self.(Hash_map_slots) hash_mod;
  inserted <- hash_map_insert_in_list_fwd T n key value l;
  if inserted
  then (
    i0 <- usize_add self.(Hash_map_num_entries) 1%usize;
    l0 <- hash_map_insert_in_list_back T n key value l;
    v <- vec_index_mut_back (List_t T) self.(Hash_map_slots) hash_mod l0;
    Return
      {|
        Hash_map_num_entries := i0;
        Hash_map_max_load_factor := self.(Hash_map_max_load_factor);
        Hash_map_max_load := self.(Hash_map_max_load);
        Hash_map_slots := v
      |})
  else (
    l0 <- hash_map_insert_in_list_back T n key value l;
    v <- vec_index_mut_back (List_t T) self.(Hash_map_slots) hash_mod l0;
    Return
      {|
        Hash_map_num_entries := self.(Hash_map_num_entries);
        Hash_map_max_load_factor := self.(Hash_map_max_load_factor);
        Hash_map_max_load := self.(Hash_map_max_load);
        Hash_map_slots := v
      |})
.

(** [core::num::u32::{9}::MAX] *)
Definition core_num_u32_max_body : result u32 := Return 4294967295%u32.
Definition core_num_u32_max_c : u32 := core_num_u32_max_body%global.

(** [hashmap::HashMap::{0}::move_elements_from_list] *)
Fixpoint hash_map_move_elements_from_list_loop_fwd_back
  (T : Type) (n : nat) (ntable : Hash_map_t T) (ls : List_t T) :
  result (Hash_map_t T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons k v tl =>
      ntable0 <- hash_map_insert_no_resize_fwd_back T n0 ntable k v;
      hash_map_move_elements_from_list_loop_fwd_back T n0 ntable0 tl
    | ListNil => Return ntable
    end
  end
.

(** [hashmap::HashMap::{0}::move_elements_from_list] *)
Definition hash_map_move_elements_from_list_fwd_back
  (T : Type) (n : nat) (ntable : Hash_map_t T) (ls : List_t T) :
  result (Hash_map_t T)
  :=
  hash_map_move_elements_from_list_loop_fwd_back T n ntable ls
.

(** [hashmap::HashMap::{0}::move_elements] *)
Fixpoint hash_map_move_elements_loop_fwd_back
  (T : Type) (n : nat) (ntable : Hash_map_t T) (slots : vec (List_t T))
  (i : usize) :
  result ((Hash_map_t T) * (vec (List_t T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    let i0 := vec_len (List_t T) slots in
    if i s< i0
    then (
      l <- vec_index_mut_fwd (List_t T) slots i;
      let ls := mem_replace_fwd (List_t T) l ListNil in
      ntable0 <- hash_map_move_elements_from_list_fwd_back T n0 ntable ls;
      i1 <- usize_add i 1%usize;
      let l0 := mem_replace_back (List_t T) l ListNil in
      slots0 <- vec_index_mut_back (List_t T) slots i l0;
      hash_map_move_elements_loop_fwd_back T n0 ntable0 slots0 i1)
    else Return (ntable, slots)
  end
.

(** [hashmap::HashMap::{0}::move_elements] *)
Definition hash_map_move_elements_fwd_back
  (T : Type) (n : nat) (ntable : Hash_map_t T) (slots : vec (List_t T))
  (i : usize) :
  result ((Hash_map_t T) * (vec (List_t T)))
  :=
  hash_map_move_elements_loop_fwd_back T n ntable slots i
.

(** [hashmap::HashMap::{0}::try_resize] *)
Definition hash_map_try_resize_fwd_back
  (T : Type) (n : nat) (self : Hash_map_t T) : result (Hash_map_t T) :=
  max_usize <- scalar_cast U32 Usize core_num_u32_max_c;
  let capacity := vec_len (List_t T) self.(Hash_map_slots) in
  n1 <- usize_div max_usize 2%usize;
  let (i, i0) := self.(Hash_map_max_load_factor) in
  i1 <- usize_div n1 i;
  if capacity s<= i1
  then (
    i2 <- usize_mul capacity 2%usize;
    ntable <- hash_map_new_with_capacity_fwd T n i2 i i0;
    p <-
      hash_map_move_elements_fwd_back T n ntable self.(Hash_map_slots) 0%usize;
    let (ntable0, _) := p in
    Return
      {|
        Hash_map_num_entries := self.(Hash_map_num_entries);
        Hash_map_max_load_factor := (i, i0);
        Hash_map_max_load := ntable0.(Hash_map_max_load);
        Hash_map_slots := ntable0.(Hash_map_slots)
      |})
  else
    Return
      {|
        Hash_map_num_entries := self.(Hash_map_num_entries);
        Hash_map_max_load_factor := (i, i0);
        Hash_map_max_load := self.(Hash_map_max_load);
        Hash_map_slots := self.(Hash_map_slots)
      |}
.

(** [hashmap::HashMap::{0}::insert] *)
Definition hash_map_insert_fwd_back
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) (value : T) :
  result (Hash_map_t T)
  :=
  self0 <- hash_map_insert_no_resize_fwd_back T n self key value;
  i <- hash_map_len_fwd T self0;
  if i s> self0.(Hash_map_max_load)
  then hash_map_try_resize_fwd_back T n self0
  else Return self0
.

(** [hashmap::HashMap::{0}::contains_key_in_list] *)
Fixpoint hash_map_contains_key_in_list_loop_fwd
  (T : Type) (n : nat) (key : usize) (ls : List_t T) : result bool :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey t tl =>
      if ckey s= key
      then Return true
      else hash_map_contains_key_in_list_loop_fwd T n0 key tl
    | ListNil => Return false
    end
  end
.

(** [hashmap::HashMap::{0}::contains_key_in_list] *)
Definition hash_map_contains_key_in_list_fwd
  (T : Type) (n : nat) (key : usize) (ls : List_t T) : result bool :=
  hash_map_contains_key_in_list_loop_fwd T n key ls
.

(** [hashmap::HashMap::{0}::contains_key] *)
Definition hash_map_contains_key_fwd
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) : result bool :=
  hash <- hash_key_fwd key;
  let i := vec_len (List_t T) self.(Hash_map_slots) in
  hash_mod <- usize_rem hash i;
  l <- vec_index_fwd (List_t T) self.(Hash_map_slots) hash_mod;
  hash_map_contains_key_in_list_fwd T n key l
.

(** [hashmap::HashMap::{0}::get_in_list] *)
Fixpoint hash_map_get_in_list_loop_fwd
  (T : Type) (n : nat) (key : usize) (ls : List_t T) : result T :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey cvalue tl =>
      if ckey s= key
      then Return cvalue
      else hash_map_get_in_list_loop_fwd T n0 key tl
    | ListNil => Fail_ Failure
    end
  end
.

(** [hashmap::HashMap::{0}::get_in_list] *)
Definition hash_map_get_in_list_fwd
  (T : Type) (n : nat) (key : usize) (ls : List_t T) : result T :=
  hash_map_get_in_list_loop_fwd T n key ls
.

(** [hashmap::HashMap::{0}::get] *)
Definition hash_map_get_fwd
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) : result T :=
  hash <- hash_key_fwd key;
  let i := vec_len (List_t T) self.(Hash_map_slots) in
  hash_mod <- usize_rem hash i;
  l <- vec_index_fwd (List_t T) self.(Hash_map_slots) hash_mod;
  hash_map_get_in_list_fwd T n key l
.

(** [hashmap::HashMap::{0}::get_mut_in_list] *)
Fixpoint hash_map_get_mut_in_list_loop_fwd
  (T : Type) (n : nat) (ls : List_t T) (key : usize) : result T :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey cvalue tl =>
      if ckey s= key
      then Return cvalue
      else hash_map_get_mut_in_list_loop_fwd T n0 tl key
    | ListNil => Fail_ Failure
    end
  end
.

(** [hashmap::HashMap::{0}::get_mut_in_list] *)
Definition hash_map_get_mut_in_list_fwd
  (T : Type) (n : nat) (ls : List_t T) (key : usize) : result T :=
  hash_map_get_mut_in_list_loop_fwd T n ls key
.

(** [hashmap::HashMap::{0}::get_mut_in_list] *)
Fixpoint hash_map_get_mut_in_list_loop_back
  (T : Type) (n : nat) (ls : List_t T) (key : usize) (ret : T) :
  result (List_t T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey cvalue tl =>
      if ckey s= key
      then Return (ListCons ckey ret tl)
      else (
        tl0 <- hash_map_get_mut_in_list_loop_back T n0 tl key ret;
        Return (ListCons ckey cvalue tl0))
    | ListNil => Fail_ Failure
    end
  end
.

(** [hashmap::HashMap::{0}::get_mut_in_list] *)
Definition hash_map_get_mut_in_list_back
  (T : Type) (n : nat) (ls : List_t T) (key : usize) (ret : T) :
  result (List_t T)
  :=
  hash_map_get_mut_in_list_loop_back T n ls key ret
.

(** [hashmap::HashMap::{0}::get_mut] *)
Definition hash_map_get_mut_fwd
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) : result T :=
  hash <- hash_key_fwd key;
  let i := vec_len (List_t T) self.(Hash_map_slots) in
  hash_mod <- usize_rem hash i;
  l <- vec_index_mut_fwd (List_t T) self.(Hash_map_slots) hash_mod;
  hash_map_get_mut_in_list_fwd T n l key
.

(** [hashmap::HashMap::{0}::get_mut] *)
Definition hash_map_get_mut_back
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) (ret : T) :
  result (Hash_map_t T)
  :=
  hash <- hash_key_fwd key;
  let i := vec_len (List_t T) self.(Hash_map_slots) in
  hash_mod <- usize_rem hash i;
  l <- vec_index_mut_fwd (List_t T) self.(Hash_map_slots) hash_mod;
  l0 <- hash_map_get_mut_in_list_back T n l key ret;
  v <- vec_index_mut_back (List_t T) self.(Hash_map_slots) hash_mod l0;
  Return
    {|
      Hash_map_num_entries := self.(Hash_map_num_entries);
      Hash_map_max_load_factor := self.(Hash_map_max_load_factor);
      Hash_map_max_load := self.(Hash_map_max_load);
      Hash_map_slots := v
    |}
.

(** [hashmap::HashMap::{0}::remove_from_list] *)
Fixpoint hash_map_remove_from_list_loop_fwd
  (T : Type) (n : nat) (key : usize) (ls : List_t T) : result (option T) :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey t tl =>
      if ckey s= key
      then
        let mv_ls := mem_replace_fwd (List_t T) (ListCons ckey t tl) ListNil in
        match mv_ls with
        | ListCons i cvalue tl0 => Return (Some cvalue)
        | ListNil => Fail_ Failure
        end
      else hash_map_remove_from_list_loop_fwd T n0 key tl
    | ListNil => Return None
    end
  end
.

(** [hashmap::HashMap::{0}::remove_from_list] *)
Definition hash_map_remove_from_list_fwd
  (T : Type) (n : nat) (key : usize) (ls : List_t T) : result (option T) :=
  hash_map_remove_from_list_loop_fwd T n key ls
.

(** [hashmap::HashMap::{0}::remove_from_list] *)
Fixpoint hash_map_remove_from_list_loop_back
  (T : Type) (n : nat) (key : usize) (ls : List_t T) : result (List_t T) :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey t tl =>
      if ckey s= key
      then
        let mv_ls := mem_replace_fwd (List_t T) (ListCons ckey t tl) ListNil in
        match mv_ls with
        | ListCons i cvalue tl0 => Return tl0
        | ListNil => Fail_ Failure
        end
      else (
        tl0 <- hash_map_remove_from_list_loop_back T n0 key tl;
        Return (ListCons ckey t tl0))
    | ListNil => Return ListNil
    end
  end
.

(** [hashmap::HashMap::{0}::remove_from_list] *)
Definition hash_map_remove_from_list_back
  (T : Type) (n : nat) (key : usize) (ls : List_t T) : result (List_t T) :=
  hash_map_remove_from_list_loop_back T n key ls
.

(** [hashmap::HashMap::{0}::remove] *)
Definition hash_map_remove_fwd
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) :
  result (option T)
  :=
  hash <- hash_key_fwd key;
  let i := vec_len (List_t T) self.(Hash_map_slots) in
  hash_mod <- usize_rem hash i;
  l <- vec_index_mut_fwd (List_t T) self.(Hash_map_slots) hash_mod;
  x <- hash_map_remove_from_list_fwd T n key l;
  match x with
  | None => Return None
  | Some x0 =>
    _ <- usize_sub self.(Hash_map_num_entries) 1%usize; Return (Some x0)
  end
.

(** [hashmap::HashMap::{0}::remove] *)
Definition hash_map_remove_back
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) :
  result (Hash_map_t T)
  :=
  hash <- hash_key_fwd key;
  let i := vec_len (List_t T) self.(Hash_map_slots) in
  hash_mod <- usize_rem hash i;
  l <- vec_index_mut_fwd (List_t T) self.(Hash_map_slots) hash_mod;
  x <- hash_map_remove_from_list_fwd T n key l;
  match x with
  | None =>
    l0 <- hash_map_remove_from_list_back T n key l;
    v <- vec_index_mut_back (List_t T) self.(Hash_map_slots) hash_mod l0;
    Return
      {|
        Hash_map_num_entries := self.(Hash_map_num_entries);
        Hash_map_max_load_factor := self.(Hash_map_max_load_factor);
        Hash_map_max_load := self.(Hash_map_max_load);
        Hash_map_slots := v
      |}
  | Some x0 =>
    i0 <- usize_sub self.(Hash_map_num_entries) 1%usize;
    l0 <- hash_map_remove_from_list_back T n key l;
    v <- vec_index_mut_back (List_t T) self.(Hash_map_slots) hash_mod l0;
    Return
      {|
        Hash_map_num_entries := i0;
        Hash_map_max_load_factor := self.(Hash_map_max_load_factor);
        Hash_map_max_load := self.(Hash_map_max_load);
        Hash_map_slots := v
      |}
  end
.

(** [hashmap::test1] *)
Definition test1_fwd (n : nat) : result unit :=
  hm <- hash_map_new_fwd u64 n;
  hm0 <- hash_map_insert_fwd_back u64 n hm 0%usize 42%u64;
  hm1 <- hash_map_insert_fwd_back u64 n hm0 128%usize 18%u64;
  hm2 <- hash_map_insert_fwd_back u64 n hm1 1024%usize 138%u64;
  hm3 <- hash_map_insert_fwd_back u64 n hm2 1056%usize 256%u64;
  i <- hash_map_get_fwd u64 n hm3 128%usize;
  if negb (i s= 18%u64)
  then Fail_ Failure
  else (
    hm4 <- hash_map_get_mut_back u64 n hm3 1024%usize 56%u64;
    i0 <- hash_map_get_fwd u64 n hm4 1024%usize;
    if negb (i0 s= 56%u64)
    then Fail_ Failure
    else (
      x <- hash_map_remove_fwd u64 n hm4 1024%usize;
      match x with
      | None => Fail_ Failure
      | Some x0 =>
        if negb (x0 s= 56%u64)
        then Fail_ Failure
        else (
          hm5 <- hash_map_remove_back u64 n hm4 1024%usize;
          i1 <- hash_map_get_fwd u64 n hm5 0%usize;
          if negb (i1 s= 42%u64)
          then Fail_ Failure
          else (
            i2 <- hash_map_get_fwd u64 n hm5 128%usize;
            if negb (i2 s= 18%u64)
            then Fail_ Failure
            else (
              i3 <- hash_map_get_fwd u64 n hm5 1056%usize;
              if negb (i3 s= 256%u64) then Fail_ Failure else Return tt)))
      end))
.

End Hashmap_Funs .
