(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [hashmap]: function definitions *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Local Open Scope Primitives_scope.
Require Export Hashmap__Types .
Import Hashmap__Types .
Module Hashmap__Funs .

(** [hashmap::hash_key] *)
Definition hash_key_fwd (k : usize) : result usize := Return k .

(** [hashmap::HashMap::{0}::allocate_slots] *)
Fixpoint hash_map_allocate_slots_fwd
  (T : Type) (n : nat) (slots : vec (List_t T)) (n0 : usize) :
  result (vec (List_t T))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if n0 s= 0 %usize
    then Return slots
    else (
      slots0 <- vec_push_back (List_t T) slots ListNil;
      i <- usize_sub n0 1 %usize;
      v <- hash_map_allocate_slots_fwd T n1 slots0 i;
      Return v)
  end
  .

(** [hashmap::HashMap::{0}::new_with_capacity] *)
Definition hash_map_new_with_capacity_fwd
  (T : Type) (n : nat) (capacity : usize) (max_load_dividend : usize)
  (max_load_divisor : usize) :
  result (Hash_map_t T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    let v := vec_new (List_t T) in
    slots <- hash_map_allocate_slots_fwd T n0 v capacity;
    i <- usize_mul capacity max_load_dividend;
    i0 <- usize_div i max_load_divisor;
    Return (mkHash_map_t (0 %usize) (max_load_dividend, max_load_divisor) i0
      slots)
  end
  .

(** [hashmap::HashMap::{0}::new] *)
Definition hash_map_new_fwd (T : Type) (n : nat) : result (Hash_map_t T) :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    hm <-
      hash_map_new_with_capacity_fwd T n0 (32 %usize) (4 %usize) (5 %usize);
    Return hm
  end
  .

(** [hashmap::HashMap::{0}::clear_slots] *)
Fixpoint hash_map_clear_slots_fwd_back
  (T : Type) (n : nat) (slots : vec (List_t T)) (i : usize) :
  result (vec (List_t T))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    let i0 := vec_len (List_t T) slots in
    if i s< i0
    then (
      slots0 <- vec_index_mut_back (List_t T) slots i ListNil;
      i1 <- usize_add i 1 %usize;
      slots1 <- hash_map_clear_slots_fwd_back T n0 slots0 i1;
      Return slots1)
    else Return slots
  end
  .

(** [hashmap::HashMap::{0}::clear] *)
Definition hash_map_clear_fwd_back
  (T : Type) (n : nat) (self : Hash_map_t T) : result (Hash_map_t T) :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match self with
    | mkHash_map_t i p i0 v =>
      v0 <- hash_map_clear_slots_fwd_back T n0 v (0 %usize);
      Return (mkHash_map_t (0 %usize) p i0 v0)
    end
  end
  .

(** [hashmap::HashMap::{0}::len] *)
Definition hash_map_len_fwd (T : Type) (self : Hash_map_t T) : result usize :=
  match self with | mkHash_map_t i p i0 v => Return i end .

(** [hashmap::HashMap::{0}::insert_in_list] *)
Fixpoint hash_map_insert_in_list_fwd
  (T : Type) (n : nat) (key : usize) (value : T) (ls : List_t T) :
  result bool
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey cvalue ls0 =>
      if ckey s= key
      then Return false
      else (b <- hash_map_insert_in_list_fwd T n0 key value ls0; Return b)
    | ListNil => Return true
    end
  end
  .

(** [hashmap::HashMap::{0}::insert_in_list] *)
Fixpoint hash_map_insert_in_list_back
  (T : Type) (n : nat) (key : usize) (value : T) (ls : List_t T) :
  result (List_t T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey cvalue ls0 =>
      if ckey s= key
      then Return (ListCons ckey value ls0)
      else (
        ls1 <- hash_map_insert_in_list_back T n0 key value ls0;
        Return (ListCons ckey cvalue ls1))
    | ListNil => let l := ListNil in Return (ListCons key value l)
    end
  end
  .

(** [hashmap::HashMap::{0}::insert_no_resize] *)
Definition hash_map_insert_no_resize_fwd_back
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) (value : T) :
  result (Hash_map_t T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    hash <- hash_key_fwd key;
    match self with
    | mkHash_map_t i p i0 v =>
      let i1 := vec_len (List_t T) v in
      hash_mod <- usize_rem hash i1;
      l <- vec_index_mut_fwd (List_t T) v hash_mod;
      inserted <- hash_map_insert_in_list_fwd T n0 key value l;
      if inserted
      then (
        i2 <- usize_add i 1 %usize;
        l0 <- hash_map_insert_in_list_back T n0 key value l;
        v0 <- vec_index_mut_back (List_t T) v hash_mod l0;
        Return (mkHash_map_t i2 p i0 v0))
      else (
        l0 <- hash_map_insert_in_list_back T n0 key value l;
        v0 <- vec_index_mut_back (List_t T) v hash_mod l0;
        Return (mkHash_map_t i p i0 v0))
    end
  end
  .

(** [core::num::u32::{9}::MAX] *)
Definition core_num_u32_max_body : result u32 := Return (4294967295 %u32) .
Definition core_num_u32_max_c : u32 := core_num_u32_max_body%global .

(** [hashmap::HashMap::{0}::move_elements_from_list] *)
Fixpoint hash_map_move_elements_from_list_fwd_back
  (T : Type) (n : nat) (ntable : Hash_map_t T) (ls : List_t T) :
  result (Hash_map_t T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons k v tl =>
      ntable0 <- hash_map_insert_no_resize_fwd_back T n0 ntable k v;
      ntable1 <- hash_map_move_elements_from_list_fwd_back T n0 ntable0 tl;
      Return ntable1
    | ListNil => Return ntable
    end
  end
  .

(** [hashmap::HashMap::{0}::move_elements] *)
Fixpoint hash_map_move_elements_fwd_back
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
      let l0 := mem_replace_back (List_t T) l ListNil in
      slots0 <- vec_index_mut_back (List_t T) slots i l0;
      i1 <- usize_add i 1 %usize;
      p <- hash_map_move_elements_fwd_back T n0 ntable0 slots0 i1;
      let (ntable1, slots1) := p in
      Return (ntable1, slots1))
    else Return (ntable, slots)
  end
  .

(** [hashmap::HashMap::{0}::try_resize] *)
Definition hash_map_try_resize_fwd_back
  (T : Type) (n : nat) (self : Hash_map_t T) : result (Hash_map_t T) :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    max_usize <- scalar_cast U32 Usize core_num_u32_max_c;
    match self with
    | mkHash_map_t i p i0 v =>
      let capacity := vec_len (List_t T) v in
      n1 <- usize_div max_usize 2 %usize;
      let (i1, i2) := p in
      i3 <- usize_div n1 i1;
      if capacity s<= i3
      then (
        i4 <- usize_mul capacity 2 %usize;
        ntable <- hash_map_new_with_capacity_fwd T n0 i4 i1 i2;
        p0 <- hash_map_move_elements_fwd_back T n0 ntable v (0 %usize);
        let (ntable0, _) := p0 in
        match ntable0 with
        | mkHash_map_t i5 p1 i6 v0 => Return (mkHash_map_t i (i1, i2) i6 v0)
        end)
      else Return (mkHash_map_t i (i1, i2) i0 v)
    end
  end
  .

(** [hashmap::HashMap::{0}::insert] *)
Definition hash_map_insert_fwd_back
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) (value : T) :
  result (Hash_map_t T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    self0 <- hash_map_insert_no_resize_fwd_back T n0 self key value;
    i <- hash_map_len_fwd T self0;
    match self0 with
    | mkHash_map_t i0 p i1 v =>
      if i s> i1
      then (
        self1 <- hash_map_try_resize_fwd_back T n0 (mkHash_map_t i0 p i1 v);
        Return self1)
      else Return (mkHash_map_t i0 p i1 v)
    end
  end
  .

(** [hashmap::HashMap::{0}::contains_key_in_list] *)
Fixpoint hash_map_contains_key_in_list_fwd
  (T : Type) (n : nat) (key : usize) (ls : List_t T) : result bool :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey t ls0 =>
      if ckey s= key
      then Return true
      else (b <- hash_map_contains_key_in_list_fwd T n0 key ls0; Return b)
    | ListNil => Return false
    end
  end
  .

(** [hashmap::HashMap::{0}::contains_key] *)
Definition hash_map_contains_key_fwd
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) : result bool :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    hash <- hash_key_fwd key;
    match self with
    | mkHash_map_t i p i0 v =>
      let i1 := vec_len (List_t T) v in
      hash_mod <- usize_rem hash i1;
      l <- vec_index_fwd (List_t T) v hash_mod;
      b <- hash_map_contains_key_in_list_fwd T n0 key l;
      Return b
    end
  end
  .

(** [hashmap::HashMap::{0}::get_in_list] *)
Fixpoint hash_map_get_in_list_fwd
  (T : Type) (n : nat) (key : usize) (ls : List_t T) : result T :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey cvalue ls0 =>
      if ckey s= key
      then Return cvalue
      else (t <- hash_map_get_in_list_fwd T n0 key ls0; Return t)
    | ListNil => Fail_ Failure
    end
  end
  .

(** [hashmap::HashMap::{0}::get] *)
Definition hash_map_get_fwd
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) : result T :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    hash <- hash_key_fwd key;
    match self with
    | mkHash_map_t i p i0 v =>
      let i1 := vec_len (List_t T) v in
      hash_mod <- usize_rem hash i1;
      l <- vec_index_fwd (List_t T) v hash_mod;
      t <- hash_map_get_in_list_fwd T n0 key l;
      Return t
    end
  end
  .

(** [hashmap::HashMap::{0}::get_mut_in_list] *)
Fixpoint hash_map_get_mut_in_list_fwd
  (T : Type) (n : nat) (key : usize) (ls : List_t T) : result T :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey cvalue ls0 =>
      if ckey s= key
      then Return cvalue
      else (t <- hash_map_get_mut_in_list_fwd T n0 key ls0; Return t)
    | ListNil => Fail_ Failure
    end
  end
  .

(** [hashmap::HashMap::{0}::get_mut_in_list] *)
Fixpoint hash_map_get_mut_in_list_back
  (T : Type) (n : nat) (key : usize) (ls : List_t T) (ret : T) :
  result (List_t T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    match ls with
    | ListCons ckey cvalue ls0 =>
      if ckey s= key
      then Return (ListCons ckey ret ls0)
      else (
        ls1 <- hash_map_get_mut_in_list_back T n0 key ls0 ret;
        Return (ListCons ckey cvalue ls1))
    | ListNil => Fail_ Failure
    end
  end
  .

(** [hashmap::HashMap::{0}::get_mut] *)
Definition hash_map_get_mut_fwd
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) : result T :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    hash <- hash_key_fwd key;
    match self with
    | mkHash_map_t i p i0 v =>
      let i1 := vec_len (List_t T) v in
      hash_mod <- usize_rem hash i1;
      l <- vec_index_mut_fwd (List_t T) v hash_mod;
      t <- hash_map_get_mut_in_list_fwd T n0 key l;
      Return t
    end
  end
  .

(** [hashmap::HashMap::{0}::get_mut] *)
Definition hash_map_get_mut_back
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) (ret : T) :
  result (Hash_map_t T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    hash <- hash_key_fwd key;
    match self with
    | mkHash_map_t i p i0 v =>
      let i1 := vec_len (List_t T) v in
      hash_mod <- usize_rem hash i1;
      l <- vec_index_mut_fwd (List_t T) v hash_mod;
      l0 <- hash_map_get_mut_in_list_back T n0 key l ret;
      v0 <- vec_index_mut_back (List_t T) v hash_mod l0;
      Return (mkHash_map_t i p i0 v0)
    end
  end
  .

(** [hashmap::HashMap::{0}::remove_from_list] *)
Fixpoint hash_map_remove_from_list_fwd
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
      else (opt <- hash_map_remove_from_list_fwd T n0 key tl; Return opt)
    | ListNil => Return None
    end
  end
  .

(** [hashmap::HashMap::{0}::remove_from_list] *)
Fixpoint hash_map_remove_from_list_back
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
        tl0 <- hash_map_remove_from_list_back T n0 key tl;
        Return (ListCons ckey t tl0))
    | ListNil => Return ListNil
    end
  end
  .

(** [hashmap::HashMap::{0}::remove] *)
Definition hash_map_remove_fwd
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) :
  result (option T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    hash <- hash_key_fwd key;
    match self with
    | mkHash_map_t i p i0 v =>
      let i1 := vec_len (List_t T) v in
      hash_mod <- usize_rem hash i1;
      l <- vec_index_mut_fwd (List_t T) v hash_mod;
      x <- hash_map_remove_from_list_fwd T n0 key l;
      match x with
      | None => Return None
      | Some x0 => i2 <- usize_sub i 1 %usize; let _ := i2 in Return (Some x0)
      end
    end
  end
  .

(** [hashmap::HashMap::{0}::remove] *)
Definition hash_map_remove_back
  (T : Type) (n : nat) (self : Hash_map_t T) (key : usize) :
  result (Hash_map_t T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    hash <- hash_key_fwd key;
    match self with
    | mkHash_map_t i p i0 v =>
      let i1 := vec_len (List_t T) v in
      hash_mod <- usize_rem hash i1;
      l <- vec_index_mut_fwd (List_t T) v hash_mod;
      x <- hash_map_remove_from_list_fwd T n0 key l;
      match x with
      | None =>
        l0 <- hash_map_remove_from_list_back T n0 key l;
        v0 <- vec_index_mut_back (List_t T) v hash_mod l0;
        Return (mkHash_map_t i p i0 v0)
      | Some x0 =>
        i2 <- usize_sub i 1 %usize;
        l0 <- hash_map_remove_from_list_back T n0 key l;
        v0 <- vec_index_mut_back (List_t T) v hash_mod l0;
        Return (mkHash_map_t i2 p i0 v0)
      end
    end
  end
  .

(** [hashmap::test1] *)
Definition test1_fwd (n : nat) : result unit :=
  match n with
  | O => Fail_ OutOfFuel
  | S n0 =>
    hm <- hash_map_new_fwd u64 n0;
    hm0 <- hash_map_insert_fwd_back u64 n0 hm (0 %usize) (42 %u64);
    hm1 <- hash_map_insert_fwd_back u64 n0 hm0 (128 %usize) (18 %u64);
    hm2 <- hash_map_insert_fwd_back u64 n0 hm1 (1024 %usize) (138 %u64);
    hm3 <- hash_map_insert_fwd_back u64 n0 hm2 (1056 %usize) (256 %u64);
    i <- hash_map_get_fwd u64 n0 hm3 (128 %usize);
    if negb (i s= 18 %u64)
    then Fail_ Failure
    else (
      hm4 <- hash_map_get_mut_back u64 n0 hm3 (1024 %usize) (56 %u64);
      i0 <- hash_map_get_fwd u64 n0 hm4 (1024 %usize);
      if negb (i0 s= 56 %u64)
      then Fail_ Failure
      else (
        x <- hash_map_remove_fwd u64 n0 hm4 (1024 %usize);
        match x with
        | None => Fail_ Failure
        | Some x0 =>
          if negb (x0 s= 56 %u64)
          then Fail_ Failure
          else (
            hm5 <- hash_map_remove_back u64 n0 hm4 (1024 %usize);
            i1 <- hash_map_get_fwd u64 n0 hm5 (0 %usize);
            if negb (i1 s= 42 %u64)
            then Fail_ Failure
            else (
              i2 <- hash_map_get_fwd u64 n0 hm5 (128 %usize);
              if negb (i2 s= 18 %u64)
              then Fail_ Failure
              else (
                i3 <- hash_map_get_fwd u64 n0 hm5 (1056 %usize);
                if negb (i3 s= 256 %u64) then Fail_ Failure else Return tt)))
        end))
  end
  .

End Hashmap__Funs .