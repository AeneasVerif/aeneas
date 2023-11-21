-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [hashmap_main]: function definitions
import Base
import HashmapMain.Types
import HashmapMain.FunsExternal
open Primitives

namespace hashmap_main

/- [hashmap_main::hashmap::hash_key]: forward function -/
def hashmap.hash_key (k : Usize) : Result Usize :=
  Result.ret k

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::allocate_slots]: loop 0: forward function -/
divergent def hashmap.HashMap.allocate_slots_loop
  (T : Type) (slots : alloc.vec.Vec (hashmap.List T)) (n : Usize) :
  Result (alloc.vec.Vec (hashmap.List T))
  :=
  if n > 0#usize
  then
    do
      let slots0 ← alloc.vec.Vec.push (hashmap.List T) slots hashmap.List.Nil
      let n0 ← n - 1#usize
      hashmap.HashMap.allocate_slots_loop T slots0 n0
  else Result.ret slots

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::allocate_slots]: forward function -/
def hashmap.HashMap.allocate_slots
  (T : Type) (slots : alloc.vec.Vec (hashmap.List T)) (n : Usize) :
  Result (alloc.vec.Vec (hashmap.List T))
  :=
  hashmap.HashMap.allocate_slots_loop T slots n

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::new_with_capacity]: forward function -/
def hashmap.HashMap.new_with_capacity
  (T : Type) (capacity : Usize) (max_load_dividend : Usize)
  (max_load_divisor : Usize) :
  Result (hashmap.HashMap T)
  :=
  do
    let v := alloc.vec.Vec.new (hashmap.List T)
    let slots ← hashmap.HashMap.allocate_slots T v capacity
    let i ← capacity * max_load_dividend
    let i0 ← i / max_load_divisor
    Result.ret
      {
        num_entries := 0#usize,
        max_load_factor := (max_load_dividend, max_load_divisor),
        max_load := i0,
        slots := slots
      }

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::new]: forward function -/
def hashmap.HashMap.new (T : Type) : Result (hashmap.HashMap T) :=
  hashmap.HashMap.new_with_capacity T 32#usize 4#usize 5#usize

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::clear]: loop 0: merged forward/backward function
   (there is a single backward function, and the forward function returns ()) -/
divergent def hashmap.HashMap.clear_loop
  (T : Type) (slots : alloc.vec.Vec (hashmap.List T)) (i : Usize) :
  Result (alloc.vec.Vec (hashmap.List T))
  :=
  let i0 := alloc.vec.Vec.len (hashmap.List T) slots
  if i < i0
  then
    do
      let i1 ← i + 1#usize
      let slots0 ←
        alloc.vec.Vec.index_mut_back (hashmap.List T) Usize
          (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T)) slots i
          hashmap.List.Nil
      hashmap.HashMap.clear_loop T slots0 i1
  else Result.ret slots

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::clear]: merged forward/backward function
   (there is a single backward function, and the forward function returns ()) -/
def hashmap.HashMap.clear
  (T : Type) (self : hashmap.HashMap T) : Result (hashmap.HashMap T) :=
  do
    let v ← hashmap.HashMap.clear_loop T self.slots 0#usize
    Result.ret { self with num_entries := 0#usize, slots := v }

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::len]: forward function -/
def hashmap.HashMap.len (T : Type) (self : hashmap.HashMap T) : Result Usize :=
  Result.ret self.num_entries

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::insert_in_list]: loop 0: forward function -/
divergent def hashmap.HashMap.insert_in_list_loop
  (T : Type) (key : Usize) (value : T) (ls : hashmap.List T) : Result Bool :=
  match ls with
  | hashmap.List.Cons ckey cvalue tl =>
    if ckey = key
    then Result.ret false
    else hashmap.HashMap.insert_in_list_loop T key value tl
  | hashmap.List.Nil => Result.ret true

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::insert_in_list]: forward function -/
def hashmap.HashMap.insert_in_list
  (T : Type) (key : Usize) (value : T) (ls : hashmap.List T) : Result Bool :=
  hashmap.HashMap.insert_in_list_loop T key value ls

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::insert_in_list]: loop 0: backward function 0 -/
divergent def hashmap.HashMap.insert_in_list_loop_back
  (T : Type) (key : Usize) (value : T) (ls : hashmap.List T) :
  Result (hashmap.List T)
  :=
  match ls with
  | hashmap.List.Cons ckey cvalue tl =>
    if ckey = key
    then Result.ret (hashmap.List.Cons ckey value tl)
    else
      do
        let tl0 ← hashmap.HashMap.insert_in_list_loop_back T key value tl
        Result.ret (hashmap.List.Cons ckey cvalue tl0)
  | hashmap.List.Nil =>
    let l := hashmap.List.Nil
    Result.ret (hashmap.List.Cons key value l)

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::insert_in_list]: backward function 0 -/
def hashmap.HashMap.insert_in_list_back
  (T : Type) (key : Usize) (value : T) (ls : hashmap.List T) :
  Result (hashmap.List T)
  :=
  hashmap.HashMap.insert_in_list_loop_back T key value ls

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::insert_no_resize]: merged forward/backward function
   (there is a single backward function, and the forward function returns ()) -/
def hashmap.HashMap.insert_no_resize
  (T : Type) (self : hashmap.HashMap T) (key : Usize) (value : T) :
  Result (hashmap.HashMap T)
  :=
  do
    let hash ← hashmap.hash_key key
    let i := alloc.vec.Vec.len (hashmap.List T) self.slots
    let hash_mod ← hash % i
    let l ←
      alloc.vec.Vec.index_mut (hashmap.List T) Usize
        (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T))
        self.slots hash_mod
    let inserted ← hashmap.HashMap.insert_in_list T key value l
    if inserted
    then
      do
        let i0 ← self.num_entries + 1#usize
        let l0 ← hashmap.HashMap.insert_in_list_back T key value l
        let v ←
          alloc.vec.Vec.index_mut_back (hashmap.List T) Usize
            (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T))
            self.slots hash_mod l0
        Result.ret { self with num_entries := i0, slots := v }
    else
      do
        let l0 ← hashmap.HashMap.insert_in_list_back T key value l
        let v ←
          alloc.vec.Vec.index_mut_back (hashmap.List T) Usize
            (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T))
            self.slots hash_mod l0
        Result.ret { self with slots := v }

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::move_elements_from_list]: loop 0: merged forward/backward function
   (there is a single backward function, and the forward function returns ()) -/
divergent def hashmap.HashMap.move_elements_from_list_loop
  (T : Type) (ntable : hashmap.HashMap T) (ls : hashmap.List T) :
  Result (hashmap.HashMap T)
  :=
  match ls with
  | hashmap.List.Cons k v tl =>
    do
      let ntable0 ← hashmap.HashMap.insert_no_resize T ntable k v
      hashmap.HashMap.move_elements_from_list_loop T ntable0 tl
  | hashmap.List.Nil => Result.ret ntable

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::move_elements_from_list]: merged forward/backward function
   (there is a single backward function, and the forward function returns ()) -/
def hashmap.HashMap.move_elements_from_list
  (T : Type) (ntable : hashmap.HashMap T) (ls : hashmap.List T) :
  Result (hashmap.HashMap T)
  :=
  hashmap.HashMap.move_elements_from_list_loop T ntable ls

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::move_elements]: loop 0: merged forward/backward function
   (there is a single backward function, and the forward function returns ()) -/
divergent def hashmap.HashMap.move_elements_loop
  (T : Type) (ntable : hashmap.HashMap T)
  (slots : alloc.vec.Vec (hashmap.List T)) (i : Usize) :
  Result ((hashmap.HashMap T) × (alloc.vec.Vec (hashmap.List T)))
  :=
  let i0 := alloc.vec.Vec.len (hashmap.List T) slots
  if i < i0
  then
    do
      let l ←
        alloc.vec.Vec.index_mut (hashmap.List T) Usize
          (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T)) slots i
      let ls := core.mem.replace (hashmap.List T) l hashmap.List.Nil
      let ntable0 ← hashmap.HashMap.move_elements_from_list T ntable ls
      let i1 ← i + 1#usize
      let l0 := core.mem.replace_back (hashmap.List T) l hashmap.List.Nil
      let slots0 ←
        alloc.vec.Vec.index_mut_back (hashmap.List T) Usize
          (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T)) slots i
          l0
      hashmap.HashMap.move_elements_loop T ntable0 slots0 i1
  else Result.ret (ntable, slots)

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::move_elements]: merged forward/backward function
   (there is a single backward function, and the forward function returns ()) -/
def hashmap.HashMap.move_elements
  (T : Type) (ntable : hashmap.HashMap T)
  (slots : alloc.vec.Vec (hashmap.List T)) (i : Usize) :
  Result ((hashmap.HashMap T) × (alloc.vec.Vec (hashmap.List T)))
  :=
  hashmap.HashMap.move_elements_loop T ntable slots i

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::try_resize]: merged forward/backward function
   (there is a single backward function, and the forward function returns ()) -/
def hashmap.HashMap.try_resize
  (T : Type) (self : hashmap.HashMap T) : Result (hashmap.HashMap T) :=
  do
    let max_usize ← Scalar.cast .Usize core_u32_max
    let capacity := alloc.vec.Vec.len (hashmap.List T) self.slots
    let n1 ← max_usize / 2#usize
    let (i, i0) := self.max_load_factor
    let i1 ← n1 / i
    if capacity <= i1
    then
      do
        let i2 ← capacity * 2#usize
        let ntable ← hashmap.HashMap.new_with_capacity T i2 i i0
        let (ntable0, _) ←
          hashmap.HashMap.move_elements T ntable self.slots 0#usize
        Result.ret
          {
            ntable0
              with
              num_entries := self.num_entries, max_load_factor := (i, i0)
          }
    else Result.ret { self with max_load_factor := (i, i0) }

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::insert]: merged forward/backward function
   (there is a single backward function, and the forward function returns ()) -/
def hashmap.HashMap.insert
  (T : Type) (self : hashmap.HashMap T) (key : Usize) (value : T) :
  Result (hashmap.HashMap T)
  :=
  do
    let self0 ← hashmap.HashMap.insert_no_resize T self key value
    let i ← hashmap.HashMap.len T self0
    if i > self0.max_load
    then hashmap.HashMap.try_resize T self0
    else Result.ret self0

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::contains_key_in_list]: loop 0: forward function -/
divergent def hashmap.HashMap.contains_key_in_list_loop
  (T : Type) (key : Usize) (ls : hashmap.List T) : Result Bool :=
  match ls with
  | hashmap.List.Cons ckey t tl =>
    if ckey = key
    then Result.ret true
    else hashmap.HashMap.contains_key_in_list_loop T key tl
  | hashmap.List.Nil => Result.ret false

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::contains_key_in_list]: forward function -/
def hashmap.HashMap.contains_key_in_list
  (T : Type) (key : Usize) (ls : hashmap.List T) : Result Bool :=
  hashmap.HashMap.contains_key_in_list_loop T key ls

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::contains_key]: forward function -/
def hashmap.HashMap.contains_key
  (T : Type) (self : hashmap.HashMap T) (key : Usize) : Result Bool :=
  do
    let hash ← hashmap.hash_key key
    let i := alloc.vec.Vec.len (hashmap.List T) self.slots
    let hash_mod ← hash % i
    let l ←
      alloc.vec.Vec.index (hashmap.List T) Usize
        (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T))
        self.slots hash_mod
    hashmap.HashMap.contains_key_in_list T key l

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_in_list]: loop 0: forward function -/
divergent def hashmap.HashMap.get_in_list_loop
  (T : Type) (key : Usize) (ls : hashmap.List T) : Result T :=
  match ls with
  | hashmap.List.Cons ckey cvalue tl =>
    if ckey = key
    then Result.ret cvalue
    else hashmap.HashMap.get_in_list_loop T key tl
  | hashmap.List.Nil => Result.fail Error.panic

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_in_list]: forward function -/
def hashmap.HashMap.get_in_list
  (T : Type) (key : Usize) (ls : hashmap.List T) : Result T :=
  hashmap.HashMap.get_in_list_loop T key ls

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get]: forward function -/
def hashmap.HashMap.get
  (T : Type) (self : hashmap.HashMap T) (key : Usize) : Result T :=
  do
    let hash ← hashmap.hash_key key
    let i := alloc.vec.Vec.len (hashmap.List T) self.slots
    let hash_mod ← hash % i
    let l ←
      alloc.vec.Vec.index (hashmap.List T) Usize
        (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T))
        self.slots hash_mod
    hashmap.HashMap.get_in_list T key l

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_mut_in_list]: loop 0: forward function -/
divergent def hashmap.HashMap.get_mut_in_list_loop
  (T : Type) (ls : hashmap.List T) (key : Usize) : Result T :=
  match ls with
  | hashmap.List.Cons ckey cvalue tl =>
    if ckey = key
    then Result.ret cvalue
    else hashmap.HashMap.get_mut_in_list_loop T tl key
  | hashmap.List.Nil => Result.fail Error.panic

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_mut_in_list]: forward function -/
def hashmap.HashMap.get_mut_in_list
  (T : Type) (ls : hashmap.List T) (key : Usize) : Result T :=
  hashmap.HashMap.get_mut_in_list_loop T ls key

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_mut_in_list]: loop 0: backward function 0 -/
divergent def hashmap.HashMap.get_mut_in_list_loop_back
  (T : Type) (ls : hashmap.List T) (key : Usize) (ret0 : T) :
  Result (hashmap.List T)
  :=
  match ls with
  | hashmap.List.Cons ckey cvalue tl =>
    if ckey = key
    then Result.ret (hashmap.List.Cons ckey ret0 tl)
    else
      do
        let tl0 ← hashmap.HashMap.get_mut_in_list_loop_back T tl key ret0
        Result.ret (hashmap.List.Cons ckey cvalue tl0)
  | hashmap.List.Nil => Result.fail Error.panic

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_mut_in_list]: backward function 0 -/
def hashmap.HashMap.get_mut_in_list_back
  (T : Type) (ls : hashmap.List T) (key : Usize) (ret0 : T) :
  Result (hashmap.List T)
  :=
  hashmap.HashMap.get_mut_in_list_loop_back T ls key ret0

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_mut]: forward function -/
def hashmap.HashMap.get_mut
  (T : Type) (self : hashmap.HashMap T) (key : Usize) : Result T :=
  do
    let hash ← hashmap.hash_key key
    let i := alloc.vec.Vec.len (hashmap.List T) self.slots
    let hash_mod ← hash % i
    let l ←
      alloc.vec.Vec.index_mut (hashmap.List T) Usize
        (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T))
        self.slots hash_mod
    hashmap.HashMap.get_mut_in_list T l key

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_mut]: backward function 0 -/
def hashmap.HashMap.get_mut_back
  (T : Type) (self : hashmap.HashMap T) (key : Usize) (ret0 : T) :
  Result (hashmap.HashMap T)
  :=
  do
    let hash ← hashmap.hash_key key
    let i := alloc.vec.Vec.len (hashmap.List T) self.slots
    let hash_mod ← hash % i
    let l ←
      alloc.vec.Vec.index_mut (hashmap.List T) Usize
        (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T))
        self.slots hash_mod
    let l0 ← hashmap.HashMap.get_mut_in_list_back T l key ret0
    let v ←
      alloc.vec.Vec.index_mut_back (hashmap.List T) Usize
        (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T))
        self.slots hash_mod l0
    Result.ret { self with slots := v }

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::remove_from_list]: loop 0: forward function -/
divergent def hashmap.HashMap.remove_from_list_loop
  (T : Type) (key : Usize) (ls : hashmap.List T) : Result (Option T) :=
  match ls with
  | hashmap.List.Cons ckey t tl =>
    if ckey = key
    then
      let mv_ls :=
        core.mem.replace (hashmap.List T) (hashmap.List.Cons ckey t tl)
          hashmap.List.Nil
      match mv_ls with
      | hashmap.List.Cons i cvalue tl0 => Result.ret (some cvalue)
      | hashmap.List.Nil => Result.fail Error.panic
    else hashmap.HashMap.remove_from_list_loop T key tl
  | hashmap.List.Nil => Result.ret none

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::remove_from_list]: forward function -/
def hashmap.HashMap.remove_from_list
  (T : Type) (key : Usize) (ls : hashmap.List T) : Result (Option T) :=
  hashmap.HashMap.remove_from_list_loop T key ls

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::remove_from_list]: loop 0: backward function 1 -/
divergent def hashmap.HashMap.remove_from_list_loop_back
  (T : Type) (key : Usize) (ls : hashmap.List T) : Result (hashmap.List T) :=
  match ls with
  | hashmap.List.Cons ckey t tl =>
    if ckey = key
    then
      let mv_ls :=
        core.mem.replace (hashmap.List T) (hashmap.List.Cons ckey t tl)
          hashmap.List.Nil
      match mv_ls with
      | hashmap.List.Cons i cvalue tl0 => Result.ret tl0
      | hashmap.List.Nil => Result.fail Error.panic
    else
      do
        let tl0 ← hashmap.HashMap.remove_from_list_loop_back T key tl
        Result.ret (hashmap.List.Cons ckey t tl0)
  | hashmap.List.Nil => Result.ret hashmap.List.Nil

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::remove_from_list]: backward function 1 -/
def hashmap.HashMap.remove_from_list_back
  (T : Type) (key : Usize) (ls : hashmap.List T) : Result (hashmap.List T) :=
  hashmap.HashMap.remove_from_list_loop_back T key ls

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::remove]: forward function -/
def hashmap.HashMap.remove
  (T : Type) (self : hashmap.HashMap T) (key : Usize) : Result (Option T) :=
  do
    let hash ← hashmap.hash_key key
    let i := alloc.vec.Vec.len (hashmap.List T) self.slots
    let hash_mod ← hash % i
    let l ←
      alloc.vec.Vec.index_mut (hashmap.List T) Usize
        (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T))
        self.slots hash_mod
    let x ← hashmap.HashMap.remove_from_list T key l
    match x with
    | none => Result.ret none
    | some x0 => do
                   let _ ← self.num_entries - 1#usize
                   Result.ret (some x0)

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::remove]: backward function 0 -/
def hashmap.HashMap.remove_back
  (T : Type) (self : hashmap.HashMap T) (key : Usize) :
  Result (hashmap.HashMap T)
  :=
  do
    let hash ← hashmap.hash_key key
    let i := alloc.vec.Vec.len (hashmap.List T) self.slots
    let hash_mod ← hash % i
    let l ←
      alloc.vec.Vec.index_mut (hashmap.List T) Usize
        (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T))
        self.slots hash_mod
    let x ← hashmap.HashMap.remove_from_list T key l
    match x with
    | none =>
      do
        let l0 ← hashmap.HashMap.remove_from_list_back T key l
        let v ←
          alloc.vec.Vec.index_mut_back (hashmap.List T) Usize
            (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T))
            self.slots hash_mod l0
        Result.ret { self with slots := v }
    | some x0 =>
      do
        let i0 ← self.num_entries - 1#usize
        let l0 ← hashmap.HashMap.remove_from_list_back T key l
        let v ←
          alloc.vec.Vec.index_mut_back (hashmap.List T) Usize
            (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T))
            self.slots hash_mod l0
        Result.ret { self with num_entries := i0, slots := v }

/- [hashmap_main::hashmap::test1]: forward function -/
def hashmap.test1 : Result Unit :=
  do
    let hm ← hashmap.HashMap.new U64
    let hm0 ← hashmap.HashMap.insert U64 hm 0#usize 42#u64
    let hm1 ← hashmap.HashMap.insert U64 hm0 128#usize 18#u64
    let hm2 ← hashmap.HashMap.insert U64 hm1 1024#usize 138#u64
    let hm3 ← hashmap.HashMap.insert U64 hm2 1056#usize 256#u64
    let i ← hashmap.HashMap.get U64 hm3 128#usize
    if not (i = 18#u64)
    then Result.fail Error.panic
    else
      do
        let hm4 ← hashmap.HashMap.get_mut_back U64 hm3 1024#usize 56#u64
        let i0 ← hashmap.HashMap.get U64 hm4 1024#usize
        if not (i0 = 56#u64)
        then Result.fail Error.panic
        else
          do
            let x ← hashmap.HashMap.remove U64 hm4 1024#usize
            match x with
            | none => Result.fail Error.panic
            | some x0 =>
              if not (x0 = 56#u64)
              then Result.fail Error.panic
              else
                do
                  let hm5 ← hashmap.HashMap.remove_back U64 hm4 1024#usize
                  let i1 ← hashmap.HashMap.get U64 hm5 0#usize
                  if not (i1 = 42#u64)
                  then Result.fail Error.panic
                  else
                    do
                      let i2 ← hashmap.HashMap.get U64 hm5 128#usize
                      if not (i2 = 18#u64)
                      then Result.fail Error.panic
                      else
                        do
                          let i3 ← hashmap.HashMap.get U64 hm5 1056#usize
                          if not (i3 = 256#u64)
                          then Result.fail Error.panic
                          else Result.ret ()

/- [hashmap_main::insert_on_disk]: forward function -/
def insert_on_disk
  (key : Usize) (value : U64) (st : State) : Result (State × Unit) :=
  do
    let (st0, hm) ← hashmap_utils.deserialize st
    let hm0 ← hashmap.HashMap.insert U64 hm key value
    let (st1, _) ← hashmap_utils.serialize hm0 st0
    Result.ret (st1, ())

/- [hashmap_main::main]: forward function -/
def main : Result Unit :=
  Result.ret ()

end hashmap_main
