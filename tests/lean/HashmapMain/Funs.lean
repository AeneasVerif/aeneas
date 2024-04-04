-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [hashmap_main]: function definitions
import Base
import HashmapMain.Types
import HashmapMain.FunsExternal
open Primitives

namespace hashmap_main

/- [hashmap_main::hashmap::hash_key]:
   Source: 'src/hashmap.rs', lines 27:0-27:32 -/
def hashmap.hash_key (k : Usize) : Result Usize :=
  Result.ret k

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::allocate_slots]: loop 0:
   Source: 'src/hashmap.rs', lines 50:4-56:5 -/
divergent def hashmap.HashMap.allocate_slots_loop
  (T : Type) (slots : alloc.vec.Vec (hashmap.List T)) (n : Usize) :
  Result (alloc.vec.Vec (hashmap.List T))
  :=
  if n > 0#usize
  then
    do
    let slots1 ← alloc.vec.Vec.push (hashmap.List T) slots hashmap.List.Nil
    let n1 ← n - 1#usize
    hashmap.HashMap.allocate_slots_loop T slots1 n1
  else Result.ret slots

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::allocate_slots]:
   Source: 'src/hashmap.rs', lines 50:4-50:76 -/
def hashmap.HashMap.allocate_slots
  (T : Type) (slots : alloc.vec.Vec (hashmap.List T)) (n : Usize) :
  Result (alloc.vec.Vec (hashmap.List T))
  :=
  hashmap.HashMap.allocate_slots_loop T slots n

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::new_with_capacity]:
   Source: 'src/hashmap.rs', lines 59:4-63:13 -/
def hashmap.HashMap.new_with_capacity
  (T : Type) (capacity : Usize) (max_load_dividend : Usize)
  (max_load_divisor : Usize) :
  Result (hashmap.HashMap T)
  :=
  do
  let slots ←
    hashmap.HashMap.allocate_slots T (alloc.vec.Vec.new (hashmap.List T))
      capacity
  let i ← capacity * max_load_dividend
  let i1 ← i / max_load_divisor
  Result.ret
    {
      num_entries := 0#usize,
      max_load_factor := (max_load_dividend, max_load_divisor),
      max_load := i1,
      slots := slots
    }

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::new]:
   Source: 'src/hashmap.rs', lines 75:4-75:24 -/
def hashmap.HashMap.new (T : Type) : Result (hashmap.HashMap T) :=
  hashmap.HashMap.new_with_capacity T 32#usize 4#usize 5#usize

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::clear]: loop 0:
   Source: 'src/hashmap.rs', lines 80:4-88:5 -/
divergent def hashmap.HashMap.clear_loop
  (T : Type) (slots : alloc.vec.Vec (hashmap.List T)) (i : Usize) :
  Result (alloc.vec.Vec (hashmap.List T))
  :=
  let i1 := alloc.vec.Vec.len (hashmap.List T) slots
  if i < i1
  then
    do
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (hashmap.List T) Usize
        (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T)) slots i
    let i2 ← i + 1#usize
    let slots1 ← index_mut_back hashmap.List.Nil
    hashmap.HashMap.clear_loop T slots1 i2
  else Result.ret slots

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::clear]:
   Source: 'src/hashmap.rs', lines 80:4-80:27 -/
def hashmap.HashMap.clear
  (T : Type) (self : hashmap.HashMap T) : Result (hashmap.HashMap T) :=
  do
  let back ← hashmap.HashMap.clear_loop T self.slots 0#usize
  Result.ret { self with num_entries := 0#usize, slots := back }

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::len]:
   Source: 'src/hashmap.rs', lines 90:4-90:30 -/
def hashmap.HashMap.len (T : Type) (self : hashmap.HashMap T) : Result Usize :=
  Result.ret self.num_entries

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::insert_in_list]: loop 0:
   Source: 'src/hashmap.rs', lines 97:4-114:5 -/
divergent def hashmap.HashMap.insert_in_list_loop
  (T : Type) (key : Usize) (value : T) (ls : hashmap.List T) :
  Result (Bool × (hashmap.List T))
  :=
  match ls with
  | hashmap.List.Cons ckey cvalue tl =>
    if ckey = key
    then Result.ret (false, hashmap.List.Cons ckey value tl)
    else
      do
      let (b, back) ← hashmap.HashMap.insert_in_list_loop T key value tl
      Result.ret (b, hashmap.List.Cons ckey cvalue back)
  | hashmap.List.Nil =>
    Result.ret (true, hashmap.List.Cons key value hashmap.List.Nil)

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::insert_in_list]:
   Source: 'src/hashmap.rs', lines 97:4-97:71 -/
def hashmap.HashMap.insert_in_list
  (T : Type) (key : Usize) (value : T) (ls : hashmap.List T) :
  Result (Bool × (hashmap.List T))
  :=
  hashmap.HashMap.insert_in_list_loop T key value ls

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::insert_no_resize]:
   Source: 'src/hashmap.rs', lines 117:4-117:54 -/
def hashmap.HashMap.insert_no_resize
  (T : Type) (self : hashmap.HashMap T) (key : Usize) (value : T) :
  Result (hashmap.HashMap T)
  :=
  do
  let hash ← hashmap.hash_key key
  let i := alloc.vec.Vec.len (hashmap.List T) self.slots
  let hash_mod ← hash % i
  let (l, index_mut_back) ←
    alloc.vec.Vec.index_mut (hashmap.List T) Usize
      (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T)) self.slots
      hash_mod
  let (inserted, l1) ← hashmap.HashMap.insert_in_list T key value l
  if inserted
  then
    do
    let i1 ← self.num_entries + 1#usize
    let v ← index_mut_back l1
    Result.ret { self with num_entries := i1, slots := v }
  else do
       let v ← index_mut_back l1
       Result.ret { self with slots := v }

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::move_elements_from_list]: loop 0:
   Source: 'src/hashmap.rs', lines 183:4-196:5 -/
divergent def hashmap.HashMap.move_elements_from_list_loop
  (T : Type) (ntable : hashmap.HashMap T) (ls : hashmap.List T) :
  Result (hashmap.HashMap T)
  :=
  match ls with
  | hashmap.List.Cons k v tl =>
    do
    let ntable1 ← hashmap.HashMap.insert_no_resize T ntable k v
    hashmap.HashMap.move_elements_from_list_loop T ntable1 tl
  | hashmap.List.Nil => Result.ret ntable

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::move_elements_from_list]:
   Source: 'src/hashmap.rs', lines 183:4-183:72 -/
def hashmap.HashMap.move_elements_from_list
  (T : Type) (ntable : hashmap.HashMap T) (ls : hashmap.List T) :
  Result (hashmap.HashMap T)
  :=
  hashmap.HashMap.move_elements_from_list_loop T ntable ls

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::move_elements]: loop 0:
   Source: 'src/hashmap.rs', lines 171:4-180:5 -/
divergent def hashmap.HashMap.move_elements_loop
  (T : Type) (ntable : hashmap.HashMap T)
  (slots : alloc.vec.Vec (hashmap.List T)) (i : Usize) :
  Result ((hashmap.HashMap T) × (alloc.vec.Vec (hashmap.List T)))
  :=
  let i1 := alloc.vec.Vec.len (hashmap.List T) slots
  if i < i1
  then
    do
    let (l, index_mut_back) ←
      alloc.vec.Vec.index_mut (hashmap.List T) Usize
        (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T)) slots i
    let (ls, l1) := core.mem.replace (hashmap.List T) l hashmap.List.Nil
    let ntable1 ← hashmap.HashMap.move_elements_from_list T ntable ls
    let i2 ← i + 1#usize
    let slots1 ← index_mut_back l1
    hashmap.HashMap.move_elements_loop T ntable1 slots1 i2
  else Result.ret (ntable, slots)

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::move_elements]:
   Source: 'src/hashmap.rs', lines 171:4-171:95 -/
def hashmap.HashMap.move_elements
  (T : Type) (ntable : hashmap.HashMap T)
  (slots : alloc.vec.Vec (hashmap.List T)) (i : Usize) :
  Result ((hashmap.HashMap T) × (alloc.vec.Vec (hashmap.List T)))
  :=
  hashmap.HashMap.move_elements_loop T ntable slots i

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::try_resize]:
   Source: 'src/hashmap.rs', lines 140:4-140:28 -/
def hashmap.HashMap.try_resize
  (T : Type) (self : hashmap.HashMap T) : Result (hashmap.HashMap T) :=
  do
  let max_usize ← Scalar.cast .Usize core_u32_max
  let capacity := alloc.vec.Vec.len (hashmap.List T) self.slots
  let n1 ← max_usize / 2#usize
  let (i, i1) := self.max_load_factor
  let i2 ← n1 / i
  if capacity <= i2
  then
    do
    let i3 ← capacity * 2#usize
    let ntable ← hashmap.HashMap.new_with_capacity T i3 i i1
    let p ← hashmap.HashMap.move_elements T ntable self.slots 0#usize
    let (ntable1, _) := p
    Result.ret
      {
        ntable1
          with
          num_entries := self.num_entries, max_load_factor := (i, i1)
      }
  else Result.ret { self with max_load_factor := (i, i1) }

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::insert]:
   Source: 'src/hashmap.rs', lines 129:4-129:48 -/
def hashmap.HashMap.insert
  (T : Type) (self : hashmap.HashMap T) (key : Usize) (value : T) :
  Result (hashmap.HashMap T)
  :=
  do
  let self1 ← hashmap.HashMap.insert_no_resize T self key value
  let i ← hashmap.HashMap.len T self1
  if i > self1.max_load
  then hashmap.HashMap.try_resize T self1
  else Result.ret self1

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::contains_key_in_list]: loop 0:
   Source: 'src/hashmap.rs', lines 206:4-219:5 -/
divergent def hashmap.HashMap.contains_key_in_list_loop
  (T : Type) (key : Usize) (ls : hashmap.List T) : Result Bool :=
  match ls with
  | hashmap.List.Cons ckey _ tl =>
    if ckey = key
    then Result.ret true
    else hashmap.HashMap.contains_key_in_list_loop T key tl
  | hashmap.List.Nil => Result.ret false

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::contains_key_in_list]:
   Source: 'src/hashmap.rs', lines 206:4-206:68 -/
def hashmap.HashMap.contains_key_in_list
  (T : Type) (key : Usize) (ls : hashmap.List T) : Result Bool :=
  hashmap.HashMap.contains_key_in_list_loop T key ls

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::contains_key]:
   Source: 'src/hashmap.rs', lines 199:4-199:49 -/
def hashmap.HashMap.contains_key
  (T : Type) (self : hashmap.HashMap T) (key : Usize) : Result Bool :=
  do
  let hash ← hashmap.hash_key key
  let i := alloc.vec.Vec.len (hashmap.List T) self.slots
  let hash_mod ← hash % i
  let l ←
    alloc.vec.Vec.index (hashmap.List T) Usize
      (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T)) self.slots
      hash_mod
  hashmap.HashMap.contains_key_in_list T key l

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_in_list]: loop 0:
   Source: 'src/hashmap.rs', lines 224:4-237:5 -/
divergent def hashmap.HashMap.get_in_list_loop
  (T : Type) (key : Usize) (ls : hashmap.List T) : Result T :=
  match ls with
  | hashmap.List.Cons ckey cvalue tl =>
    if ckey = key
    then Result.ret cvalue
    else hashmap.HashMap.get_in_list_loop T key tl
  | hashmap.List.Nil => Result.fail .panic

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_in_list]:
   Source: 'src/hashmap.rs', lines 224:4-224:70 -/
def hashmap.HashMap.get_in_list
  (T : Type) (key : Usize) (ls : hashmap.List T) : Result T :=
  hashmap.HashMap.get_in_list_loop T key ls

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get]:
   Source: 'src/hashmap.rs', lines 239:4-239:55 -/
def hashmap.HashMap.get
  (T : Type) (self : hashmap.HashMap T) (key : Usize) : Result T :=
  do
  let hash ← hashmap.hash_key key
  let i := alloc.vec.Vec.len (hashmap.List T) self.slots
  let hash_mod ← hash % i
  let l ←
    alloc.vec.Vec.index (hashmap.List T) Usize
      (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T)) self.slots
      hash_mod
  hashmap.HashMap.get_in_list T key l

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_mut_in_list]: loop 0:
   Source: 'src/hashmap.rs', lines 245:4-254:5 -/
divergent def hashmap.HashMap.get_mut_in_list_loop
  (T : Type) (ls : hashmap.List T) (key : Usize) :
  Result (T × (T → Result (hashmap.List T)))
  :=
  match ls with
  | hashmap.List.Cons ckey cvalue tl =>
    if ckey = key
    then
      let back := fun ret => Result.ret (hashmap.List.Cons ckey ret tl)
      Result.ret (cvalue, back)
    else
      do
      let (t, back) ← hashmap.HashMap.get_mut_in_list_loop T tl key
      let back1 :=
        fun ret =>
          do
          let tl1 ← back ret
          Result.ret (hashmap.List.Cons ckey cvalue tl1)
      Result.ret (t, back1)
  | hashmap.List.Nil => Result.fail .panic

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_mut_in_list]:
   Source: 'src/hashmap.rs', lines 245:4-245:86 -/
def hashmap.HashMap.get_mut_in_list
  (T : Type) (ls : hashmap.List T) (key : Usize) :
  Result (T × (T → Result (hashmap.List T)))
  :=
  hashmap.HashMap.get_mut_in_list_loop T ls key

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::get_mut]:
   Source: 'src/hashmap.rs', lines 257:4-257:67 -/
def hashmap.HashMap.get_mut
  (T : Type) (self : hashmap.HashMap T) (key : Usize) :
  Result (T × (T → Result (hashmap.HashMap T)))
  :=
  do
  let hash ← hashmap.hash_key key
  let i := alloc.vec.Vec.len (hashmap.List T) self.slots
  let hash_mod ← hash % i
  let (l, index_mut_back) ←
    alloc.vec.Vec.index_mut (hashmap.List T) Usize
      (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T)) self.slots
      hash_mod
  let (t, get_mut_in_list_back) ← hashmap.HashMap.get_mut_in_list T l key
  let back :=
    fun ret =>
      do
      let l1 ← get_mut_in_list_back ret
      let v ← index_mut_back l1
      Result.ret { self with slots := v }
  Result.ret (t, back)

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::remove_from_list]: loop 0:
   Source: 'src/hashmap.rs', lines 265:4-291:5 -/
divergent def hashmap.HashMap.remove_from_list_loop
  (T : Type) (key : Usize) (ls : hashmap.List T) :
  Result ((Option T) × (hashmap.List T))
  :=
  match ls with
  | hashmap.List.Cons ckey t tl =>
    if ckey = key
    then
      let (mv_ls, _) :=
        core.mem.replace (hashmap.List T) (hashmap.List.Cons ckey t tl)
          hashmap.List.Nil
      match mv_ls with
      | hashmap.List.Cons _ cvalue tl1 => Result.ret (some cvalue, tl1)
      | hashmap.List.Nil => Result.fail .panic
    else
      do
      let (o, back) ← hashmap.HashMap.remove_from_list_loop T key tl
      Result.ret (o, hashmap.List.Cons ckey t back)
  | hashmap.List.Nil => Result.ret (none, hashmap.List.Nil)

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::remove_from_list]:
   Source: 'src/hashmap.rs', lines 265:4-265:69 -/
def hashmap.HashMap.remove_from_list
  (T : Type) (key : Usize) (ls : hashmap.List T) :
  Result ((Option T) × (hashmap.List T))
  :=
  hashmap.HashMap.remove_from_list_loop T key ls

/- [hashmap_main::hashmap::{hashmap_main::hashmap::HashMap<T>}::remove]:
   Source: 'src/hashmap.rs', lines 294:4-294:52 -/
def hashmap.HashMap.remove
  (T : Type) (self : hashmap.HashMap T) (key : Usize) :
  Result ((Option T) × (hashmap.HashMap T))
  :=
  do
  let hash ← hashmap.hash_key key
  let i := alloc.vec.Vec.len (hashmap.List T) self.slots
  let hash_mod ← hash % i
  let (l, index_mut_back) ←
    alloc.vec.Vec.index_mut (hashmap.List T) Usize
      (core.slice.index.SliceIndexUsizeSliceTInst (hashmap.List T)) self.slots
      hash_mod
  let (x, l1) ← hashmap.HashMap.remove_from_list T key l
  match x with
  | none =>
    do
    let v ← index_mut_back l1
    Result.ret (none, { self with slots := v })
  | some x1 =>
    do
    let i1 ← self.num_entries - 1#usize
    let v ← index_mut_back l1
    Result.ret (some x1, { self with num_entries := i1, slots := v })

/- [hashmap_main::hashmap::test1]:
   Source: 'src/hashmap.rs', lines 315:0-315:10 -/
def hashmap.test1 : Result Unit :=
  do
  let hm ← hashmap.HashMap.new U64
  let hm1 ← hashmap.HashMap.insert U64 hm 0#usize 42#u64
  let hm2 ← hashmap.HashMap.insert U64 hm1 128#usize 18#u64
  let hm3 ← hashmap.HashMap.insert U64 hm2 1024#usize 138#u64
  let hm4 ← hashmap.HashMap.insert U64 hm3 1056#usize 256#u64
  let i ← hashmap.HashMap.get U64 hm4 128#usize
  if ¬ (i = 18#u64)
  then Result.fail .panic
  else
    do
    let (_, get_mut_back) ← hashmap.HashMap.get_mut U64 hm4 1024#usize
    let hm5 ← get_mut_back 56#u64
    let i1 ← hashmap.HashMap.get U64 hm5 1024#usize
    if ¬ (i1 = 56#u64)
    then Result.fail .panic
    else
      do
      let (x, hm6) ← hashmap.HashMap.remove U64 hm5 1024#usize
      match x with
      | none => Result.fail .panic
      | some x1 =>
        if ¬ (x1 = 56#u64)
        then Result.fail .panic
        else
          do
          let i2 ← hashmap.HashMap.get U64 hm6 0#usize
          if ¬ (i2 = 42#u64)
          then Result.fail .panic
          else
            do
            let i3 ← hashmap.HashMap.get U64 hm6 128#usize
            if ¬ (i3 = 18#u64)
            then Result.fail .panic
            else
              do
              let i4 ← hashmap.HashMap.get U64 hm6 1056#usize
              if ¬ (i4 = 256#u64)
              then Result.fail .panic
              else Result.ret ()

/- [hashmap_main::insert_on_disk]:
   Source: 'src/hashmap_main.rs', lines 7:0-7:43 -/
def insert_on_disk
  (key : Usize) (value : U64) (st : State) : Result (State × Unit) :=
  do
  let (st1, hm) ← hashmap_utils.deserialize st
  let hm1 ← hashmap.HashMap.insert U64 hm key value
  hashmap_utils.serialize hm1 st1

/- [hashmap_main::main]:
   Source: 'src/hashmap_main.rs', lines 16:0-16:13 -/
def main : Result Unit :=
  Result.ret ()

end hashmap_main
