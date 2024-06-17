-- THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS
-- [loops]
import Base
open Primitives

namespace loops

/- [loops::sum]: loop 0:
   Source: 'tests/src/loops.rs', lines 8:0-18:1 -/
divergent def sum_loop (max : U32) (i : U32) (s : U32) : Result U32 :=
  if i < max
  then do
       let s1 ← s + i
       let i1 ← i + 1#u32
       sum_loop max i1 s1
  else s * 2#u32

/- [loops::sum]:
   Source: 'tests/src/loops.rs', lines 8:0-8:27 -/
def sum (max : U32) : Result U32 :=
  sum_loop max 0#u32 0#u32

/- [loops::sum_with_mut_borrows]: loop 0:
   Source: 'tests/src/loops.rs', lines 23:0-35:1 -/
divergent def sum_with_mut_borrows_loop
  (max : U32) (i : U32) (s : U32) : Result U32 :=
  if i < max
  then
    do
    let ms ← s + i
    let mi ← i + 1#u32
    sum_with_mut_borrows_loop max mi ms
  else s * 2#u32

/- [loops::sum_with_mut_borrows]:
   Source: 'tests/src/loops.rs', lines 23:0-23:44 -/
def sum_with_mut_borrows (max : U32) : Result U32 :=
  sum_with_mut_borrows_loop max 0#u32 0#u32

/- [loops::sum_with_shared_borrows]: loop 0:
   Source: 'tests/src/loops.rs', lines 38:0-52:1 -/
divergent def sum_with_shared_borrows_loop
  (max : U32) (i : U32) (s : U32) : Result U32 :=
  if i < max
  then
    do
    let i1 ← i + 1#u32
    let s1 ← s + i1
    sum_with_shared_borrows_loop max i1 s1
  else s * 2#u32

/- [loops::sum_with_shared_borrows]:
   Source: 'tests/src/loops.rs', lines 38:0-38:47 -/
def sum_with_shared_borrows (max : U32) : Result U32 :=
  sum_with_shared_borrows_loop max 0#u32 0#u32

/- [loops::sum_array]: loop 0:
   Source: 'tests/src/loops.rs', lines 54:0-62:1 -/
divergent def sum_array_loop
  (N : Usize) (a : Array U32 N) (i : Usize) (s : U32) : Result U32 :=
  if i < N
  then
    do
    let i1 ← Array.index_usize U32 N a i
    let s1 ← s + i1
    let i2 ← i + 1#usize
    sum_array_loop N a i2 s1
  else Result.ok s

/- [loops::sum_array]:
   Source: 'tests/src/loops.rs', lines 54:0-54:52 -/
def sum_array (N : Usize) (a : Array U32 N) : Result U32 :=
  sum_array_loop N a 0#usize 0#u32

/- [loops::clear]: loop 0:
   Source: 'tests/src/loops.rs', lines 66:0-72:1 -/
divergent def clear_loop
  (v : alloc.vec.Vec U32) (i : Usize) : Result (alloc.vec.Vec U32) :=
  let i1 := alloc.vec.Vec.len U32 v
  if i < i1
  then
    do
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut U32 Usize
        (core.slice.index.SliceIndexUsizeSliceTInst U32) v i
    let i2 ← i + 1#usize
    let v1 ← index_mut_back 0#u32
    clear_loop v1 i2
  else Result.ok v

/- [loops::clear]:
   Source: 'tests/src/loops.rs', lines 66:0-66:30 -/
def clear (v : alloc.vec.Vec U32) : Result (alloc.vec.Vec U32) :=
  clear_loop v 0#usize

/- [loops::List]
   Source: 'tests/src/loops.rs', lines 74:0-74:16 -/
inductive List (T : Type) :=
| Cons : T → List T → List T
| Nil : List T

/- [loops::list_mem]: loop 0:
   Source: 'tests/src/loops.rs', lines 80:0-89:1 -/
divergent def list_mem_loop (x : U32) (ls : List U32) : Result Bool :=
  match ls with
  | List.Cons y tl => if y = x
                      then Result.ok true
                      else list_mem_loop x tl
  | List.Nil => Result.ok false

/- [loops::list_mem]:
   Source: 'tests/src/loops.rs', lines 80:0-80:52 -/
@[reducible]
def list_mem (x : U32) (ls : List U32) : Result Bool :=
  list_mem_loop x ls

/- [loops::list_nth_mut_loop]: loop 0:
   Source: 'tests/src/loops.rs', lines 92:0-102:1 -/
divergent def list_nth_mut_loop_loop
  (T : Type) (ls : List T) (i : U32) : Result (T × (T → Result (List T))) :=
  match ls with
  | List.Cons x tl =>
    if i = 0#u32
    then
      let back := fun ret => Result.ok (List.Cons ret tl)
      Result.ok (x, back)
    else
      do
      let i1 ← i - 1#u32
      let (t, back) ← list_nth_mut_loop_loop T tl i1
      let back1 :=
        fun ret => do
                   let tl1 ← back ret
                   Result.ok (List.Cons x tl1)
      Result.ok (t, back1)
  | List.Nil => Result.fail .panic

/- [loops::list_nth_mut_loop]:
   Source: 'tests/src/loops.rs', lines 92:0-92:71 -/
@[reducible]
def list_nth_mut_loop
  (T : Type) (ls : List T) (i : U32) : Result (T × (T → Result (List T))) :=
  list_nth_mut_loop_loop T ls i

/- [loops::list_nth_shared_loop]: loop 0:
   Source: 'tests/src/loops.rs', lines 105:0-115:1 -/
divergent def list_nth_shared_loop_loop
  (T : Type) (ls : List T) (i : U32) : Result T :=
  match ls with
  | List.Cons x tl =>
    if i = 0#u32
    then Result.ok x
    else do
         let i1 ← i - 1#u32
         list_nth_shared_loop_loop T tl i1
  | List.Nil => Result.fail .panic

/- [loops::list_nth_shared_loop]:
   Source: 'tests/src/loops.rs', lines 105:0-105:66 -/
@[reducible]
def list_nth_shared_loop (T : Type) (ls : List T) (i : U32) : Result T :=
  list_nth_shared_loop_loop T ls i

/- [loops::get_elem_mut]: loop 0:
   Source: 'tests/src/loops.rs', lines 117:0-131:1 -/
divergent def get_elem_mut_loop
  (x : Usize) (ls : List Usize) :
  Result (Usize × (Usize → Result (List Usize)))
  :=
  match ls with
  | List.Cons y tl =>
    if y = x
    then
      let back := fun ret => Result.ok (List.Cons ret tl)
      Result.ok (y, back)
    else
      do
      let (i, back) ← get_elem_mut_loop x tl
      let back1 :=
        fun ret => do
                   let tl1 ← back ret
                   Result.ok (List.Cons y tl1)
      Result.ok (i, back1)
  | List.Nil => Result.fail .panic

/- [loops::get_elem_mut]:
   Source: 'tests/src/loops.rs', lines 117:0-117:73 -/
def get_elem_mut
  (slots : alloc.vec.Vec (List Usize)) (x : Usize) :
  Result (Usize × (Usize → Result (alloc.vec.Vec (List Usize))))
  :=
  do
  let (ls, index_mut_back) ←
    alloc.vec.Vec.index_mut (List Usize) Usize
      (core.slice.index.SliceIndexUsizeSliceTInst (List Usize)) slots 0#usize
  let (i, back) ← get_elem_mut_loop x ls
  let back1 := fun ret => do
                          let l ← back ret
                          index_mut_back l
  Result.ok (i, back1)

/- [loops::get_elem_shared]: loop 0:
   Source: 'tests/src/loops.rs', lines 133:0-147:1 -/
divergent def get_elem_shared_loop
  (x : Usize) (ls : List Usize) : Result Usize :=
  match ls with
  | List.Cons y tl => if y = x
                      then Result.ok y
                      else get_elem_shared_loop x tl
  | List.Nil => Result.fail .panic

/- [loops::get_elem_shared]:
   Source: 'tests/src/loops.rs', lines 133:0-133:68 -/
def get_elem_shared
  (slots : alloc.vec.Vec (List Usize)) (x : Usize) : Result Usize :=
  do
  let ls ←
    alloc.vec.Vec.index (List Usize) Usize
      (core.slice.index.SliceIndexUsizeSliceTInst (List Usize)) slots 0#usize
  get_elem_shared_loop x ls

/- [loops::id_mut]:
   Source: 'tests/src/loops.rs', lines 149:0-149:50 -/
def id_mut
  (T : Type) (ls : List T) :
  Result ((List T) × (List T → Result (List T)))
  :=
  Result.ok (ls, Result.ok)

/- [loops::id_shared]:
   Source: 'tests/src/loops.rs', lines 153:0-153:45 -/
def id_shared (T : Type) (ls : List T) : Result (List T) :=
  Result.ok ls

/- [loops::list_nth_mut_loop_with_id]: loop 0:
   Source: 'tests/src/loops.rs', lines 158:0-169:1 -/
divergent def list_nth_mut_loop_with_id_loop
  (T : Type) (i : U32) (ls : List T) : Result (T × (T → Result (List T))) :=
  match ls with
  | List.Cons x tl =>
    if i = 0#u32
    then
      let back := fun ret => Result.ok (List.Cons ret tl)
      Result.ok (x, back)
    else
      do
      let i1 ← i - 1#u32
      let (t, back) ← list_nth_mut_loop_with_id_loop T i1 tl
      let back1 :=
        fun ret => do
                   let tl1 ← back ret
                   Result.ok (List.Cons x tl1)
      Result.ok (t, back1)
  | List.Nil => Result.fail .panic

/- [loops::list_nth_mut_loop_with_id]:
   Source: 'tests/src/loops.rs', lines 158:0-158:75 -/
def list_nth_mut_loop_with_id
  (T : Type) (ls : List T) (i : U32) : Result (T × (T → Result (List T))) :=
  do
  let (ls1, id_mut_back) ← id_mut T ls
  let (t, back) ← list_nth_mut_loop_with_id_loop T i ls1
  let back1 := fun ret => do
                          let l ← back ret
                          id_mut_back l
  Result.ok (t, back1)

/- [loops::list_nth_shared_loop_with_id]: loop 0:
   Source: 'tests/src/loops.rs', lines 172:0-183:1 -/
divergent def list_nth_shared_loop_with_id_loop
  (T : Type) (i : U32) (ls : List T) : Result T :=
  match ls with
  | List.Cons x tl =>
    if i = 0#u32
    then Result.ok x
    else do
         let i1 ← i - 1#u32
         list_nth_shared_loop_with_id_loop T i1 tl
  | List.Nil => Result.fail .panic

/- [loops::list_nth_shared_loop_with_id]:
   Source: 'tests/src/loops.rs', lines 172:0-172:70 -/
def list_nth_shared_loop_with_id
  (T : Type) (ls : List T) (i : U32) : Result T :=
  do
  let ls1 ← id_shared T ls
  list_nth_shared_loop_with_id_loop T i ls1

/- [loops::list_nth_mut_loop_pair]: loop 0:
   Source: 'tests/src/loops.rs', lines 188:0-209:1 -/
divergent def list_nth_mut_loop_pair_loop
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) :
  Result ((T × T) × (T → Result (List T)) × (T → Result (List T)))
  :=
  match ls0 with
  | List.Cons x0 tl0 =>
    match ls1 with
    | List.Cons x1 tl1 =>
      if i = 0#u32
      then
        let back'a := fun ret => Result.ok (List.Cons ret tl0)
        let back'b := fun ret => Result.ok (List.Cons ret tl1)
        Result.ok ((x0, x1), back'a, back'b)
      else
        do
        let i1 ← i - 1#u32
        let (p, back'a, back'b) ← list_nth_mut_loop_pair_loop T tl0 tl1 i1
        let back'a1 :=
          fun ret => do
                     let tl01 ← back'a ret
                     Result.ok (List.Cons x0 tl01)
        let back'b1 :=
          fun ret => do
                     let tl11 ← back'b ret
                     Result.ok (List.Cons x1 tl11)
        Result.ok (p, back'a1, back'b1)
    | List.Nil => Result.fail .panic
  | List.Nil => Result.fail .panic

/- [loops::list_nth_mut_loop_pair]:
   Source: 'tests/src/loops.rs', lines 188:0-192:27 -/
@[reducible]
def list_nth_mut_loop_pair
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) :
  Result ((T × T) × (T → Result (List T)) × (T → Result (List T)))
  :=
  list_nth_mut_loop_pair_loop T ls0 ls1 i

/- [loops::list_nth_shared_loop_pair]: loop 0:
   Source: 'tests/src/loops.rs', lines 212:0-233:1 -/
divergent def list_nth_shared_loop_pair_loop
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) : Result (T × T) :=
  match ls0 with
  | List.Cons x0 tl0 =>
    match ls1 with
    | List.Cons x1 tl1 =>
      if i = 0#u32
      then Result.ok (x0, x1)
      else do
           let i1 ← i - 1#u32
           list_nth_shared_loop_pair_loop T tl0 tl1 i1
    | List.Nil => Result.fail .panic
  | List.Nil => Result.fail .panic

/- [loops::list_nth_shared_loop_pair]:
   Source: 'tests/src/loops.rs', lines 212:0-216:19 -/
@[reducible]
def list_nth_shared_loop_pair
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) : Result (T × T) :=
  list_nth_shared_loop_pair_loop T ls0 ls1 i

/- [loops::list_nth_mut_loop_pair_merge]: loop 0:
   Source: 'tests/src/loops.rs', lines 237:0-252:1 -/
divergent def list_nth_mut_loop_pair_merge_loop
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) :
  Result ((T × T) × ((T × T) → Result ((List T) × (List T))))
  :=
  match ls0 with
  | List.Cons x0 tl0 =>
    match ls1 with
    | List.Cons x1 tl1 =>
      if i = 0#u32
      then
        let back :=
          fun ret =>
            let (t, t1) := ret
            Result.ok (List.Cons t tl0, List.Cons t1 tl1)
        Result.ok ((x0, x1), back)
      else
        do
        let i1 ← i - 1#u32
        let (p, back) ← list_nth_mut_loop_pair_merge_loop T tl0 tl1 i1
        let back1 :=
          fun ret =>
            do
            let (tl01, tl11) ← back ret
            Result.ok (List.Cons x0 tl01, List.Cons x1 tl11)
        Result.ok (p, back1)
    | List.Nil => Result.fail .panic
  | List.Nil => Result.fail .panic

/- [loops::list_nth_mut_loop_pair_merge]:
   Source: 'tests/src/loops.rs', lines 237:0-241:27 -/
@[reducible]
def list_nth_mut_loop_pair_merge
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) :
  Result ((T × T) × ((T × T) → Result ((List T) × (List T))))
  :=
  list_nth_mut_loop_pair_merge_loop T ls0 ls1 i

/- [loops::list_nth_shared_loop_pair_merge]: loop 0:
   Source: 'tests/src/loops.rs', lines 255:0-270:1 -/
divergent def list_nth_shared_loop_pair_merge_loop
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) : Result (T × T) :=
  match ls0 with
  | List.Cons x0 tl0 =>
    match ls1 with
    | List.Cons x1 tl1 =>
      if i = 0#u32
      then Result.ok (x0, x1)
      else
        do
        let i1 ← i - 1#u32
        list_nth_shared_loop_pair_merge_loop T tl0 tl1 i1
    | List.Nil => Result.fail .panic
  | List.Nil => Result.fail .panic

/- [loops::list_nth_shared_loop_pair_merge]:
   Source: 'tests/src/loops.rs', lines 255:0-259:19 -/
@[reducible]
def list_nth_shared_loop_pair_merge
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) : Result (T × T) :=
  list_nth_shared_loop_pair_merge_loop T ls0 ls1 i

/- [loops::list_nth_mut_shared_loop_pair]: loop 0:
   Source: 'tests/src/loops.rs', lines 273:0-288:1 -/
divergent def list_nth_mut_shared_loop_pair_loop
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) :
  Result ((T × T) × (T → Result (List T)))
  :=
  match ls0 with
  | List.Cons x0 tl0 =>
    match ls1 with
    | List.Cons x1 tl1 =>
      if i = 0#u32
      then
        let back := fun ret => Result.ok (List.Cons ret tl0)
        Result.ok ((x0, x1), back)
      else
        do
        let i1 ← i - 1#u32
        let (p, back) ← list_nth_mut_shared_loop_pair_loop T tl0 tl1 i1
        let back1 :=
          fun ret => do
                     let tl01 ← back ret
                     Result.ok (List.Cons x0 tl01)
        Result.ok (p, back1)
    | List.Nil => Result.fail .panic
  | List.Nil => Result.fail .panic

/- [loops::list_nth_mut_shared_loop_pair]:
   Source: 'tests/src/loops.rs', lines 273:0-277:23 -/
@[reducible]
def list_nth_mut_shared_loop_pair
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) :
  Result ((T × T) × (T → Result (List T)))
  :=
  list_nth_mut_shared_loop_pair_loop T ls0 ls1 i

/- [loops::list_nth_mut_shared_loop_pair_merge]: loop 0:
   Source: 'tests/src/loops.rs', lines 292:0-307:1 -/
divergent def list_nth_mut_shared_loop_pair_merge_loop
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) :
  Result ((T × T) × (T → Result (List T)))
  :=
  match ls0 with
  | List.Cons x0 tl0 =>
    match ls1 with
    | List.Cons x1 tl1 =>
      if i = 0#u32
      then
        let back := fun ret => Result.ok (List.Cons ret tl0)
        Result.ok ((x0, x1), back)
      else
        do
        let i1 ← i - 1#u32
        let (p, back) ← list_nth_mut_shared_loop_pair_merge_loop T tl0 tl1 i1
        let back1 :=
          fun ret => do
                     let tl01 ← back ret
                     Result.ok (List.Cons x0 tl01)
        Result.ok (p, back1)
    | List.Nil => Result.fail .panic
  | List.Nil => Result.fail .panic

/- [loops::list_nth_mut_shared_loop_pair_merge]:
   Source: 'tests/src/loops.rs', lines 292:0-296:23 -/
@[reducible]
def list_nth_mut_shared_loop_pair_merge
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) :
  Result ((T × T) × (T → Result (List T)))
  :=
  list_nth_mut_shared_loop_pair_merge_loop T ls0 ls1 i

/- [loops::list_nth_shared_mut_loop_pair]: loop 0:
   Source: 'tests/src/loops.rs', lines 311:0-326:1 -/
divergent def list_nth_shared_mut_loop_pair_loop
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) :
  Result ((T × T) × (T → Result (List T)))
  :=
  match ls0 with
  | List.Cons x0 tl0 =>
    match ls1 with
    | List.Cons x1 tl1 =>
      if i = 0#u32
      then
        let back := fun ret => Result.ok (List.Cons ret tl1)
        Result.ok ((x0, x1), back)
      else
        do
        let i1 ← i - 1#u32
        let (p, back) ← list_nth_shared_mut_loop_pair_loop T tl0 tl1 i1
        let back1 :=
          fun ret => do
                     let tl11 ← back ret
                     Result.ok (List.Cons x1 tl11)
        Result.ok (p, back1)
    | List.Nil => Result.fail .panic
  | List.Nil => Result.fail .panic

/- [loops::list_nth_shared_mut_loop_pair]:
   Source: 'tests/src/loops.rs', lines 311:0-315:23 -/
@[reducible]
def list_nth_shared_mut_loop_pair
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) :
  Result ((T × T) × (T → Result (List T)))
  :=
  list_nth_shared_mut_loop_pair_loop T ls0 ls1 i

/- [loops::list_nth_shared_mut_loop_pair_merge]: loop 0:
   Source: 'tests/src/loops.rs', lines 330:0-345:1 -/
divergent def list_nth_shared_mut_loop_pair_merge_loop
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) :
  Result ((T × T) × (T → Result (List T)))
  :=
  match ls0 with
  | List.Cons x0 tl0 =>
    match ls1 with
    | List.Cons x1 tl1 =>
      if i = 0#u32
      then
        let back := fun ret => Result.ok (List.Cons ret tl1)
        Result.ok ((x0, x1), back)
      else
        do
        let i1 ← i - 1#u32
        let (p, back) ← list_nth_shared_mut_loop_pair_merge_loop T tl0 tl1 i1
        let back1 :=
          fun ret => do
                     let tl11 ← back ret
                     Result.ok (List.Cons x1 tl11)
        Result.ok (p, back1)
    | List.Nil => Result.fail .panic
  | List.Nil => Result.fail .panic

/- [loops::list_nth_shared_mut_loop_pair_merge]:
   Source: 'tests/src/loops.rs', lines 330:0-334:23 -/
@[reducible]
def list_nth_shared_mut_loop_pair_merge
  (T : Type) (ls0 : List T) (ls1 : List T) (i : U32) :
  Result ((T × T) × (T → Result (List T)))
  :=
  list_nth_shared_mut_loop_pair_merge_loop T ls0 ls1 i

/- [loops::ignore_input_mut_borrow]: loop 0:
   Source: 'tests/src/loops.rs', lines 349:0-353:1 -/
divergent def ignore_input_mut_borrow_loop (i : U32) : Result Unit :=
  if i > 0#u32
  then do
       let i1 ← i - 1#u32
       ignore_input_mut_borrow_loop i1
  else Result.ok ()

/- [loops::ignore_input_mut_borrow]:
   Source: 'tests/src/loops.rs', lines 349:0-349:56 -/
def ignore_input_mut_borrow (_a : U32) (i : U32) : Result U32 :=
  do
  let _ ← ignore_input_mut_borrow_loop i
  Result.ok _a

/- [loops::incr_ignore_input_mut_borrow]: loop 0:
   Source: 'tests/src/loops.rs', lines 357:0-362:1 -/
divergent def incr_ignore_input_mut_borrow_loop (i : U32) : Result Unit :=
  if i > 0#u32
  then do
       let i1 ← i - 1#u32
       incr_ignore_input_mut_borrow_loop i1
  else Result.ok ()

/- [loops::incr_ignore_input_mut_borrow]:
   Source: 'tests/src/loops.rs', lines 357:0-357:60 -/
def incr_ignore_input_mut_borrow (a : U32) (i : U32) : Result U32 :=
  do
  let a1 ← a + 1#u32
  let _ ← incr_ignore_input_mut_borrow_loop i
  Result.ok a1

/- [loops::ignore_input_shared_borrow]: loop 0:
   Source: 'tests/src/loops.rs', lines 366:0-370:1 -/
divergent def ignore_input_shared_borrow_loop (i : U32) : Result Unit :=
  if i > 0#u32
  then do
       let i1 ← i - 1#u32
       ignore_input_shared_borrow_loop i1
  else Result.ok ()

/- [loops::ignore_input_shared_borrow]:
   Source: 'tests/src/loops.rs', lines 366:0-366:59 -/
def ignore_input_shared_borrow (_a : U32) (i : U32) : Result U32 :=
  do
  let _ ← ignore_input_shared_borrow_loop i
  Result.ok _a

end loops
