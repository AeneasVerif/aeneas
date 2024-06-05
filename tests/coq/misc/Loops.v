(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [loops] *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Module Loops.

(** [loops::sum]: loop 0:
    Source: 'tests/src/loops.rs', lines 7:0-17:1 *)
Fixpoint sum_loop (max : u32) (i : u32) (s : u32) : result u32 :=
  if i s< max
  then (s1 <- u32_add s i; i1 <- u32_add i 1%u32; sum_loop max i1 s1)
  else u32_mul s 2%u32
.

(** [loops::sum]:
    Source: 'tests/src/loops.rs', lines 7:0-7:27 *)
Definition sum (max : u32) : result u32 :=
  sum_loop max 0%u32 0%u32.

(** [loops::sum_with_mut_borrows]: loop 0:
    Source: 'tests/src/loops.rs', lines 22:0-34:1 *)
Fixpoint sum_with_mut_borrows_loop
  (max : u32) (i : u32) (s : u32) : result u32 :=
  if i s< max
  then (
    ms <- u32_add s i;
    mi <- u32_add i 1%u32;
    sum_with_mut_borrows_loop max mi ms)
  else u32_mul s 2%u32
.

(** [loops::sum_with_mut_borrows]:
    Source: 'tests/src/loops.rs', lines 22:0-22:44 *)
Definition sum_with_mut_borrows (max : u32) : result u32 :=
  sum_with_mut_borrows_loop max 0%u32 0%u32
.

(** [loops::sum_with_shared_borrows]: loop 0:
    Source: 'tests/src/loops.rs', lines 37:0-51:1 *)
Fixpoint sum_with_shared_borrows_loop
  (max : u32) (i : u32) (s : u32) : result u32 :=
  if i s< max
  then (
    i1 <- u32_add i 1%u32;
    s1 <- u32_add s i1;
    sum_with_shared_borrows_loop max i1 s1)
  else u32_mul s 2%u32
.

(** [loops::sum_with_shared_borrows]:
    Source: 'tests/src/loops.rs', lines 37:0-37:47 *)
Definition sum_with_shared_borrows (max : u32) : result u32 :=
  sum_with_shared_borrows_loop max 0%u32 0%u32
.

(** [loops::sum_array]: loop 0:
    Source: 'tests/src/loops.rs', lines 53:0-61:1 *)
Fixpoint sum_array_loop
  (N : usize) (a : array u32 N) (i : usize) (s : u32) : result u32 :=
  if i s< N
  then (
    i1 <- array_index_usize u32 N a i;
    s1 <- u32_add s i1;
    i2 <- usize_add i 1%usize;
    sum_array_loop N a i2 s1)
  else Ok s
.

(** [loops::sum_array]:
    Source: 'tests/src/loops.rs', lines 53:0-53:52 *)
Definition sum_array (N : usize) (a : array u32 N) : result u32 :=
  sum_array_loop N a 0%usize 0%u32
.

(** [loops::clear]: loop 0:
    Source: 'tests/src/loops.rs', lines 65:0-71:1 *)
Fixpoint clear_loop
  (v : alloc_vec_Vec u32) (i : usize) : result (alloc_vec_Vec u32) :=
  let i1 := alloc_vec_Vec_len u32 v in
  if i s< i1
  then (
    p <-
      alloc_vec_Vec_index_mut u32 usize
        (core_slice_index_SliceIndexUsizeSliceTInst u32) v i;
    let (_, index_mut_back) := p in
    i2 <- usize_add i 1%usize;
    v1 <- index_mut_back 0%u32;
    clear_loop v1 i2)
  else Ok v
.

(** [loops::clear]:
    Source: 'tests/src/loops.rs', lines 65:0-65:30 *)
Definition clear (v : alloc_vec_Vec u32) : result (alloc_vec_Vec u32) :=
  clear_loop v 0%usize
.

(** [loops::List]
    Source: 'tests/src/loops.rs', lines 73:0-73:16 *)
Inductive List_t (T : Type) :=
| List_Cons : T -> List_t T -> List_t T
| List_Nil : List_t T
.

Arguments List_Cons { _ }.
Arguments List_Nil { _ }.

(** [loops::list_mem]: loop 0:
    Source: 'tests/src/loops.rs', lines 79:0-88:1 *)
Fixpoint list_mem_loop (x : u32) (ls : List_t u32) : result bool :=
  match ls with
  | List_Cons y tl => if y s= x then Ok true else list_mem_loop x tl
  | List_Nil => Ok false
  end
.

(** [loops::list_mem]:
    Source: 'tests/src/loops.rs', lines 79:0-79:52 *)
Definition list_mem (x : u32) (ls : List_t u32) : result bool :=
  list_mem_loop x ls
.

(** [loops::list_nth_mut_loop]: loop 0:
    Source: 'tests/src/loops.rs', lines 91:0-101:1 *)
Fixpoint list_nth_mut_loop_loop
  (T : Type) (ls : List_t T) (i : u32) :
  result (T * (T -> result (List_t T)))
  :=
  match ls with
  | List_Cons x tl =>
    if i s= 0%u32
    then let back := fun (ret : T) => Ok (List_Cons ret tl) in Ok (x, back)
    else (
      i1 <- u32_sub i 1%u32;
      p <- list_nth_mut_loop_loop T tl i1;
      let (t, back) := p in
      let back1 := fun (ret : T) => tl1 <- back ret; Ok (List_Cons x tl1) in
      Ok (t, back1))
  | List_Nil => Fail_ Failure
  end
.

(** [loops::list_nth_mut_loop]:
    Source: 'tests/src/loops.rs', lines 91:0-91:71 *)
Definition list_nth_mut_loop
  (T : Type) (ls : List_t T) (i : u32) :
  result (T * (T -> result (List_t T)))
  :=
  list_nth_mut_loop_loop T ls i
.

(** [loops::list_nth_shared_loop]: loop 0:
    Source: 'tests/src/loops.rs', lines 104:0-114:1 *)
Fixpoint list_nth_shared_loop_loop
  (T : Type) (ls : List_t T) (i : u32) : result T :=
  match ls with
  | List_Cons x tl =>
    if i s= 0%u32
    then Ok x
    else (i1 <- u32_sub i 1%u32; list_nth_shared_loop_loop T tl i1)
  | List_Nil => Fail_ Failure
  end
.

(** [loops::list_nth_shared_loop]:
    Source: 'tests/src/loops.rs', lines 104:0-104:66 *)
Definition list_nth_shared_loop
  (T : Type) (ls : List_t T) (i : u32) : result T :=
  list_nth_shared_loop_loop T ls i
.

(** [loops::get_elem_mut]: loop 0:
    Source: 'tests/src/loops.rs', lines 116:0-130:1 *)
Fixpoint get_elem_mut_loop
  (x : usize) (ls : List_t usize) :
  result (usize * (usize -> result (List_t usize)))
  :=
  match ls with
  | List_Cons y tl =>
    if y s= x
    then let back := fun (ret : usize) => Ok (List_Cons ret tl) in Ok (y, back)
    else (
      p <- get_elem_mut_loop x tl;
      let (i, back) := p in
      let back1 := fun (ret : usize) => tl1 <- back ret; Ok (List_Cons y tl1)
        in
      Ok (i, back1))
  | List_Nil => Fail_ Failure
  end
.

(** [loops::get_elem_mut]:
    Source: 'tests/src/loops.rs', lines 116:0-116:73 *)
Definition get_elem_mut
  (slots : alloc_vec_Vec (List_t usize)) (x : usize) :
  result (usize * (usize -> result (alloc_vec_Vec (List_t usize))))
  :=
  p <-
    alloc_vec_Vec_index_mut (List_t usize) usize
      (core_slice_index_SliceIndexUsizeSliceTInst (List_t usize)) slots 0%usize;
  let (ls, index_mut_back) := p in
  p1 <- get_elem_mut_loop x ls;
  let (i, back) := p1 in
  let back1 := fun (ret : usize) => l <- back ret; index_mut_back l in
  Ok (i, back1)
.

(** [loops::get_elem_shared]: loop 0:
    Source: 'tests/src/loops.rs', lines 132:0-146:1 *)
Fixpoint get_elem_shared_loop (x : usize) (ls : List_t usize) : result usize :=
  match ls with
  | List_Cons y tl => if y s= x then Ok y else get_elem_shared_loop x tl
  | List_Nil => Fail_ Failure
  end
.

(** [loops::get_elem_shared]:
    Source: 'tests/src/loops.rs', lines 132:0-132:68 *)
Definition get_elem_shared
  (slots : alloc_vec_Vec (List_t usize)) (x : usize) : result usize :=
  ls <-
    alloc_vec_Vec_index (List_t usize) usize
      (core_slice_index_SliceIndexUsizeSliceTInst (List_t usize)) slots 0%usize;
  get_elem_shared_loop x ls
.

(** [loops::id_mut]:
    Source: 'tests/src/loops.rs', lines 148:0-148:50 *)
Definition id_mut
  (T : Type) (ls : List_t T) :
  result ((List_t T) * (List_t T -> result (List_t T)))
  :=
  Ok (ls, Ok)
.

(** [loops::id_shared]:
    Source: 'tests/src/loops.rs', lines 152:0-152:45 *)
Definition id_shared (T : Type) (ls : List_t T) : result (List_t T) :=
  Ok ls.

(** [loops::list_nth_mut_loop_with_id]: loop 0:
    Source: 'tests/src/loops.rs', lines 157:0-168:1 *)
Fixpoint list_nth_mut_loop_with_id_loop
  (T : Type) (i : u32) (ls : List_t T) :
  result (T * (T -> result (List_t T)))
  :=
  match ls with
  | List_Cons x tl =>
    if i s= 0%u32
    then let back := fun (ret : T) => Ok (List_Cons ret tl) in Ok (x, back)
    else (
      i1 <- u32_sub i 1%u32;
      p <- list_nth_mut_loop_with_id_loop T i1 tl;
      let (t, back) := p in
      let back1 := fun (ret : T) => tl1 <- back ret; Ok (List_Cons x tl1) in
      Ok (t, back1))
  | List_Nil => Fail_ Failure
  end
.

(** [loops::list_nth_mut_loop_with_id]:
    Source: 'tests/src/loops.rs', lines 157:0-157:75 *)
Definition list_nth_mut_loop_with_id
  (T : Type) (ls : List_t T) (i : u32) :
  result (T * (T -> result (List_t T)))
  :=
  p <- id_mut T ls;
  let (ls1, id_mut_back) := p in
  p1 <- list_nth_mut_loop_with_id_loop T i ls1;
  let (t, back) := p1 in
  let back1 := fun (ret : T) => l <- back ret; id_mut_back l in
  Ok (t, back1)
.

(** [loops::list_nth_shared_loop_with_id]: loop 0:
    Source: 'tests/src/loops.rs', lines 171:0-182:1 *)
Fixpoint list_nth_shared_loop_with_id_loop
  (T : Type) (i : u32) (ls : List_t T) : result T :=
  match ls with
  | List_Cons x tl =>
    if i s= 0%u32
    then Ok x
    else (i1 <- u32_sub i 1%u32; list_nth_shared_loop_with_id_loop T i1 tl)
  | List_Nil => Fail_ Failure
  end
.

(** [loops::list_nth_shared_loop_with_id]:
    Source: 'tests/src/loops.rs', lines 171:0-171:70 *)
Definition list_nth_shared_loop_with_id
  (T : Type) (ls : List_t T) (i : u32) : result T :=
  ls1 <- id_shared T ls; list_nth_shared_loop_with_id_loop T i ls1
.

(** [loops::list_nth_mut_loop_pair]: loop 0:
    Source: 'tests/src/loops.rs', lines 187:0-208:1 *)
Fixpoint list_nth_mut_loop_pair_loop
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)) * (T -> result (List_t T)))
  :=
  match ls0 with
  | List_Cons x0 tl0 =>
    match ls1 with
    | List_Cons x1 tl1 =>
      if i s= 0%u32
      then
        let back'a := fun (ret : T) => Ok (List_Cons ret tl0) in
        let back'b := fun (ret : T) => Ok (List_Cons ret tl1) in
        Ok ((x0, x1), back'a, back'b)
      else (
        i1 <- u32_sub i 1%u32;
        t <- list_nth_mut_loop_pair_loop T tl0 tl1 i1;
        let '(p, back'a, back'b) := t in
        let back'a1 :=
          fun (ret : T) => tl01 <- back'a ret; Ok (List_Cons x0 tl01) in
        let back'b1 :=
          fun (ret : T) => tl11 <- back'b ret; Ok (List_Cons x1 tl11) in
        Ok (p, back'a1, back'b1))
    | List_Nil => Fail_ Failure
    end
  | List_Nil => Fail_ Failure
  end
.

(** [loops::list_nth_mut_loop_pair]:
    Source: 'tests/src/loops.rs', lines 187:0-191:27 *)
Definition list_nth_mut_loop_pair
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)) * (T -> result (List_t T)))
  :=
  list_nth_mut_loop_pair_loop T ls0 ls1 i
.

(** [loops::list_nth_shared_loop_pair]: loop 0:
    Source: 'tests/src/loops.rs', lines 211:0-232:1 *)
Fixpoint list_nth_shared_loop_pair_loop
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) : result (T * T) :=
  match ls0 with
  | List_Cons x0 tl0 =>
    match ls1 with
    | List_Cons x1 tl1 =>
      if i s= 0%u32
      then Ok (x0, x1)
      else (i1 <- u32_sub i 1%u32; list_nth_shared_loop_pair_loop T tl0 tl1 i1)
    | List_Nil => Fail_ Failure
    end
  | List_Nil => Fail_ Failure
  end
.

(** [loops::list_nth_shared_loop_pair]:
    Source: 'tests/src/loops.rs', lines 211:0-215:19 *)
Definition list_nth_shared_loop_pair
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) : result (T * T) :=
  list_nth_shared_loop_pair_loop T ls0 ls1 i
.

(** [loops::list_nth_mut_loop_pair_merge]: loop 0:
    Source: 'tests/src/loops.rs', lines 236:0-251:1 *)
Fixpoint list_nth_mut_loop_pair_merge_loop
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * ((T * T) -> result ((List_t T) * (List_t T))))
  :=
  match ls0 with
  | List_Cons x0 tl0 =>
    match ls1 with
    | List_Cons x1 tl1 =>
      if i s= 0%u32
      then
        let back :=
          fun (ret : (T * T)) =>
            let (t, t1) := ret in Ok (List_Cons t tl0, List_Cons t1 tl1) in
        Ok ((x0, x1), back)
      else (
        i1 <- u32_sub i 1%u32;
        p <- list_nth_mut_loop_pair_merge_loop T tl0 tl1 i1;
        let (p1, back) := p in
        let back1 :=
          fun (ret : (T * T)) =>
            p2 <- back ret;
            let (tl01, tl11) := p2 in
            Ok (List_Cons x0 tl01, List_Cons x1 tl11) in
        Ok (p1, back1))
    | List_Nil => Fail_ Failure
    end
  | List_Nil => Fail_ Failure
  end
.

(** [loops::list_nth_mut_loop_pair_merge]:
    Source: 'tests/src/loops.rs', lines 236:0-240:27 *)
Definition list_nth_mut_loop_pair_merge
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * ((T * T) -> result ((List_t T) * (List_t T))))
  :=
  list_nth_mut_loop_pair_merge_loop T ls0 ls1 i
.

(** [loops::list_nth_shared_loop_pair_merge]: loop 0:
    Source: 'tests/src/loops.rs', lines 254:0-269:1 *)
Fixpoint list_nth_shared_loop_pair_merge_loop
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) : result (T * T) :=
  match ls0 with
  | List_Cons x0 tl0 =>
    match ls1 with
    | List_Cons x1 tl1 =>
      if i s= 0%u32
      then Ok (x0, x1)
      else (
        i1 <- u32_sub i 1%u32;
        list_nth_shared_loop_pair_merge_loop T tl0 tl1 i1)
    | List_Nil => Fail_ Failure
    end
  | List_Nil => Fail_ Failure
  end
.

(** [loops::list_nth_shared_loop_pair_merge]:
    Source: 'tests/src/loops.rs', lines 254:0-258:19 *)
Definition list_nth_shared_loop_pair_merge
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) : result (T * T) :=
  list_nth_shared_loop_pair_merge_loop T ls0 ls1 i
.

(** [loops::list_nth_mut_shared_loop_pair]: loop 0:
    Source: 'tests/src/loops.rs', lines 272:0-287:1 *)
Fixpoint list_nth_mut_shared_loop_pair_loop
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  match ls0 with
  | List_Cons x0 tl0 =>
    match ls1 with
    | List_Cons x1 tl1 =>
      if i s= 0%u32
      then
        let back := fun (ret : T) => Ok (List_Cons ret tl0) in
        Ok ((x0, x1), back)
      else (
        i1 <- u32_sub i 1%u32;
        p <- list_nth_mut_shared_loop_pair_loop T tl0 tl1 i1;
        let (p1, back) := p in
        let back1 := fun (ret : T) => tl01 <- back ret; Ok (List_Cons x0 tl01)
          in
        Ok (p1, back1))
    | List_Nil => Fail_ Failure
    end
  | List_Nil => Fail_ Failure
  end
.

(** [loops::list_nth_mut_shared_loop_pair]:
    Source: 'tests/src/loops.rs', lines 272:0-276:23 *)
Definition list_nth_mut_shared_loop_pair
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  list_nth_mut_shared_loop_pair_loop T ls0 ls1 i
.

(** [loops::list_nth_mut_shared_loop_pair_merge]: loop 0:
    Source: 'tests/src/loops.rs', lines 291:0-306:1 *)
Fixpoint list_nth_mut_shared_loop_pair_merge_loop
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  match ls0 with
  | List_Cons x0 tl0 =>
    match ls1 with
    | List_Cons x1 tl1 =>
      if i s= 0%u32
      then
        let back := fun (ret : T) => Ok (List_Cons ret tl0) in
        Ok ((x0, x1), back)
      else (
        i1 <- u32_sub i 1%u32;
        p <- list_nth_mut_shared_loop_pair_merge_loop T tl0 tl1 i1;
        let (p1, back) := p in
        let back1 := fun (ret : T) => tl01 <- back ret; Ok (List_Cons x0 tl01)
          in
        Ok (p1, back1))
    | List_Nil => Fail_ Failure
    end
  | List_Nil => Fail_ Failure
  end
.

(** [loops::list_nth_mut_shared_loop_pair_merge]:
    Source: 'tests/src/loops.rs', lines 291:0-295:23 *)
Definition list_nth_mut_shared_loop_pair_merge
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  list_nth_mut_shared_loop_pair_merge_loop T ls0 ls1 i
.

(** [loops::list_nth_shared_mut_loop_pair]: loop 0:
    Source: 'tests/src/loops.rs', lines 310:0-325:1 *)
Fixpoint list_nth_shared_mut_loop_pair_loop
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  match ls0 with
  | List_Cons x0 tl0 =>
    match ls1 with
    | List_Cons x1 tl1 =>
      if i s= 0%u32
      then
        let back := fun (ret : T) => Ok (List_Cons ret tl1) in
        Ok ((x0, x1), back)
      else (
        i1 <- u32_sub i 1%u32;
        p <- list_nth_shared_mut_loop_pair_loop T tl0 tl1 i1;
        let (p1, back) := p in
        let back1 := fun (ret : T) => tl11 <- back ret; Ok (List_Cons x1 tl11)
          in
        Ok (p1, back1))
    | List_Nil => Fail_ Failure
    end
  | List_Nil => Fail_ Failure
  end
.

(** [loops::list_nth_shared_mut_loop_pair]:
    Source: 'tests/src/loops.rs', lines 310:0-314:23 *)
Definition list_nth_shared_mut_loop_pair
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  list_nth_shared_mut_loop_pair_loop T ls0 ls1 i
.

(** [loops::list_nth_shared_mut_loop_pair_merge]: loop 0:
    Source: 'tests/src/loops.rs', lines 329:0-344:1 *)
Fixpoint list_nth_shared_mut_loop_pair_merge_loop
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  match ls0 with
  | List_Cons x0 tl0 =>
    match ls1 with
    | List_Cons x1 tl1 =>
      if i s= 0%u32
      then
        let back := fun (ret : T) => Ok (List_Cons ret tl1) in
        Ok ((x0, x1), back)
      else (
        i1 <- u32_sub i 1%u32;
        p <- list_nth_shared_mut_loop_pair_merge_loop T tl0 tl1 i1;
        let (p1, back) := p in
        let back1 := fun (ret : T) => tl11 <- back ret; Ok (List_Cons x1 tl11)
          in
        Ok (p1, back1))
    | List_Nil => Fail_ Failure
    end
  | List_Nil => Fail_ Failure
  end
.

(** [loops::list_nth_shared_mut_loop_pair_merge]:
    Source: 'tests/src/loops.rs', lines 329:0-333:23 *)
Definition list_nth_shared_mut_loop_pair_merge
  (T : Type) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  list_nth_shared_mut_loop_pair_merge_loop T ls0 ls1 i
.

(** [loops::ignore_input_mut_borrow]: loop 0:
    Source: 'tests/src/loops.rs', lines 348:0-352:1 *)
Fixpoint ignore_input_mut_borrow_loop (i : u32) : result unit :=
  if i s> 0%u32
  then (i1 <- u32_sub i 1%u32; ignore_input_mut_borrow_loop i1)
  else Ok tt
.

(** [loops::ignore_input_mut_borrow]:
    Source: 'tests/src/loops.rs', lines 348:0-348:56 *)
Definition ignore_input_mut_borrow (_a : u32) (i : u32) : result u32 :=
  _ <- ignore_input_mut_borrow_loop i; Ok _a
.

(** [loops::incr_ignore_input_mut_borrow]: loop 0:
    Source: 'tests/src/loops.rs', lines 356:0-361:1 *)
Fixpoint incr_ignore_input_mut_borrow_loop (i : u32) : result unit :=
  if i s> 0%u32
  then (i1 <- u32_sub i 1%u32; incr_ignore_input_mut_borrow_loop i1)
  else Ok tt
.

(** [loops::incr_ignore_input_mut_borrow]:
    Source: 'tests/src/loops.rs', lines 356:0-356:60 *)
Definition incr_ignore_input_mut_borrow (a : u32) (i : u32) : result u32 :=
  a1 <- u32_add a 1%u32; _ <- incr_ignore_input_mut_borrow_loop i; Ok a1
.

(** [loops::ignore_input_shared_borrow]: loop 0:
    Source: 'tests/src/loops.rs', lines 365:0-369:1 *)
Fixpoint ignore_input_shared_borrow_loop (i : u32) : result unit :=
  if i s> 0%u32
  then (i1 <- u32_sub i 1%u32; ignore_input_shared_borrow_loop i1)
  else Ok tt
.

(** [loops::ignore_input_shared_borrow]:
    Source: 'tests/src/loops.rs', lines 365:0-365:59 *)
Definition ignore_input_shared_borrow (_a : u32) (i : u32) : result u32 :=
  _ <- ignore_input_shared_borrow_loop i; Ok _a
.

(** [loops::sum1]: loop 0:
    Source: 'tests/src/loops.rs', lines 373:0-381:1 *)
Fixpoint sum1_loop (s : slice u32) (sum3 : u32) (i : usize) : result u32 :=
  let i1 := slice_len u32 s in
  if i s< i1
  then (
    i2 <- slice_index_usize u32 s i;
    sum4 <- u32_add sum3 i2;
    i3 <- usize_add i 1%usize;
    sum1_loop s sum4 i3)
  else Ok sum3
.

(** [loops::sum1]:
    Source: 'tests/src/loops.rs', lines 373:0-373:29 *)
Definition sum1 (s : slice u32) : result u32 :=
  sum1_loop s 0%u32 0%usize.

(** [loops::sum2]: loop 0:
    Source: 'tests/src/loops.rs', lines 383:0-392:1 *)
Fixpoint sum2_loop
  (s : slice u32) (s2 : slice u32) (sum3 : u32) (i : usize) : result u32 :=
  let i1 := slice_len u32 s in
  if i s< i1
  then (
    i2 <- slice_index_usize u32 s i;
    i3 <- slice_index_usize u32 s2 i;
    i4 <- u32_add i2 i3;
    sum4 <- u32_add sum3 i4;
    i5 <- usize_add i 1%usize;
    sum2_loop s s2 sum4 i5)
  else Ok sum3
.

(** [loops::sum2]:
    Source: 'tests/src/loops.rs', lines 383:0-383:41 *)
Definition sum2 (s : slice u32) (s2 : slice u32) : result u32 :=
  let i := slice_len u32 s in
  let i1 := slice_len u32 s2 in
  if i s= i1 then sum2_loop s s2 0%u32 0%usize else Fail_ Failure
.

(** [loops::zero_slice]: loop 0:
    Source: 'tests/src/loops.rs', lines 394:0-401:1 *)
Fixpoint zero_slice_loop
  (a : slice u8) (i : usize) (len : usize) : result (slice u8) :=
  if i s< len
  then (
    p <- slice_index_mut_usize u8 a i;
    let (_, index_mut_back) := p in
    i1 <- usize_add i 1%usize;
    a1 <- index_mut_back 0%u8;
    zero_slice_loop a1 i1 len)
  else Ok a
.

(** [loops::zero_slice]:
    Source: 'tests/src/loops.rs', lines 394:0-394:31 *)
Definition zero_slice (a : slice u8) : result (slice u8) :=
  let len := slice_len u8 a in zero_slice_loop a 0%usize len
.

(** [loops::iter_mut_slice]: loop 0:
    Source: 'tests/src/loops.rs', lines 403:0-409:1 *)
Fixpoint iter_mut_slice_loop (len : usize) (i : usize) : result unit :=
  if i s< len
  then (i1 <- usize_add i 1%usize; iter_mut_slice_loop len i1)
  else Ok tt
.

(** [loops::iter_mut_slice]:
    Source: 'tests/src/loops.rs', lines 403:0-403:35 *)
Definition iter_mut_slice (a : slice u8) : result (slice u8) :=
  let len := slice_len u8 a in _ <- iter_mut_slice_loop len 0%usize; Ok a
.

(** [loops::sum_mut_slice]: loop 0:
    Source: 'tests/src/loops.rs', lines 411:0-419:1 *)
Fixpoint sum_mut_slice_loop
  (a : slice u32) (i : usize) (s : u32) : result u32 :=
  let i1 := slice_len u32 a in
  if i s< i1
  then (
    i2 <- slice_index_usize u32 a i;
    s1 <- u32_add s i2;
    i3 <- usize_add i 1%usize;
    sum_mut_slice_loop a i3 s1)
  else Ok s
.

(** [loops::sum_mut_slice]:
    Source: 'tests/src/loops.rs', lines 411:0-411:42 *)
Definition sum_mut_slice (a : slice u32) : result (u32 * (slice u32)) :=
  i <- sum_mut_slice_loop a 0%usize 0%u32; Ok (i, a)
.

End Loops.
