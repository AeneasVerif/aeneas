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
    Source: 'src/loops.rs', lines 4:0-14:1 *)
Fixpoint sum_loop (n : nat) (max : u32) (i : u32) (s : u32) : result u32 :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if i s< max
    then (s1 <- u32_add s i; i1 <- u32_add i 1%u32; sum_loop n1 max i1 s1)
    else u32_mul s 2%u32
  end
.

(** [loops::sum]:
    Source: 'src/loops.rs', lines 4:0-4:27 *)
Definition sum (n : nat) (max : u32) : result u32 :=
  sum_loop n max 0%u32 0%u32
.

(** [loops::sum_with_mut_borrows]: loop 0:
    Source: 'src/loops.rs', lines 19:0-31:1 *)
Fixpoint sum_with_mut_borrows_loop
  (n : nat) (max : u32) (i : u32) (s : u32) : result u32 :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if i s< max
    then (
      ms <- u32_add s i;
      mi <- u32_add i 1%u32;
      sum_with_mut_borrows_loop n1 max mi ms)
    else u32_mul s 2%u32
  end
.

(** [loops::sum_with_mut_borrows]:
    Source: 'src/loops.rs', lines 19:0-19:44 *)
Definition sum_with_mut_borrows (n : nat) (max : u32) : result u32 :=
  sum_with_mut_borrows_loop n max 0%u32 0%u32
.

(** [loops::sum_with_shared_borrows]: loop 0:
    Source: 'src/loops.rs', lines 34:0-48:1 *)
Fixpoint sum_with_shared_borrows_loop
  (n : nat) (max : u32) (i : u32) (s : u32) : result u32 :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if i s< max
    then (
      i1 <- u32_add i 1%u32;
      s1 <- u32_add s i1;
      sum_with_shared_borrows_loop n1 max i1 s1)
    else u32_mul s 2%u32
  end
.

(** [loops::sum_with_shared_borrows]:
    Source: 'src/loops.rs', lines 34:0-34:47 *)
Definition sum_with_shared_borrows (n : nat) (max : u32) : result u32 :=
  sum_with_shared_borrows_loop n max 0%u32 0%u32
.

(** [loops::sum_array]: loop 0:
    Source: 'src/loops.rs', lines 50:0-58:1 *)
Fixpoint sum_array_loop
  (N : usize) (n : nat) (a : array u32 N) (i : usize) (s : u32) : result u32 :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if i s< N
    then (
      i1 <- array_index_usize u32 N a i;
      s1 <- u32_add s i1;
      i2 <- usize_add i 1%usize;
      sum_array_loop N n1 a i2 s1)
    else Return s
  end
.

(** [loops::sum_array]:
    Source: 'src/loops.rs', lines 50:0-50:52 *)
Definition sum_array (N : usize) (n : nat) (a : array u32 N) : result u32 :=
  sum_array_loop N n a 0%usize 0%u32
.

(** [loops::clear]: loop 0:
    Source: 'src/loops.rs', lines 62:0-68:1 *)
Fixpoint clear_loop
  (n : nat) (v : alloc_vec_Vec u32) (i : usize) : result (alloc_vec_Vec u32) :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    let i1 := alloc_vec_Vec_len u32 v in
    if i s< i1
    then (
      p <-
        alloc_vec_Vec_index_mut u32 usize
          (core_slice_index_SliceIndexUsizeSliceTInst u32) v i;
      let (_, index_mut_back) := p in
      i2 <- usize_add i 1%usize;
      v1 <- index_mut_back 0%u32;
      clear_loop n1 v1 i2)
    else Return v
  end
.

(** [loops::clear]:
    Source: 'src/loops.rs', lines 62:0-62:30 *)
Definition clear
  (n : nat) (v : alloc_vec_Vec u32) : result (alloc_vec_Vec u32) :=
  clear_loop n v 0%usize
.

(** [loops::List]
    Source: 'src/loops.rs', lines 70:0-70:16 *)
Inductive List_t (T : Type) :=
| List_Cons : T -> List_t T -> List_t T
| List_Nil : List_t T
.

Arguments List_Cons { _ }.
Arguments List_Nil { _ }.

(** [loops::list_mem]: loop 0:
    Source: 'src/loops.rs', lines 76:0-85:1 *)
Fixpoint list_mem_loop (n : nat) (x : u32) (ls : List_t u32) : result bool :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | List_Cons y tl => if y s= x then Return true else list_mem_loop n1 x tl
    | List_Nil => Return false
    end
  end
.

(** [loops::list_mem]:
    Source: 'src/loops.rs', lines 76:0-76:52 *)
Definition list_mem (n : nat) (x : u32) (ls : List_t u32) : result bool :=
  list_mem_loop n x ls
.

(** [loops::list_nth_mut_loop]: loop 0:
    Source: 'src/loops.rs', lines 88:0-98:1 *)
Fixpoint list_nth_mut_loop_loop
  (T : Type) (n : nat) (ls : List_t T) (i : u32) :
  result (T * (T -> result (List_t T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | List_Cons x tl =>
      if i s= 0%u32
      then
        let back := fun (ret : T) => Return (List_Cons ret tl) in
        Return (x, back)
      else (
        i1 <- u32_sub i 1%u32;
        p <- list_nth_mut_loop_loop T n1 tl i1;
        let (t, back) := p in
        let back1 := fun (ret : T) => tl1 <- back ret; Return (List_Cons x tl1)
          in
        Return (t, back1))
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::list_nth_mut_loop]:
    Source: 'src/loops.rs', lines 88:0-88:71 *)
Definition list_nth_mut_loop
  (T : Type) (n : nat) (ls : List_t T) (i : u32) :
  result (T * (T -> result (List_t T)))
  :=
  list_nth_mut_loop_loop T n ls i
.

(** [loops::list_nth_shared_loop]: loop 0:
    Source: 'src/loops.rs', lines 101:0-111:1 *)
Fixpoint list_nth_shared_loop_loop
  (T : Type) (n : nat) (ls : List_t T) (i : u32) : result T :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | List_Cons x tl =>
      if i s= 0%u32
      then Return x
      else (i1 <- u32_sub i 1%u32; list_nth_shared_loop_loop T n1 tl i1)
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::list_nth_shared_loop]:
    Source: 'src/loops.rs', lines 101:0-101:66 *)
Definition list_nth_shared_loop
  (T : Type) (n : nat) (ls : List_t T) (i : u32) : result T :=
  list_nth_shared_loop_loop T n ls i
.

(** [loops::get_elem_mut]: loop 0:
    Source: 'src/loops.rs', lines 113:0-127:1 *)
Fixpoint get_elem_mut_loop
  (n : nat) (x : usize) (ls : List_t usize) :
  result (usize * (usize -> result (List_t usize)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | List_Cons y tl =>
      if y s= x
      then
        let back := fun (ret : usize) => Return (List_Cons ret tl) in
        Return (y, back)
      else (
        p <- get_elem_mut_loop n1 x tl;
        let (i, back) := p in
        let back1 :=
          fun (ret : usize) => tl1 <- back ret; Return (List_Cons y tl1) in
        Return (i, back1))
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::get_elem_mut]:
    Source: 'src/loops.rs', lines 113:0-113:73 *)
Definition get_elem_mut
  (n : nat) (slots : alloc_vec_Vec (List_t usize)) (x : usize) :
  result (usize * (usize -> result (alloc_vec_Vec (List_t usize))))
  :=
  p <-
    alloc_vec_Vec_index_mut (List_t usize) usize
      (core_slice_index_SliceIndexUsizeSliceTInst (List_t usize)) slots 0%usize;
  let (ls, index_mut_back) := p in
  p1 <- get_elem_mut_loop n x ls;
  let (i, back) := p1 in
  let back1 := fun (ret : usize) => l <- back ret; index_mut_back l in
  Return (i, back1)
.

(** [loops::get_elem_shared]: loop 0:
    Source: 'src/loops.rs', lines 129:0-143:1 *)
Fixpoint get_elem_shared_loop
  (n : nat) (x : usize) (ls : List_t usize) : result usize :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | List_Cons y tl =>
      if y s= x then Return y else get_elem_shared_loop n1 x tl
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::get_elem_shared]:
    Source: 'src/loops.rs', lines 129:0-129:68 *)
Definition get_elem_shared
  (n : nat) (slots : alloc_vec_Vec (List_t usize)) (x : usize) :
  result usize
  :=
  ls <-
    alloc_vec_Vec_index (List_t usize) usize
      (core_slice_index_SliceIndexUsizeSliceTInst (List_t usize)) slots 0%usize;
  get_elem_shared_loop n x ls
.

(** [loops::id_mut]:
    Source: 'src/loops.rs', lines 145:0-145:50 *)
Definition id_mut
  (T : Type) (ls : List_t T) :
  result ((List_t T) * (List_t T -> result (List_t T)))
  :=
  Return (ls, Return)
.

(** [loops::id_shared]:
    Source: 'src/loops.rs', lines 149:0-149:45 *)
Definition id_shared (T : Type) (ls : List_t T) : result (List_t T) :=
  Return ls
.

(** [loops::list_nth_mut_loop_with_id]: loop 0:
    Source: 'src/loops.rs', lines 154:0-165:1 *)
Fixpoint list_nth_mut_loop_with_id_loop
  (T : Type) (n : nat) (i : u32) (ls : List_t T) :
  result (T * (T -> result (List_t T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | List_Cons x tl =>
      if i s= 0%u32
      then
        let back := fun (ret : T) => Return (List_Cons ret tl) in
        Return (x, back)
      else (
        i1 <- u32_sub i 1%u32;
        p <- list_nth_mut_loop_with_id_loop T n1 i1 tl;
        let (t, back) := p in
        let back1 := fun (ret : T) => tl1 <- back ret; Return (List_Cons x tl1)
          in
        Return (t, back1))
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::list_nth_mut_loop_with_id]:
    Source: 'src/loops.rs', lines 154:0-154:75 *)
Definition list_nth_mut_loop_with_id
  (T : Type) (n : nat) (ls : List_t T) (i : u32) :
  result (T * (T -> result (List_t T)))
  :=
  p <- id_mut T ls;
  let (ls1, id_mut_back) := p in
  p1 <- list_nth_mut_loop_with_id_loop T n i ls1;
  let (t, back) := p1 in
  let back1 := fun (ret : T) => l <- back ret; id_mut_back l in
  Return (t, back1)
.

(** [loops::list_nth_shared_loop_with_id]: loop 0:
    Source: 'src/loops.rs', lines 168:0-179:1 *)
Fixpoint list_nth_shared_loop_with_id_loop
  (T : Type) (n : nat) (i : u32) (ls : List_t T) : result T :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls with
    | List_Cons x tl =>
      if i s= 0%u32
      then Return x
      else (
        i1 <- u32_sub i 1%u32; list_nth_shared_loop_with_id_loop T n1 i1 tl)
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::list_nth_shared_loop_with_id]:
    Source: 'src/loops.rs', lines 168:0-168:70 *)
Definition list_nth_shared_loop_with_id
  (T : Type) (n : nat) (ls : List_t T) (i : u32) : result T :=
  ls1 <- id_shared T ls; list_nth_shared_loop_with_id_loop T n i ls1
.

(** [loops::list_nth_mut_loop_pair]: loop 0:
    Source: 'src/loops.rs', lines 184:0-205:1 *)
Fixpoint list_nth_mut_loop_pair_loop
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)) * (T -> result (List_t T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls0 with
    | List_Cons x0 tl0 =>
      match ls1 with
      | List_Cons x1 tl1 =>
        if i s= 0%u32
        then
          let back'a := fun (ret : T) => Return (List_Cons ret tl0) in
          let back'b := fun (ret : T) => Return (List_Cons ret tl1) in
          Return ((x0, x1), back'a, back'b)
        else (
          i1 <- u32_sub i 1%u32;
          t <- list_nth_mut_loop_pair_loop T n1 tl0 tl1 i1;
          let '(p, back'a, back'b) := t in
          let back'a1 :=
            fun (ret : T) => tl01 <- back'a ret; Return (List_Cons x0 tl01) in
          let back'b1 :=
            fun (ret : T) => tl11 <- back'b ret; Return (List_Cons x1 tl11) in
          Return (p, back'a1, back'b1))
      | List_Nil => Fail_ Failure
      end
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::list_nth_mut_loop_pair]:
    Source: 'src/loops.rs', lines 184:0-188:27 *)
Definition list_nth_mut_loop_pair
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)) * (T -> result (List_t T)))
  :=
  list_nth_mut_loop_pair_loop T n ls0 ls1 i
.

(** [loops::list_nth_shared_loop_pair]: loop 0:
    Source: 'src/loops.rs', lines 208:0-229:1 *)
Fixpoint list_nth_shared_loop_pair_loop
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result (T * T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls0 with
    | List_Cons x0 tl0 =>
      match ls1 with
      | List_Cons x1 tl1 =>
        if i s= 0%u32
        then Return (x0, x1)
        else (
          i1 <- u32_sub i 1%u32; list_nth_shared_loop_pair_loop T n1 tl0 tl1 i1)
      | List_Nil => Fail_ Failure
      end
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::list_nth_shared_loop_pair]:
    Source: 'src/loops.rs', lines 208:0-212:19 *)
Definition list_nth_shared_loop_pair
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result (T * T)
  :=
  list_nth_shared_loop_pair_loop T n ls0 ls1 i
.

(** [loops::list_nth_mut_loop_pair_merge]: loop 0:
    Source: 'src/loops.rs', lines 233:0-248:1 *)
Fixpoint list_nth_mut_loop_pair_merge_loop
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * ((T * T) -> result ((List_t T) * (List_t T))))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls0 with
    | List_Cons x0 tl0 =>
      match ls1 with
      | List_Cons x1 tl1 =>
        if i s= 0%u32
        then
          let back :=
            fun (ret : (T * T)) =>
              let (t, t1) := ret in Return (List_Cons t tl0, List_Cons t1 tl1)
            in
          Return ((x0, x1), back)
        else (
          i1 <- u32_sub i 1%u32;
          p <- list_nth_mut_loop_pair_merge_loop T n1 tl0 tl1 i1;
          let (p1, back) := p in
          let back1 :=
            fun (ret : (T * T)) =>
              p2 <- back ret;
              let (tl01, tl11) := p2 in
              Return (List_Cons x0 tl01, List_Cons x1 tl11) in
          Return (p1, back1))
      | List_Nil => Fail_ Failure
      end
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::list_nth_mut_loop_pair_merge]:
    Source: 'src/loops.rs', lines 233:0-237:27 *)
Definition list_nth_mut_loop_pair_merge
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * ((T * T) -> result ((List_t T) * (List_t T))))
  :=
  list_nth_mut_loop_pair_merge_loop T n ls0 ls1 i
.

(** [loops::list_nth_shared_loop_pair_merge]: loop 0:
    Source: 'src/loops.rs', lines 251:0-266:1 *)
Fixpoint list_nth_shared_loop_pair_merge_loop
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result (T * T)
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls0 with
    | List_Cons x0 tl0 =>
      match ls1 with
      | List_Cons x1 tl1 =>
        if i s= 0%u32
        then Return (x0, x1)
        else (
          i1 <- u32_sub i 1%u32;
          list_nth_shared_loop_pair_merge_loop T n1 tl0 tl1 i1)
      | List_Nil => Fail_ Failure
      end
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::list_nth_shared_loop_pair_merge]:
    Source: 'src/loops.rs', lines 251:0-255:19 *)
Definition list_nth_shared_loop_pair_merge
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result (T * T)
  :=
  list_nth_shared_loop_pair_merge_loop T n ls0 ls1 i
.

(** [loops::list_nth_mut_shared_loop_pair]: loop 0:
    Source: 'src/loops.rs', lines 269:0-284:1 *)
Fixpoint list_nth_mut_shared_loop_pair_loop
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls0 with
    | List_Cons x0 tl0 =>
      match ls1 with
      | List_Cons x1 tl1 =>
        if i s= 0%u32
        then
          let back := fun (ret : T) => Return (List_Cons ret tl0) in
          Return ((x0, x1), back)
        else (
          i1 <- u32_sub i 1%u32;
          p <- list_nth_mut_shared_loop_pair_loop T n1 tl0 tl1 i1;
          let (p1, back) := p in
          let back1 :=
            fun (ret : T) => tl01 <- back ret; Return (List_Cons x0 tl01) in
          Return (p1, back1))
      | List_Nil => Fail_ Failure
      end
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::list_nth_mut_shared_loop_pair]:
    Source: 'src/loops.rs', lines 269:0-273:23 *)
Definition list_nth_mut_shared_loop_pair
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  list_nth_mut_shared_loop_pair_loop T n ls0 ls1 i
.

(** [loops::list_nth_mut_shared_loop_pair_merge]: loop 0:
    Source: 'src/loops.rs', lines 288:0-303:1 *)
Fixpoint list_nth_mut_shared_loop_pair_merge_loop
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls0 with
    | List_Cons x0 tl0 =>
      match ls1 with
      | List_Cons x1 tl1 =>
        if i s= 0%u32
        then
          let back := fun (ret : T) => Return (List_Cons ret tl0) in
          Return ((x0, x1), back)
        else (
          i1 <- u32_sub i 1%u32;
          p <- list_nth_mut_shared_loop_pair_merge_loop T n1 tl0 tl1 i1;
          let (p1, back) := p in
          let back1 :=
            fun (ret : T) => tl01 <- back ret; Return (List_Cons x0 tl01) in
          Return (p1, back1))
      | List_Nil => Fail_ Failure
      end
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::list_nth_mut_shared_loop_pair_merge]:
    Source: 'src/loops.rs', lines 288:0-292:23 *)
Definition list_nth_mut_shared_loop_pair_merge
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  list_nth_mut_shared_loop_pair_merge_loop T n ls0 ls1 i
.

(** [loops::list_nth_shared_mut_loop_pair]: loop 0:
    Source: 'src/loops.rs', lines 307:0-322:1 *)
Fixpoint list_nth_shared_mut_loop_pair_loop
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls0 with
    | List_Cons x0 tl0 =>
      match ls1 with
      | List_Cons x1 tl1 =>
        if i s= 0%u32
        then
          let back := fun (ret : T) => Return (List_Cons ret tl1) in
          Return ((x0, x1), back)
        else (
          i1 <- u32_sub i 1%u32;
          p <- list_nth_shared_mut_loop_pair_loop T n1 tl0 tl1 i1;
          let (p1, back) := p in
          let back1 :=
            fun (ret : T) => tl11 <- back ret; Return (List_Cons x1 tl11) in
          Return (p1, back1))
      | List_Nil => Fail_ Failure
      end
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::list_nth_shared_mut_loop_pair]:
    Source: 'src/loops.rs', lines 307:0-311:23 *)
Definition list_nth_shared_mut_loop_pair
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  list_nth_shared_mut_loop_pair_loop T n ls0 ls1 i
.

(** [loops::list_nth_shared_mut_loop_pair_merge]: loop 0:
    Source: 'src/loops.rs', lines 326:0-341:1 *)
Fixpoint list_nth_shared_mut_loop_pair_merge_loop
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match ls0 with
    | List_Cons x0 tl0 =>
      match ls1 with
      | List_Cons x1 tl1 =>
        if i s= 0%u32
        then
          let back := fun (ret : T) => Return (List_Cons ret tl1) in
          Return ((x0, x1), back)
        else (
          i1 <- u32_sub i 1%u32;
          p <- list_nth_shared_mut_loop_pair_merge_loop T n1 tl0 tl1 i1;
          let (p1, back) := p in
          let back1 :=
            fun (ret : T) => tl11 <- back ret; Return (List_Cons x1 tl11) in
          Return (p1, back1))
      | List_Nil => Fail_ Failure
      end
    | List_Nil => Fail_ Failure
    end
  end
.

(** [loops::list_nth_shared_mut_loop_pair_merge]:
    Source: 'src/loops.rs', lines 326:0-330:23 *)
Definition list_nth_shared_mut_loop_pair_merge
  (T : Type) (n : nat) (ls0 : List_t T) (ls1 : List_t T) (i : u32) :
  result ((T * T) * (T -> result (List_t T)))
  :=
  list_nth_shared_mut_loop_pair_merge_loop T n ls0 ls1 i
.

(** [loops::ignore_input_mut_borrow]: loop 0:
    Source: 'src/loops.rs', lines 345:0-349:1 *)
Fixpoint ignore_input_mut_borrow_loop (n : nat) (i : u32) : result unit :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if i s> 0%u32
    then (i1 <- u32_sub i 1%u32; ignore_input_mut_borrow_loop n1 i1)
    else Return tt
  end
.

(** [loops::ignore_input_mut_borrow]:
    Source: 'src/loops.rs', lines 345:0-345:56 *)
Definition ignore_input_mut_borrow
  (n : nat) (_a : u32) (i : u32) : result u32 :=
  _ <- ignore_input_mut_borrow_loop n i; Return _a
.

(** [loops::incr_ignore_input_mut_borrow]: loop 0:
    Source: 'src/loops.rs', lines 353:0-358:1 *)
Fixpoint incr_ignore_input_mut_borrow_loop (n : nat) (i : u32) : result unit :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if i s> 0%u32
    then (i1 <- u32_sub i 1%u32; incr_ignore_input_mut_borrow_loop n1 i1)
    else Return tt
  end
.

(** [loops::incr_ignore_input_mut_borrow]:
    Source: 'src/loops.rs', lines 353:0-353:60 *)
Definition incr_ignore_input_mut_borrow
  (n : nat) (a : u32) (i : u32) : result u32 :=
  a1 <- u32_add a 1%u32; _ <- incr_ignore_input_mut_borrow_loop n i; Return a1
.

(** [loops::ignore_input_shared_borrow]: loop 0:
    Source: 'src/loops.rs', lines 362:0-366:1 *)
Fixpoint ignore_input_shared_borrow_loop (n : nat) (i : u32) : result unit :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if i s> 0%u32
    then (i1 <- u32_sub i 1%u32; ignore_input_shared_borrow_loop n1 i1)
    else Return tt
  end
.

(** [loops::ignore_input_shared_borrow]:
    Source: 'src/loops.rs', lines 362:0-362:59 *)
Definition ignore_input_shared_borrow
  (n : nat) (_a : u32) (i : u32) : result u32 :=
  _ <- ignore_input_shared_borrow_loop n i; Return _a
.

End Loops.
