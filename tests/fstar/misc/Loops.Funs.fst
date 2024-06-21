(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [loops]: function definitions *)
module Loops.Funs
open Primitives
include Loops.Types
include Loops.Clauses

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [loops::sum]: loop 0:
    Source: 'tests/src/loops.rs', lines 10:4-18:1 *)
let rec sum_loop
  (max : u32) (i : u32) (s : u32) :
  Tot (result u32) (decreases (sum_loop_decreases max i s))
  =
  if i < max
  then let* s1 = u32_add s i in let* i1 = u32_add i 1 in sum_loop max i1 s1
  else u32_mul s 2

(** [loops::sum]:
    Source: 'tests/src/loops.rs', lines 8:0-8:27 *)
let sum (max : u32) : result u32 =
  sum_loop max 0 0

(** [loops::sum_with_mut_borrows]: loop 0:
    Source: 'tests/src/loops.rs', lines 25:4-35:1 *)
let rec sum_with_mut_borrows_loop
  (max : u32) (i : u32) (s : u32) :
  Tot (result u32) (decreases (sum_with_mut_borrows_loop_decreases max i s))
  =
  if i < max
  then
    let* ms = u32_add s i in
    let* mi = u32_add i 1 in
    sum_with_mut_borrows_loop max mi ms
  else u32_mul s 2

(** [loops::sum_with_mut_borrows]:
    Source: 'tests/src/loops.rs', lines 23:0-23:44 *)
let sum_with_mut_borrows (max : u32) : result u32 =
  sum_with_mut_borrows_loop max 0 0

(** [loops::sum_with_shared_borrows]: loop 0:
    Source: 'tests/src/loops.rs', lines 40:4-52:1 *)
let rec sum_with_shared_borrows_loop
  (max : u32) (i : u32) (s : u32) :
  Tot (result u32) (decreases (sum_with_shared_borrows_loop_decreases max i s))
  =
  if i < max
  then
    let* i1 = u32_add i 1 in
    let* s1 = u32_add s i1 in
    sum_with_shared_borrows_loop max i1 s1
  else u32_mul s 2

(** [loops::sum_with_shared_borrows]:
    Source: 'tests/src/loops.rs', lines 38:0-38:47 *)
let sum_with_shared_borrows (max : u32) : result u32 =
  sum_with_shared_borrows_loop max 0 0

(** [loops::sum_array]: loop 0:
    Source: 'tests/src/loops.rs', lines 56:4-62:1 *)
let rec sum_array_loop
  (n : usize) (a : array u32 n) (i : usize) (s : u32) :
  Tot (result u32) (decreases (sum_array_loop_decreases n a i s))
  =
  if i < n
  then
    let* i1 = array_index_usize u32 n a i in
    let* s1 = u32_add s i1 in
    let* i2 = usize_add i 1 in
    sum_array_loop n a i2 s1
  else Ok s

(** [loops::sum_array]:
    Source: 'tests/src/loops.rs', lines 54:0-54:52 *)
let sum_array (n : usize) (a : array u32 n) : result u32 =
  sum_array_loop n a 0 0

(** [loops::clear]: loop 0:
    Source: 'tests/src/loops.rs', lines 67:4-72:1 *)
let rec clear_loop
  (v : alloc_vec_Vec u32) (i : usize) :
  Tot (result (alloc_vec_Vec u32)) (decreases (clear_loop_decreases v i))
  =
  let i1 = alloc_vec_Vec_len u32 v in
  if i < i1
  then
    let* (_, index_mut_back) =
      alloc_vec_Vec_index_mut u32 usize
        (core_slice_index_SliceIndexUsizeSliceTInst u32) v i in
    let* i2 = usize_add i 1 in
    let* v1 = index_mut_back 0 in
    clear_loop v1 i2
  else Ok v

(** [loops::clear]:
    Source: 'tests/src/loops.rs', lines 66:0-66:30 *)
let clear (v : alloc_vec_Vec u32) : result (alloc_vec_Vec u32) =
  clear_loop v 0

(** [loops::list_mem]: loop 0:
    Source: 'tests/src/loops.rs', lines 80:0-89:1 *)
let rec list_mem_loop
  (x : u32) (ls : list_t u32) :
  Tot (result bool) (decreases (list_mem_loop_decreases x ls))
  =
  begin match ls with
  | List_Cons y tl -> if y = x then Ok true else list_mem_loop x tl
  | List_Nil -> Ok false
  end

(** [loops::list_mem]:
    Source: 'tests/src/loops.rs', lines 80:0-80:52 *)
let list_mem (x : u32) (ls : list_t u32) : result bool =
  list_mem_loop x ls

(** [loops::list_nth_mut_loop]: loop 0:
    Source: 'tests/src/loops.rs', lines 92:0-102:1 *)
let rec list_nth_mut_loop_loop
  (t : Type0) (ls : list_t t) (i : u32) :
  Tot (result (t & (t -> result (list_t t))))
  (decreases (list_nth_mut_loop_loop_decreases t ls i))
  =
  begin match ls with
  | List_Cons x tl ->
    if i = 0
    then let back = fun ret -> Ok (List_Cons ret tl) in Ok (x, back)
    else
      let* i1 = u32_sub i 1 in
      let* (x1, back) = list_nth_mut_loop_loop t tl i1 in
      let back1 = fun ret -> let* tl1 = back ret in Ok (List_Cons x tl1) in
      Ok (x1, back1)
  | List_Nil -> Fail Failure
  end

(** [loops::list_nth_mut_loop]:
    Source: 'tests/src/loops.rs', lines 92:0-92:71 *)
let list_nth_mut_loop
  (t : Type0) (ls : list_t t) (i : u32) :
  result (t & (t -> result (list_t t)))
  =
  list_nth_mut_loop_loop t ls i

(** [loops::list_nth_shared_loop]: loop 0:
    Source: 'tests/src/loops.rs', lines 105:0-115:1 *)
let rec list_nth_shared_loop_loop
  (t : Type0) (ls : list_t t) (i : u32) :
  Tot (result t) (decreases (list_nth_shared_loop_loop_decreases t ls i))
  =
  begin match ls with
  | List_Cons x tl ->
    if i = 0
    then Ok x
    else let* i1 = u32_sub i 1 in list_nth_shared_loop_loop t tl i1
  | List_Nil -> Fail Failure
  end

(** [loops::list_nth_shared_loop]:
    Source: 'tests/src/loops.rs', lines 105:0-105:66 *)
let list_nth_shared_loop (t : Type0) (ls : list_t t) (i : u32) : result t =
  list_nth_shared_loop_loop t ls i

(** [loops::get_elem_mut]: loop 0:
    Source: 'tests/src/loops.rs', lines 117:0-131:1 *)
let rec get_elem_mut_loop
  (x : usize) (ls : list_t usize) :
  Tot (result (usize & (usize -> result (list_t usize))))
  (decreases (get_elem_mut_loop_decreases x ls))
  =
  begin match ls with
  | List_Cons y tl ->
    if y = x
    then let back = fun ret -> Ok (List_Cons ret tl) in Ok (y, back)
    else
      let* (i, back) = get_elem_mut_loop x tl in
      let back1 = fun ret -> let* tl1 = back ret in Ok (List_Cons y tl1) in
      Ok (i, back1)
  | List_Nil -> Fail Failure
  end

(** [loops::get_elem_mut]:
    Source: 'tests/src/loops.rs', lines 117:0-117:73 *)
let get_elem_mut
  (slots : alloc_vec_Vec (list_t usize)) (x : usize) :
  result (usize & (usize -> result (alloc_vec_Vec (list_t usize))))
  =
  let* (ls, index_mut_back) =
    alloc_vec_Vec_index_mut (list_t usize) usize
      (core_slice_index_SliceIndexUsizeSliceTInst (list_t usize)) slots 0 in
  let* (i, back) = get_elem_mut_loop x ls in
  let back1 = fun ret -> let* l = back ret in index_mut_back l in
  Ok (i, back1)

(** [loops::get_elem_shared]: loop 0:
    Source: 'tests/src/loops.rs', lines 133:0-147:1 *)
let rec get_elem_shared_loop
  (x : usize) (ls : list_t usize) :
  Tot (result usize) (decreases (get_elem_shared_loop_decreases x ls))
  =
  begin match ls with
  | List_Cons y tl -> if y = x then Ok y else get_elem_shared_loop x tl
  | List_Nil -> Fail Failure
  end

(** [loops::get_elem_shared]:
    Source: 'tests/src/loops.rs', lines 133:0-133:68 *)
let get_elem_shared
  (slots : alloc_vec_Vec (list_t usize)) (x : usize) : result usize =
  let* ls =
    alloc_vec_Vec_index (list_t usize) usize
      (core_slice_index_SliceIndexUsizeSliceTInst (list_t usize)) slots 0 in
  get_elem_shared_loop x ls

(** [loops::id_mut]:
    Source: 'tests/src/loops.rs', lines 149:0-149:50 *)
let id_mut
  (t : Type0) (ls : list_t t) :
  result ((list_t t) & (list_t t -> result (list_t t)))
  =
  Ok (ls, Ok)

(** [loops::id_shared]:
    Source: 'tests/src/loops.rs', lines 153:0-153:45 *)
let id_shared (t : Type0) (ls : list_t t) : result (list_t t) =
  Ok ls

(** [loops::list_nth_mut_loop_with_id]: loop 0:
    Source: 'tests/src/loops.rs', lines 158:0-169:1 *)
let rec list_nth_mut_loop_with_id_loop
  (t : Type0) (i : u32) (ls : list_t t) :
  Tot (result (t & (t -> result (list_t t))))
  (decreases (list_nth_mut_loop_with_id_loop_decreases t i ls))
  =
  begin match ls with
  | List_Cons x tl ->
    if i = 0
    then let back = fun ret -> Ok (List_Cons ret tl) in Ok (x, back)
    else
      let* i1 = u32_sub i 1 in
      let* (x1, back) = list_nth_mut_loop_with_id_loop t i1 tl in
      let back1 = fun ret -> let* tl1 = back ret in Ok (List_Cons x tl1) in
      Ok (x1, back1)
  | List_Nil -> Fail Failure
  end

(** [loops::list_nth_mut_loop_with_id]:
    Source: 'tests/src/loops.rs', lines 158:0-158:75 *)
let list_nth_mut_loop_with_id
  (t : Type0) (ls : list_t t) (i : u32) :
  result (t & (t -> result (list_t t)))
  =
  let* (ls1, id_mut_back) = id_mut t ls in
  let* (x, back) = list_nth_mut_loop_with_id_loop t i ls1 in
  let back1 = fun ret -> let* l = back ret in id_mut_back l in
  Ok (x, back1)

(** [loops::list_nth_shared_loop_with_id]: loop 0:
    Source: 'tests/src/loops.rs', lines 172:0-183:1 *)
let rec list_nth_shared_loop_with_id_loop
  (t : Type0) (i : u32) (ls : list_t t) :
  Tot (result t)
  (decreases (list_nth_shared_loop_with_id_loop_decreases t i ls))
  =
  begin match ls with
  | List_Cons x tl ->
    if i = 0
    then Ok x
    else let* i1 = u32_sub i 1 in list_nth_shared_loop_with_id_loop t i1 tl
  | List_Nil -> Fail Failure
  end

(** [loops::list_nth_shared_loop_with_id]:
    Source: 'tests/src/loops.rs', lines 172:0-172:70 *)
let list_nth_shared_loop_with_id
  (t : Type0) (ls : list_t t) (i : u32) : result t =
  let* ls1 = id_shared t ls in list_nth_shared_loop_with_id_loop t i ls1

(** [loops::list_nth_mut_loop_pair]: loop 0:
    Source: 'tests/src/loops.rs', lines 188:0-209:1 *)
let rec list_nth_mut_loop_pair_loop
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  Tot (result ((t & t) & (t -> result (list_t t)) & (t -> result (list_t t))))
  (decreases (list_nth_mut_loop_pair_loop_decreases t ls0 ls1 i))
  =
  begin match ls0 with
  | List_Cons x0 tl0 ->
    begin match ls1 with
    | List_Cons x1 tl1 ->
      if i = 0
      then
        let back'a = fun ret -> Ok (List_Cons ret tl0) in
        let back'b = fun ret -> Ok (List_Cons ret tl1) in
        Ok ((x0, x1), back'a, back'b)
      else
        let* i1 = u32_sub i 1 in
        let* (p, back'a, back'b) = list_nth_mut_loop_pair_loop t tl0 tl1 i1 in
        let back'a1 =
          fun ret -> let* tl01 = back'a ret in Ok (List_Cons x0 tl01) in
        let back'b1 =
          fun ret -> let* tl11 = back'b ret in Ok (List_Cons x1 tl11) in
        Ok (p, back'a1, back'b1)
    | List_Nil -> Fail Failure
    end
  | List_Nil -> Fail Failure
  end

(** [loops::list_nth_mut_loop_pair]:
    Source: 'tests/src/loops.rs', lines 188:0-192:27 *)
let list_nth_mut_loop_pair
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  result ((t & t) & (t -> result (list_t t)) & (t -> result (list_t t)))
  =
  list_nth_mut_loop_pair_loop t ls0 ls1 i

(** [loops::list_nth_shared_loop_pair]: loop 0:
    Source: 'tests/src/loops.rs', lines 212:0-233:1 *)
let rec list_nth_shared_loop_pair_loop
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  Tot (result (t & t))
  (decreases (list_nth_shared_loop_pair_loop_decreases t ls0 ls1 i))
  =
  begin match ls0 with
  | List_Cons x0 tl0 ->
    begin match ls1 with
    | List_Cons x1 tl1 ->
      if i = 0
      then Ok (x0, x1)
      else let* i1 = u32_sub i 1 in list_nth_shared_loop_pair_loop t tl0 tl1 i1
    | List_Nil -> Fail Failure
    end
  | List_Nil -> Fail Failure
  end

(** [loops::list_nth_shared_loop_pair]:
    Source: 'tests/src/loops.rs', lines 212:0-216:19 *)
let list_nth_shared_loop_pair
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) : result (t & t) =
  list_nth_shared_loop_pair_loop t ls0 ls1 i

(** [loops::list_nth_mut_loop_pair_merge]: loop 0:
    Source: 'tests/src/loops.rs', lines 237:0-252:1 *)
let rec list_nth_mut_loop_pair_merge_loop
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  Tot (result ((t & t) & ((t & t) -> result ((list_t t) & (list_t t)))))
  (decreases (list_nth_mut_loop_pair_merge_loop_decreases t ls0 ls1 i))
  =
  begin match ls0 with
  | List_Cons x0 tl0 ->
    begin match ls1 with
    | List_Cons x1 tl1 ->
      if i = 0
      then
        let back =
          fun ret ->
            let (x, x2) = ret in Ok (List_Cons x tl0, List_Cons x2 tl1) in
        Ok ((x0, x1), back)
      else
        let* i1 = u32_sub i 1 in
        let* (p, back) = list_nth_mut_loop_pair_merge_loop t tl0 tl1 i1 in
        let back1 =
          fun ret ->
            let* (tl01, tl11) = back ret in
            Ok (List_Cons x0 tl01, List_Cons x1 tl11) in
        Ok (p, back1)
    | List_Nil -> Fail Failure
    end
  | List_Nil -> Fail Failure
  end

(** [loops::list_nth_mut_loop_pair_merge]:
    Source: 'tests/src/loops.rs', lines 237:0-241:27 *)
let list_nth_mut_loop_pair_merge
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  result ((t & t) & ((t & t) -> result ((list_t t) & (list_t t))))
  =
  list_nth_mut_loop_pair_merge_loop t ls0 ls1 i

(** [loops::list_nth_shared_loop_pair_merge]: loop 0:
    Source: 'tests/src/loops.rs', lines 255:0-270:1 *)
let rec list_nth_shared_loop_pair_merge_loop
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  Tot (result (t & t))
  (decreases (list_nth_shared_loop_pair_merge_loop_decreases t ls0 ls1 i))
  =
  begin match ls0 with
  | List_Cons x0 tl0 ->
    begin match ls1 with
    | List_Cons x1 tl1 ->
      if i = 0
      then Ok (x0, x1)
      else
        let* i1 = u32_sub i 1 in
        list_nth_shared_loop_pair_merge_loop t tl0 tl1 i1
    | List_Nil -> Fail Failure
    end
  | List_Nil -> Fail Failure
  end

(** [loops::list_nth_shared_loop_pair_merge]:
    Source: 'tests/src/loops.rs', lines 255:0-259:19 *)
let list_nth_shared_loop_pair_merge
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) : result (t & t) =
  list_nth_shared_loop_pair_merge_loop t ls0 ls1 i

(** [loops::list_nth_mut_shared_loop_pair]: loop 0:
    Source: 'tests/src/loops.rs', lines 273:0-288:1 *)
let rec list_nth_mut_shared_loop_pair_loop
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  Tot (result ((t & t) & (t -> result (list_t t))))
  (decreases (list_nth_mut_shared_loop_pair_loop_decreases t ls0 ls1 i))
  =
  begin match ls0 with
  | List_Cons x0 tl0 ->
    begin match ls1 with
    | List_Cons x1 tl1 ->
      if i = 0
      then let back = fun ret -> Ok (List_Cons ret tl0) in Ok ((x0, x1), back)
      else
        let* i1 = u32_sub i 1 in
        let* (p, back) = list_nth_mut_shared_loop_pair_loop t tl0 tl1 i1 in
        let back1 = fun ret -> let* tl01 = back ret in Ok (List_Cons x0 tl01)
          in
        Ok (p, back1)
    | List_Nil -> Fail Failure
    end
  | List_Nil -> Fail Failure
  end

(** [loops::list_nth_mut_shared_loop_pair]:
    Source: 'tests/src/loops.rs', lines 273:0-277:23 *)
let list_nth_mut_shared_loop_pair
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  result ((t & t) & (t -> result (list_t t)))
  =
  list_nth_mut_shared_loop_pair_loop t ls0 ls1 i

(** [loops::list_nth_mut_shared_loop_pair_merge]: loop 0:
    Source: 'tests/src/loops.rs', lines 292:0-307:1 *)
let rec list_nth_mut_shared_loop_pair_merge_loop
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  Tot (result ((t & t) & (t -> result (list_t t))))
  (decreases (list_nth_mut_shared_loop_pair_merge_loop_decreases t ls0 ls1 i))
  =
  begin match ls0 with
  | List_Cons x0 tl0 ->
    begin match ls1 with
    | List_Cons x1 tl1 ->
      if i = 0
      then let back = fun ret -> Ok (List_Cons ret tl0) in Ok ((x0, x1), back)
      else
        let* i1 = u32_sub i 1 in
        let* (p, back) = list_nth_mut_shared_loop_pair_merge_loop t tl0 tl1 i1
          in
        let back1 = fun ret -> let* tl01 = back ret in Ok (List_Cons x0 tl01)
          in
        Ok (p, back1)
    | List_Nil -> Fail Failure
    end
  | List_Nil -> Fail Failure
  end

(** [loops::list_nth_mut_shared_loop_pair_merge]:
    Source: 'tests/src/loops.rs', lines 292:0-296:23 *)
let list_nth_mut_shared_loop_pair_merge
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  result ((t & t) & (t -> result (list_t t)))
  =
  list_nth_mut_shared_loop_pair_merge_loop t ls0 ls1 i

(** [loops::list_nth_shared_mut_loop_pair]: loop 0:
    Source: 'tests/src/loops.rs', lines 311:0-326:1 *)
let rec list_nth_shared_mut_loop_pair_loop
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  Tot (result ((t & t) & (t -> result (list_t t))))
  (decreases (list_nth_shared_mut_loop_pair_loop_decreases t ls0 ls1 i))
  =
  begin match ls0 with
  | List_Cons x0 tl0 ->
    begin match ls1 with
    | List_Cons x1 tl1 ->
      if i = 0
      then let back = fun ret -> Ok (List_Cons ret tl1) in Ok ((x0, x1), back)
      else
        let* i1 = u32_sub i 1 in
        let* (p, back) = list_nth_shared_mut_loop_pair_loop t tl0 tl1 i1 in
        let back1 = fun ret -> let* tl11 = back ret in Ok (List_Cons x1 tl11)
          in
        Ok (p, back1)
    | List_Nil -> Fail Failure
    end
  | List_Nil -> Fail Failure
  end

(** [loops::list_nth_shared_mut_loop_pair]:
    Source: 'tests/src/loops.rs', lines 311:0-315:23 *)
let list_nth_shared_mut_loop_pair
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  result ((t & t) & (t -> result (list_t t)))
  =
  list_nth_shared_mut_loop_pair_loop t ls0 ls1 i

(** [loops::list_nth_shared_mut_loop_pair_merge]: loop 0:
    Source: 'tests/src/loops.rs', lines 330:0-345:1 *)
let rec list_nth_shared_mut_loop_pair_merge_loop
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  Tot (result ((t & t) & (t -> result (list_t t))))
  (decreases (list_nth_shared_mut_loop_pair_merge_loop_decreases t ls0 ls1 i))
  =
  begin match ls0 with
  | List_Cons x0 tl0 ->
    begin match ls1 with
    | List_Cons x1 tl1 ->
      if i = 0
      then let back = fun ret -> Ok (List_Cons ret tl1) in Ok ((x0, x1), back)
      else
        let* i1 = u32_sub i 1 in
        let* (p, back) = list_nth_shared_mut_loop_pair_merge_loop t tl0 tl1 i1
          in
        let back1 = fun ret -> let* tl11 = back ret in Ok (List_Cons x1 tl11)
          in
        Ok (p, back1)
    | List_Nil -> Fail Failure
    end
  | List_Nil -> Fail Failure
  end

(** [loops::list_nth_shared_mut_loop_pair_merge]:
    Source: 'tests/src/loops.rs', lines 330:0-334:23 *)
let list_nth_shared_mut_loop_pair_merge
  (t : Type0) (ls0 : list_t t) (ls1 : list_t t) (i : u32) :
  result ((t & t) & (t -> result (list_t t)))
  =
  list_nth_shared_mut_loop_pair_merge_loop t ls0 ls1 i

(** [loops::ignore_input_mut_borrow]: loop 0:
    Source: 'tests/src/loops.rs', lines 349:0-353:1 *)
let rec ignore_input_mut_borrow_loop
  (i : u32) :
  Tot (result unit) (decreases (ignore_input_mut_borrow_loop_decreases i))
  =
  if i > 0
  then let* i1 = u32_sub i 1 in ignore_input_mut_borrow_loop i1
  else Ok ()

(** [loops::ignore_input_mut_borrow]:
    Source: 'tests/src/loops.rs', lines 349:0-349:56 *)
let ignore_input_mut_borrow (_a : u32) (i : u32) : result u32 =
  let* _ = ignore_input_mut_borrow_loop i in Ok _a

(** [loops::incr_ignore_input_mut_borrow]: loop 0:
    Source: 'tests/src/loops.rs', lines 357:0-362:1 *)
let rec incr_ignore_input_mut_borrow_loop
  (i : u32) :
  Tot (result unit) (decreases (incr_ignore_input_mut_borrow_loop_decreases i))
  =
  if i > 0
  then let* i1 = u32_sub i 1 in incr_ignore_input_mut_borrow_loop i1
  else Ok ()

(** [loops::incr_ignore_input_mut_borrow]:
    Source: 'tests/src/loops.rs', lines 357:0-357:60 *)
let incr_ignore_input_mut_borrow (a : u32) (i : u32) : result u32 =
  let* a1 = u32_add a 1 in
  let* _ = incr_ignore_input_mut_borrow_loop i in
  Ok a1

(** [loops::ignore_input_shared_borrow]: loop 0:
    Source: 'tests/src/loops.rs', lines 366:0-370:1 *)
let rec ignore_input_shared_borrow_loop
  (i : u32) :
  Tot (result unit) (decreases (ignore_input_shared_borrow_loop_decreases i))
  =
  if i > 0
  then let* i1 = u32_sub i 1 in ignore_input_shared_borrow_loop i1
  else Ok ()

(** [loops::ignore_input_shared_borrow]:
    Source: 'tests/src/loops.rs', lines 366:0-366:59 *)
let ignore_input_shared_borrow (_a : u32) (i : u32) : result u32 =
  let* _ = ignore_input_shared_borrow_loop i in Ok _a

