(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [paper] *)
module Paper
open Primitives

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [paper::ref_incr]:
    Source: 'src/paper.rs', lines 4:0-4:28 *)
let ref_incr (x : i32) : result i32 =
  i32_add x 1

(** [paper::test_incr]:
    Source: 'src/paper.rs', lines 8:0-8:18 *)
let test_incr : result unit =
  let* x = ref_incr 0 in if not (x = 1) then Fail Failure else Ok ()

(** Unit test for [paper::test_incr] *)
let _ = assert_norm (test_incr = Ok ())

(** [paper::choose]:
    Source: 'src/paper.rs', lines 15:0-15:70 *)
let choose
  (t : Type0) (b : bool) (x : t) (y : t) : result (t & (t -> result (t & t))) =
  if b
  then let back_'a = fun ret -> Ok (ret, y) in Ok (x, back_'a)
  else let back_'a = fun ret -> Ok (x, ret) in Ok (y, back_'a)

(** [paper::test_choose]:
    Source: 'src/paper.rs', lines 23:0-23:20 *)
let test_choose : result unit =
  let* (z, choose_back) = choose i32 true 0 0 in
  let* z1 = i32_add z 1 in
  if not (z1 = 1)
  then Fail Failure
  else
    let* (x, y) = choose_back z1 in
    if not (x = 1)
    then Fail Failure
    else if not (y = 0) then Fail Failure else Ok ()

(** Unit test for [paper::test_choose] *)
let _ = assert_norm (test_choose = Ok ())

(** [paper::List]
    Source: 'src/paper.rs', lines 35:0-35:16 *)
type list_t (t : Type0) =
| List_Cons : t -> list_t t -> list_t t
| List_Nil : list_t t

(** [paper::list_nth_mut]:
    Source: 'src/paper.rs', lines 42:0-42:67 *)
let rec list_nth_mut
  (t : Type0) (l : list_t t) (i : u32) :
  result (t & (t -> result (list_t t)))
  =
  begin match l with
  | List_Cons x tl ->
    if i = 0
    then let back_'a = fun ret -> Ok (List_Cons ret tl) in Ok (x, back_'a)
    else
      let* i1 = u32_sub i 1 in
      let* (x1, list_nth_mut_back) = list_nth_mut t tl i1 in
      let back_'a =
        fun ret -> let* tl1 = list_nth_mut_back ret in Ok (List_Cons x tl1) in
      Ok (x1, back_'a)
  | List_Nil -> Fail Failure
  end

(** [paper::sum]:
    Source: 'src/paper.rs', lines 57:0-57:32 *)
let rec sum (l : list_t i32) : result i32 =
  begin match l with
  | List_Cons x tl -> let* i = sum tl in i32_add x i
  | List_Nil -> Ok 0
  end

(** [paper::test_nth]:
    Source: 'src/paper.rs', lines 68:0-68:17 *)
let test_nth : result unit =
  let l = List_Cons 3 List_Nil in
  let l1 = List_Cons 2 l in
  let* (x, list_nth_mut_back) = list_nth_mut i32 (List_Cons 1 l1) 2 in
  let* x1 = i32_add x 1 in
  let* l2 = list_nth_mut_back x1 in
  let* i = sum l2 in
  if not (i = 7) then Fail Failure else Ok ()

(** Unit test for [paper::test_nth] *)
let _ = assert_norm (test_nth = Ok ())

(** [paper::call_choose]:
    Source: 'src/paper.rs', lines 76:0-76:44 *)
let call_choose (p : (u32 & u32)) : result u32 =
  let (px, py) = p in
  let* (pz, choose_back) = choose u32 true px py in
  let* pz1 = u32_add pz 1 in
  let* (px1, _) = choose_back pz1 in
  Ok px1

