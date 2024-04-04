(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [paper] *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Module Paper.

(** [paper::ref_incr]:
    Source: 'src/paper.rs', lines 4:0-4:28 *)
Definition ref_incr (x : i32) : result i32 :=
  i32_add x 1%i32.

(** [paper::test_incr]:
    Source: 'src/paper.rs', lines 8:0-8:18 *)
Definition test_incr : result unit :=
  x <- ref_incr 0%i32; if negb (x s= 1%i32) then Fail_ Failure else Return tt
.

(** Unit test for [paper::test_incr] *)
Check (test_incr )%return.

(** [paper::choose]:
    Source: 'src/paper.rs', lines 15:0-15:70 *)
Definition choose
  (T : Type) (b : bool) (x : T) (y : T) : result (T * (T -> result (T * T))) :=
  if b
  then let back := fun (ret : T) => Return (ret, y) in Return (x, back)
  else let back := fun (ret : T) => Return (x, ret) in Return (y, back)
.

(** [paper::test_choose]:
    Source: 'src/paper.rs', lines 23:0-23:20 *)
Definition test_choose : result unit :=
  p <- choose i32 true 0%i32 0%i32;
  let (z, choose_back) := p in
  z1 <- i32_add z 1%i32;
  if negb (z1 s= 1%i32)
  then Fail_ Failure
  else (
    p1 <- choose_back z1;
    let (x, y) := p1 in
    if negb (x s= 1%i32)
    then Fail_ Failure
    else if negb (y s= 0%i32) then Fail_ Failure else Return tt)
.

(** Unit test for [paper::test_choose] *)
Check (test_choose )%return.

(** [paper::List]
    Source: 'src/paper.rs', lines 35:0-35:16 *)
Inductive List_t (T : Type) :=
| List_Cons : T -> List_t T -> List_t T
| List_Nil : List_t T
.

Arguments List_Cons { _ }.
Arguments List_Nil { _ }.

(** [paper::list_nth_mut]:
    Source: 'src/paper.rs', lines 42:0-42:67 *)
Fixpoint list_nth_mut
  (T : Type) (l : List_t T) (i : u32) :
  result (T * (T -> result (List_t T)))
  :=
  match l with
  | List_Cons x tl =>
    if i s= 0%u32
    then
      let back := fun (ret : T) => Return (List_Cons ret tl) in
      Return (x, back)
    else (
      i1 <- u32_sub i 1%u32;
      p <- list_nth_mut T tl i1;
      let (t, list_nth_mut_back) := p in
      let back :=
        fun (ret : T) => tl1 <- list_nth_mut_back ret; Return (List_Cons x tl1)
        in
      Return (t, back))
  | List_Nil => Fail_ Failure
  end
.

(** [paper::sum]:
    Source: 'src/paper.rs', lines 57:0-57:32 *)
Fixpoint sum (l : List_t i32) : result i32 :=
  match l with
  | List_Cons x tl => i <- sum tl; i32_add x i
  | List_Nil => Return 0%i32
  end
.

(** [paper::test_nth]:
    Source: 'src/paper.rs', lines 68:0-68:17 *)
Definition test_nth : result unit :=
  let l := List_Cons 3%i32 List_Nil in
  let l1 := List_Cons 2%i32 l in
  p <- list_nth_mut i32 (List_Cons 1%i32 l1) 2%u32;
  let (x, list_nth_mut_back) := p in
  x1 <- i32_add x 1%i32;
  l2 <- list_nth_mut_back x1;
  i <- sum l2;
  if negb (i s= 7%i32) then Fail_ Failure else Return tt
.

(** Unit test for [paper::test_nth] *)
Check (test_nth )%return.

(** [paper::call_choose]:
    Source: 'src/paper.rs', lines 76:0-76:44 *)
Definition call_choose (p : (u32 * u32)) : result u32 :=
  let (px, py) := p in
  p1 <- choose u32 true px py;
  let (pz, choose_back) := p1 in
  pz1 <- u32_add pz 1%u32;
  p2 <- choose_back pz1;
  let (px1, _) := p2 in
  Return px1
.

End Paper.
