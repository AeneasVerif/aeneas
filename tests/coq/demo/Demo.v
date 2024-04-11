(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [demo] *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Module Demo.

(** [demo::choose]:
    Source: 'src/demo.rs', lines 5:0-5:70 *)
Definition choose
  (T : Type) (b : bool) (x : T) (y : T) : result (T * (T -> result (T * T))) :=
  if b
  then let back := fun (ret : T) => Ok (ret, y) in Ok (x, back)
  else let back := fun (ret : T) => Ok (x, ret) in Ok (y, back)
.

(** [demo::mul2_add1]:
    Source: 'src/demo.rs', lines 13:0-13:31 *)
Definition mul2_add1 (x : u32) : result u32 :=
  i <- u32_add x x; u32_add i 1%u32
.

(** [demo::use_mul2_add1]:
    Source: 'src/demo.rs', lines 17:0-17:43 *)
Definition use_mul2_add1 (x : u32) (y : u32) : result u32 :=
  i <- mul2_add1 x; u32_add i y
.

(** [demo::incr]:
    Source: 'src/demo.rs', lines 21:0-21:31 *)
Definition incr (x : u32) : result u32 :=
  u32_add x 1%u32.

(** [demo::use_incr]:
    Source: 'src/demo.rs', lines 25:0-25:17 *)
Definition use_incr : result unit :=
  x <- incr 0%u32; x1 <- incr x; _ <- incr x1; Ok tt
.

(** [demo::CList]
    Source: 'src/demo.rs', lines 34:0-34:17 *)
Inductive CList_t (T : Type) :=
| CList_CCons : T -> CList_t T -> CList_t T
| CList_CNil : CList_t T
.

Arguments CList_CCons { _ }.
Arguments CList_CNil { _ }.

(** [demo::list_nth]:
    Source: 'src/demo.rs', lines 39:0-39:56 *)
Fixpoint list_nth (T : Type) (n : nat) (l : CList_t T) (i : u32) : result T :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match l with
    | CList_CCons x tl =>
      if i s= 0%u32 then Ok x else (i1 <- u32_sub i 1%u32; list_nth T n1 tl i1)
    | CList_CNil => Fail_ Failure
    end
  end
.

(** [demo::list_nth_mut]:
    Source: 'src/demo.rs', lines 54:0-54:68 *)
Fixpoint list_nth_mut
  (T : Type) (n : nat) (l : CList_t T) (i : u32) :
  result (T * (T -> result (CList_t T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match l with
    | CList_CCons x tl =>
      if i s= 0%u32
      then let back := fun (ret : T) => Ok (CList_CCons ret tl) in Ok (x, back)
      else (
        i1 <- u32_sub i 1%u32;
        p <- list_nth_mut T n1 tl i1;
        let (t, list_nth_mut_back) := p in
        let back :=
          fun (ret : T) => tl1 <- list_nth_mut_back ret; Ok (CList_CCons x tl1)
          in
        Ok (t, back))
    | CList_CNil => Fail_ Failure
    end
  end
.

(** [demo::list_nth_mut1]: loop 0:
    Source: 'src/demo.rs', lines 69:0-78:1 *)
Fixpoint list_nth_mut1_loop
  (T : Type) (n : nat) (l : CList_t T) (i : u32) :
  result (T * (T -> result (CList_t T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match l with
    | CList_CCons x tl =>
      if i s= 0%u32
      then let back := fun (ret : T) => Ok (CList_CCons ret tl) in Ok (x, back)
      else (
        i1 <- u32_sub i 1%u32;
        p <- list_nth_mut1_loop T n1 tl i1;
        let (t, back) := p in
        let back1 := fun (ret : T) => tl1 <- back ret; Ok (CList_CCons x tl1)
          in
        Ok (t, back1))
    | CList_CNil => Fail_ Failure
    end
  end
.

(** [demo::list_nth_mut1]:
    Source: 'src/demo.rs', lines 69:0-69:77 *)
Definition list_nth_mut1
  (T : Type) (n : nat) (l : CList_t T) (i : u32) :
  result (T * (T -> result (CList_t T)))
  :=
  list_nth_mut1_loop T n l i
.

(** [demo::i32_id]:
    Source: 'src/demo.rs', lines 80:0-80:28 *)
Fixpoint i32_id (n : nat) (i : i32) : result i32 :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    if i s= 0%i32
    then Ok 0%i32
    else (i1 <- i32_sub i 1%i32; i2 <- i32_id n1 i1; i32_add i2 1%i32)
  end
.

(** [demo::list_tail]:
    Source: 'src/demo.rs', lines 88:0-88:64 *)
Fixpoint list_tail
  (T : Type) (n : nat) (l : CList_t T) :
  result ((CList_t T) * (CList_t T -> result (CList_t T)))
  :=
  match n with
  | O => Fail_ OutOfFuel
  | S n1 =>
    match l with
    | CList_CCons t tl =>
      p <- list_tail T n1 tl;
      let (c, list_tail_back) := p in
      let back :=
        fun (ret : CList_t T) =>
          tl1 <- list_tail_back ret; Ok (CList_CCons t tl1) in
      Ok (c, back)
    | CList_CNil => Ok (CList_CNil, Ok)
    end
  end
.

(** Trait declaration: [demo::Counter]
    Source: 'src/demo.rs', lines 97:0-97:17 *)
Record Counter_t (Self : Type) := mkCounter_t {
  Counter_t_incr : Self -> result (usize * Self);
}.

Arguments mkCounter_t { _ }.
Arguments Counter_t_incr { _ }.

(** [demo::{(demo::Counter for usize)}::incr]:
    Source: 'src/demo.rs', lines 102:4-102:31 *)
Definition counterUsize_incr (self : usize) : result (usize * usize) :=
  self1 <- usize_add self 1%usize; Ok (self, self1)
.

(** Trait implementation: [demo::{(demo::Counter for usize)}]
    Source: 'src/demo.rs', lines 101:0-101:22 *)
Definition CounterUsize : Counter_t usize := {|
  Counter_t_incr := counterUsize_incr;
|}.

(** [demo::use_counter]:
    Source: 'src/demo.rs', lines 109:0-109:59 *)
Definition use_counter
  (T : Type) (counterInst : Counter_t T) (cnt : T) : result (usize * T) :=
  counterInst.(Counter_t_incr) cnt
.

End Demo.
