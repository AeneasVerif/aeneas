(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [polonius_list] *)
Require Import Primitives.
Import Primitives.
Require Import Coq.ZArith.ZArith.
Require Import List.
Import ListNotations.
Local Open Scope Primitives_scope.
Module PoloniusList.

(** [polonius_list::List]
    Source: 'src/polonius_list.rs', lines 3:0-3:16 *)
Inductive List_t (T : Type) :=
| List_Cons : T -> List_t T -> List_t T
| List_Nil : List_t T
.

Arguments List_Cons { _ }.
Arguments List_Nil { _ }.

(** [polonius_list::get_list_at_x]:
    Source: 'src/polonius_list.rs', lines 13:0-13:76 *)
Fixpoint get_list_at_x
  (ls : List_t u32) (x : u32) :
  result ((List_t u32) * (List_t u32 -> result (List_t u32)))
  :=
  match ls with
  | List_Cons hd tl =>
    if hd s= x
    then Ok (List_Cons hd tl, Ok)
    else (
      p <- get_list_at_x tl x;
      let (l, get_list_at_x_back) := p in
      let back :=
        fun (ret : List_t u32) =>
          tl1 <- get_list_at_x_back ret; Ok (List_Cons hd tl1) in
      Ok (l, back))
  | List_Nil => Ok (List_Nil, Ok)
  end
.

End PoloniusList.
