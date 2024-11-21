(** THIS FILE WAS AUTOMATICALLY GENERATED BY AENEAS *)
(** [adt_borrows] *)
module AdtBorrows
open Primitives

#set-options "--z3rlimit 50 --fuel 1 --ifuel 1"

(** [adt_borrows::SharedWrapper]
    Source: 'tests/src/adt-borrows.rs', lines 4:0-4:35 *)
type sharedWrapper_t (t : Type0) = t

(** [adt_borrows::{adt_borrows::SharedWrapper<'a, T>}::create]:
    Source: 'tests/src/adt-borrows.rs', lines 7:4-9:5 *)
let sharedWrapper_create (#t : Type0) (x : t) : result (sharedWrapper_t t) =
  Ok x

(** [adt_borrows::{adt_borrows::SharedWrapper<'a, T>}::unwrap]:
    Source: 'tests/src/adt-borrows.rs', lines 11:4-13:5 *)
let sharedWrapper_unwrap (#t : Type0) (self : sharedWrapper_t t) : result t =
  Ok self
