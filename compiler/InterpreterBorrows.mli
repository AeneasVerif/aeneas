module T = Types
module V = Values
module C = Contexts
module Subst = Substitute
module L = Logging
module S = SynthesizeSymbolic
open Cps
open InterpreterProjectors

(** When copying values, we duplicate the shared borrows. This is tantamount to
    reborrowing the shared value. The [reborrow_shared original_id new_bid ctx]
    applies this change to an environment [ctx] by inserting a new borrow id in
    the set of borrows tracked by a shared value, referenced by the
    [original_bid] argument.  *)
val reborrow_shared : V.BorrowId.id -> V.BorrowId.id -> C.eval_ctx -> C.eval_ctx

(** End a borrow identified by its id, while preserving the invariants.

    If the borrow is inside another borrow/an abstraction or contains loans,
    [end_borrow] will end those borrows/abstractions/loans first.
  *)
val end_borrow : C.config -> V.BorrowId.id -> cm_fun

(** End a set of borrows identified by their ids, while preserving the invariants. *)
val end_borrows : C.config -> V.BorrowId.Set.t -> cm_fun

(** End an abstraction while preserving the invariants. *)
val end_abstraction : C.config -> V.AbstractionId.id -> cm_fun

(** End a set of abstractions while preserving the invariants. *)
val end_abstractions : C.config -> V.AbstractionId.Set.t -> cm_fun

(** End a borrow and return the resulting environment, ignoring synthesis *)
val end_borrow_no_synth : C.config -> V.BorrowId.id -> C.eval_ctx -> C.eval_ctx

(** End an abstraction and return the resulting environment, ignoring synthesis *)
val end_abstraction_no_synth :
  C.config -> V.AbstractionId.id -> C.eval_ctx -> C.eval_ctx

(** Promote a reserved mut borrow to a mut borrow, while preserving the invariants.

    Reserved borrows are special mutable borrows which are created as shared borrows
    then promoted to mutable borrows upon their first use.

    This function replaces the reserved borrow with a mutable borrow, then replaces
    the corresponding shared loan with a mutable loan (after having ended the
    other shared borrows which point to this loan).
 *)
val promote_reserved_mut_borrow : C.config -> V.BorrowId.id -> cm_fun

(** Transform an abstraction to an abstraction where the values are not
    structured.

    For instance:
    {[
      abs {
        (mut_borrow l0, mut_borrow l1, _)
      }

          ~~>

      abs {
        mut_borrow l0
        mut_borrow l1
      }
    ]}

    Rem.: we do this to simplify the merging of abstractions. We can do this
    because for now, we don't support nested borrows.

    Paramters:
    - [abs_kind]
    - [can_end]
    - [ctx]
    - [abs]
 *)
val destructure_abs : V.abs_kind -> bool -> C.eval_ctx -> V.abs -> V.abs

(** Return [true] if the values in an abstraction are destructured.

    We simply destructure it and check that it gives the identity.
 *)
val abs_is_destructured : C.eval_ctx -> V.abs -> bool

(** Turn a value into a abstractions.

    We are conservative, and don't group borrows/loans into the same abstraction
    unless necessary.

    For instance:
    {[
      _ -> (mut_borrow l1 (mut_loan l2), mut_borrow l3)

      ~~>

      abs'0 { mut_borrow l1, mut_loan l2 }
      abs'1 { mut_borrow l3 }
    ]}

    Parameters:
    - [abs_kind]
    - [can_end]
    - [ctx]
    - [v]
 *)
val convert_value_to_abstractions :
  V.abs_kind -> bool -> C.eval_ctx -> V.typed_value -> V.abs list

(** Merge two abstractions together.

    Merging two abstractions together implies removing the loans/borrows
    which appear in one and whose associated loans/borrows appear in the
    other. For instance:
    {[
      abs'0 { mut_borrow l0, mut_loan l1 }
      abs'1 { mut_borrow l1, mut_borrow l2 }

          ~~>

      abs'01 { mut_borrow l0, mut_borrow l2 }
    ]}

    Parameters:
    - [kind]
    - [can_end]
    - [ctx]
    - [abs0]
    - [abs1]
 *)
val merge_abstractions :
  V.abs_kind -> bool -> C.eval_ctx -> V.abs -> V.abs -> V.abs
