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

(** Activate a reserved borrow into a mutable borrow, while preserving the invariants. *)
val activate_inactivated_mut_borrow : C.config -> V.BorrowId.id -> cm_fun
