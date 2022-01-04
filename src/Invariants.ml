(* The following module defines functions to check that some invariants
 * are always maintained by evaluation contexts *)

module T = Types
module V = Values
open Scalars
module E = Expressions
open Errors
module C = Contexts
module Subst = Substitute
module A = CfimAst
module L = Logging
open TypesUtils
open ValuesUtils

(** Check that:
    - loans and borrows are correctly related
    - borrows/loans can't contain ⊥ or inactivated mut borrows
    - shared loans can't contain mutable loans
    - TODO: a two-phase borrow can't point to a value inside an abstraction
 *)
let check_borrows_invariant (ctx : C.eval_ctx) : unit = ()

let check_no_bottom_below_ref_invariant (ctx : C.eval_ctx) : unit = ()

let check_typing_invariant (ctx : C.eval_ctx) : unit = ()

let check_invariants (ctx : C.eval_ctx) : unit =
  check_borrows_invariant ctx;
  check_no_bottom_below_ref_invariant ctx;
  check_typing_invariant ctx
