(* This file defines the basic blocks to implement the semantics of borrows.
 * Note that those functions are not only used in InterpreterBorrows, but
 * also in Invariants or InterpreterProjectors *)

module T = Types
module V = Values
module C = Contexts
module Subst = Substitute
module L = Logging
open Utils
open InterpreterUtils

(** TODO: cleanup this a bit, once we have a better understanding about
    what we need.
    TODO: I'm not sure in which file this should be moved... *)
type exploration_kind = {
  enter_shared_loans : bool;
  enter_mut_borrows : bool;
  enter_abs : bool;
      (** Note that if we allow to enter abs, we don't check whether we enter
          mutable/shared loans or borrows: there are no use cases requiring
          a finer control. *)
}
(** This record controls how some generic helper lookup/update
    functions behave, by restraining the kind of therms they can enter.
*)

let ek_all : exploration_kind =
  { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }

(** The following type identifies the relative position of expressions (in
    particular borrows) in other expressions.
    
    For instance, it is used to control [end_borrow]: we usually only allow
    to end "outer" borrows, unless we perform a drop.
*)
type inner_outer = Inner | Outer

type borrow_ids = Borrows of V.BorrowId.Set.t | Borrow of V.BorrowId.id

exception FoundBorrowIds of borrow_ids

type outer_borrows_or_abs =
  | OuterBorrows of borrow_ids
  | OuterAbs of V.AbstractionId.id

let update_if_none opt x = match opt with None -> Some x | _ -> opt

exception FoundOuter of outer_borrows_or_abs
(** Utility exception *)

(** Lookup a loan content.

    The loan is referred to by a borrow id.

    TODO: group abs_or_var_id and g_loan_content. 
 *)
let lookup_loan_opt (ek : exploration_kind) (l : V.BorrowId.id)
    (ctx : C.eval_ctx) : (abs_or_var_id * g_loan_content) option =
  (* We store here whether we are inside an abstraction or a value - note that we
   * could also track that with the environment, it would probably be more idiomatic
   * and cleaner *)
  let abs_or_var : abs_or_var_id option ref = ref None in

  let obj =
    object
      inherit [_] C.iter_eval_ctx as super

      method! visit_borrow_content env bc =
        match bc with
        | V.SharedBorrow bid ->
            (* Nothing specific to do *)
            super#visit_SharedBorrow env bid
        | V.InactivatedMutBorrow bid ->
            (* Nothing specific to do *)
            super#visit_InactivatedMutBorrow env bid
        | V.MutBorrow (bid, mv) ->
            (* Control the dive *)
            if ek.enter_mut_borrows then super#visit_MutBorrow env bid mv
            else ()

      method! visit_loan_content env lc =
        match lc with
        | V.SharedLoan (bids, sv) ->
            (* Check if this is the loan we are looking for, and control the dive *)
            if V.BorrowId.Set.mem l bids then
              raise (FoundGLoanContent (Concrete lc))
            else if ek.enter_shared_loans then
              super#visit_SharedLoan env bids sv
            else ()
        | V.MutLoan bid ->
            (* Check if this is the loan we are looking for *)
            if bid = l then raise (FoundGLoanContent (Concrete lc))
            else super#visit_MutLoan env bid
      (** We reimplement [visit_Loan] (rather than the more precise functions
          [visit_SharedLoan], etc.) on purpose: as we have an exhaustive match
          below, we are more resilient to definition updates (the compiler
          is our friend).
      *)

      method! visit_aloan_content env lc =
        match lc with
        | V.AMutLoan (bid, av) ->
            if bid = l then raise (FoundGLoanContent (Abstract lc))
            else super#visit_AMutLoan env bid av
        | V.ASharedLoan (bids, v, av) ->
            if V.BorrowId.Set.mem l bids then
              raise (FoundGLoanContent (Abstract lc))
            else super#visit_ASharedLoan env bids v av
        | V.AEndedMutLoan { given_back; child } ->
            super#visit_AEndedMutLoan env given_back child
        | V.AEndedSharedLoan (v, av) -> super#visit_AEndedSharedLoan env v av
        | V.AIgnoredMutLoan (bid, av) -> super#visit_AIgnoredMutLoan env bid av
        | V.AEndedIgnoredMutLoan { given_back; child } ->
            super#visit_AEndedIgnoredMutLoan env given_back child
        | V.AIgnoredSharedLoan av -> super#visit_AIgnoredSharedLoan env av
      (** Note that we don't control diving inside the abstractions: if we
          allow to dive inside abstractions, we allow to go anywhere
          (because there are no use cases requiring finer control) *)

      method! visit_Var env bv v =
        assert (Option.is_none !abs_or_var);
        abs_or_var := Some (VarId bv.C.index);
        super#visit_Var env bv v;
        abs_or_var := None

      method! visit_Abs env abs =
        assert (Option.is_none !abs_or_var);
        if ek.enter_abs then (
          abs_or_var := Some (AbsId abs.V.abs_id);
          super#visit_Abs env abs)
        else ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_eval_ctx () ctx;
    None
  with FoundGLoanContent lc -> (
    match !abs_or_var with
    | Some abs_or_var -> Some (abs_or_var, lc)
    | None -> failwith "Inconsistent state")

(** Lookup a loan content.

    The loan is referred to by a borrow id.
    Raises an exception if no loan was found.
 *)
let lookup_loan (ek : exploration_kind) (l : V.BorrowId.id) (ctx : C.eval_ctx) :
    abs_or_var_id * g_loan_content =
  match lookup_loan_opt ek l ctx with
  | None -> failwith "Unreachable"
  | Some res -> res

(** Update a loan content.

    The loan is referred to by a borrow id.

    This is a helper function: it might break invariants.
 *)
let update_loan (ek : exploration_kind) (l : V.BorrowId.id)
    (nlc : V.loan_content) (ctx : C.eval_ctx) : C.eval_ctx =
  (* We use a reference to check that we update exactly one loan: when updating
   * inside values, we check we don't update more than one loan. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let update () : V.loan_content =
    assert (not !r);
    r := true;
    nlc
  in

  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_borrow_content env bc =
        match bc with
        | V.SharedBorrow _ | V.InactivatedMutBorrow _ ->
            (* Nothing specific to do *)
            super#visit_borrow_content env bc
        | V.MutBorrow (bid, mv) ->
            (* Control the dive into mutable borrows *)
            if ek.enter_mut_borrows then super#visit_MutBorrow env bid mv
            else V.MutBorrow (bid, mv)

      method! visit_loan_content env lc =
        match lc with
        | V.SharedLoan (bids, sv) ->
            (* Shared loan: check if this is the loan we are looking for, and
               control the dive. *)
            if V.BorrowId.Set.mem l bids then update ()
            else if ek.enter_shared_loans then
              super#visit_SharedLoan env bids sv
            else V.SharedLoan (bids, sv)
        | V.MutLoan bid ->
            (* Mut loan: checks if this is the loan we are looking for *)
            if bid = l then update () else super#visit_MutLoan env bid
      (** We reimplement [visit_loan_content] (rather than one of the sub-
          functions) on purpose: exhaustive matches are good for maintenance *)

      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else abs
      (** Note that once inside the abstractions, we don't control diving
          (there are no use cases requiring finer control).
          Also, as we give back a [loan_content] (and not an [aloan_content])
          we don't need to do reimplement the visit functions for the values
          inside the abstractions (rk.: there may be "concrete" values inside
          abstractions, so there is a utility in diving inside). *)
    end
  in

  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that we updated at least one loan *)
  assert !r;
  ctx

(** Update a abstraction loan content.

    The loan is referred to by a borrow id.

    This is a helper function: it might break invariants.
 *)
let update_aloan (ek : exploration_kind) (l : V.BorrowId.id)
    (nlc : V.aloan_content) (ctx : C.eval_ctx) : C.eval_ctx =
  (* We use a reference to check that we update exactly one loan: when updating
   * inside values, we check we don't update more than one loan. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let update () : V.aloan_content =
    assert (not !r);
    r := true;
    nlc
  in

  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_aloan_content env lc =
        match lc with
        | V.AMutLoan (bid, av) ->
            if bid = l then update () else super#visit_AMutLoan env bid av
        | V.ASharedLoan (bids, v, av) ->
            if V.BorrowId.Set.mem l bids then update ()
            else super#visit_ASharedLoan env bids v av
        | V.AEndedMutLoan { given_back; child } ->
            super#visit_AEndedMutLoan env given_back child
        | V.AEndedSharedLoan (v, av) -> super#visit_AEndedSharedLoan env v av
        | V.AIgnoredMutLoan (bid, av) -> super#visit_AIgnoredMutLoan env bid av
        | V.AEndedIgnoredMutLoan { given_back; child } ->
            super#visit_AEndedIgnoredMutLoan env given_back child
        | V.AIgnoredSharedLoan av -> super#visit_AIgnoredSharedLoan env av

      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else abs
      (** Note that once inside the abstractions, we don't control diving
          (there are no use cases requiring finer control). *)
    end
  in

  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that we updated at least one loan *)
  assert !r;
  ctx

(** Lookup a borrow content from a borrow id. *)
let lookup_borrow_opt (ek : exploration_kind) (l : V.BorrowId.id)
    (ctx : C.eval_ctx) : g_borrow_content option =
  let obj =
    object
      inherit [_] C.iter_eval_ctx as super

      method! visit_borrow_content env bc =
        match bc with
        | V.MutBorrow (bid, mv) ->
            (* Check the borrow id and control the dive *)
            if bid = l then raise (FoundGBorrowContent (Concrete bc))
            else if ek.enter_mut_borrows then super#visit_MutBorrow env bid mv
            else ()
        | V.SharedBorrow bid ->
            (* Check the borrow id *)
            if bid = l then raise (FoundGBorrowContent (Concrete bc)) else ()
        | V.InactivatedMutBorrow bid ->
            (* Check the borrow id *)
            if bid = l then raise (FoundGBorrowContent (Concrete bc)) else ()

      method! visit_loan_content env lc =
        match lc with
        | V.MutLoan bid ->
            (* Nothing special to do *) super#visit_MutLoan env bid
        | V.SharedLoan (bids, sv) ->
            (* Control the dive *)
            if ek.enter_shared_loans then super#visit_SharedLoan env bids sv
            else ()

      method! visit_aborrow_content env bc =
        match bc with
        | V.AMutBorrow (bid, av) ->
            if bid = l then raise (FoundGBorrowContent (Abstract bc))
            else super#visit_AMutBorrow env bid av
        | V.ASharedBorrow bid ->
            if bid = l then raise (FoundGBorrowContent (Abstract bc))
            else super#visit_ASharedBorrow env bid
        | V.AIgnoredMutBorrow av -> super#visit_AIgnoredMutBorrow env av
        | V.AProjSharedBorrow asb ->
            if borrow_in_asb l asb then
              raise (FoundGBorrowContent (Abstract bc))
            else ()

      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_eval_ctx () ctx;
    None
  with FoundGBorrowContent lc -> Some lc

(** Lookup a borrow content from a borrow id.

    Raise an exception if no loan was found
*)
let lookup_borrow (ek : exploration_kind) (l : V.BorrowId.id) (ctx : C.eval_ctx)
    : g_borrow_content =
  match lookup_borrow_opt ek l ctx with
  | None -> failwith "Unreachable"
  | Some lc -> lc

(** Update a borrow content.

    The borrow is referred to by a borrow id.

    This is a helper function: it might break invariants.   
 *)
let update_borrow (ek : exploration_kind) (l : V.BorrowId.id)
    (nbc : V.borrow_content) (ctx : C.eval_ctx) : C.eval_ctx =
  (* We use a reference to check that we update exactly one borrow: when updating
   * inside values, we check we don't update more than one borrow. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let update () : V.borrow_content =
    assert (not !r);
    r := true;
    nbc
  in

  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_borrow_content env bc =
        match bc with
        | V.MutBorrow (bid, mv) ->
            (* Check the id and control dive *)
            if bid = l then update ()
            else if ek.enter_mut_borrows then super#visit_MutBorrow env bid mv
            else V.MutBorrow (bid, mv)
        | V.SharedBorrow bid ->
            (* Check the id *)
            if bid = l then update () else super#visit_SharedBorrow env bid
        | V.InactivatedMutBorrow bid ->
            (* Check the id *)
            if bid = l then update ()
            else super#visit_InactivatedMutBorrow env bid

      method! visit_loan_content env lc =
        match lc with
        | V.SharedLoan (bids, sv) ->
            (* Control the dive *)
            if ek.enter_shared_loans then super#visit_SharedLoan env bids sv
            else V.SharedLoan (bids, sv)
        | V.MutLoan bid ->
            (* Nothing specific to do *)
            super#visit_MutLoan env bid

      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else abs
    end
  in

  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that we updated at least one borrow *)
  assert !r;
  ctx

(** Update an abstraction borrow content.

    The borrow is referred to by a borrow id.

    This is a helper function: it might break invariants.     
 *)
let update_aborrow (ek : exploration_kind) (l : V.BorrowId.id) (nv : V.avalue)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* We use a reference to check that we update exactly one borrow: when updating
   * inside values, we check we don't update more than one borrow. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let update () : V.avalue =
    assert (not !r);
    r := true;
    nv
  in

  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_ABorrow env bc =
        match bc with
        | V.AMutBorrow (bid, av) ->
            if bid = l then update ()
            else V.ABorrow (super#visit_AMutBorrow env bid av)
        | V.ASharedBorrow bid ->
            if bid = l then update ()
            else V.ABorrow (super#visit_ASharedBorrow env bid)
        | V.AIgnoredMutBorrow av ->
            V.ABorrow (super#visit_AIgnoredMutBorrow env av)
        | V.AProjSharedBorrow asb ->
            if borrow_in_asb l asb then update ()
            else V.ABorrow (super#visit_AProjSharedBorrow env asb)

      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else abs
    end
  in

  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that we updated at least one borrow *)
  assert !r;
  ctx

(** Auxiliary function: see its usage in [end_borrow_get_borrow_in_value] *)
let update_outer_borrows (io : inner_outer)
    (outer : V.AbstractionId.id option * borrow_ids option) (x : borrow_ids) :
    V.AbstractionId.id option * borrow_ids option =
  match io with
  | Inner ->
      (* If we can end inner borrows, we don't keep track of the outer borrows *)
      outer
  | Outer ->
      let abs, opt = outer in
      (abs, update_if_none opt x)

(** Return the first loan we find in a value *)
let get_first_loan_in_value (v : V.typed_value) : V.loan_content option =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_loan_content _ lc = raise (FoundLoanContent lc)
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    None
  with FoundLoanContent lc -> Some lc
