(** This file defines the basic blocks to implement the semantics of borrows.
    Note that those functions are not only used in InterpreterBorrows, but also
    in Invariants or InterpreterProjectors *)

open Types
open Values
open Contexts
open Utils
open TypesUtils
open InterpreterUtils
open Errors

(** The local logger *)
let log = Logging.borrows_log

(** TODO: cleanup this a bit, once we have a better understanding about what we
    need. TODO: I'm not sure in which file this should be moved... *)
type exploration_kind = {
  enter_shared_loans : bool;
  enter_mut_borrows : bool;
  enter_abs : bool;
      (** Note that if we allow to enter abs, we don't check whether we enter
          mutable/shared loans or borrows: there are no use cases requiring a
          finer control. *)
}
(** This record controls how some generic helper lookup/update functions behave,
    by restraining the kind of therms they can enter. *)

let ek_all : exploration_kind =
  { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }

type borrow_ids = Borrows of BorrowId.Set.t | Borrow of BorrowId.id
[@@deriving show]

type borrow_ids_or_proj_symbolic_value =
  | BorrowIds of borrow_ids
  | SymbolicValue of symbolic_value_id * rty
[@@deriving show]

exception FoundBorrowIds of borrow_ids

type priority_borrows_or_abs =
  | OuterBorrows of borrow_ids
  | OuterAbs of AbstractionId.id
  | InnerLoans of borrow_ids
[@@deriving show]

let update_if_none opt x =
  match opt with
  | None -> Some x
  | _ -> opt

(** Utility exception *)
exception FoundPriority of priority_borrows_or_abs

type loan_or_borrow_content =
  | LoanContent of loan_content
  | BorrowContent of borrow_content
[@@deriving show]

type borrow_or_abs_id = BorrowId of BorrowId.id | AbsId of AbstractionId.id
type borrow_or_abs_ids = borrow_or_abs_id list

let borrow_or_abs_id_to_string (id : borrow_or_abs_id) : string =
  match id with
  | AbsId id -> "abs@" ^ AbstractionId.to_string id
  | BorrowId id -> "l@" ^ BorrowId.to_string id

let borrow_or_abs_ids_chain_to_string (ids : borrow_or_abs_ids) : string =
  let ids = List.rev ids in
  let ids = List.map borrow_or_abs_id_to_string ids in
  String.concat " -> " ids

(** Add a borrow or abs id to a chain of ids, while checking that we don't loop
*)
let add_borrow_or_abs_id_to_chain (span : Meta.span) (msg : string)
    (id : borrow_or_abs_id) (ids : borrow_or_abs_ids) : borrow_or_abs_ids =
  if List.mem id ids then
    craise __FILE__ __LINE__ span
      (msg ^ "detected a loop in the chain of ids: "
      ^ borrow_or_abs_ids_chain_to_string (id :: ids))
  else id :: ids

(** Helper function.

    This function allows to define in a generic way a comparison of **region
    types**. See [projections_intersect] for instance.

    Important: the regions in the types mustn't be erased.

    [default]: default boolean to return, when comparing types with no regions
    [combine]: how to combine booleans [compare_regions]: how to compare regions

    TODO: is there a way of deriving such a comparison? TODO: rename *)
let rec compare_rtys (span : Meta.span) (default : bool)
    (combine : bool -> bool -> bool)
    (compare_regions : region -> region -> bool) (ty1 : rty) (ty2 : rty) : bool
    =
  let compare = compare_rtys span default combine compare_regions in
  (* Sanity check - TODO: don't do this at every recursive call *)
  sanity_check __FILE__ __LINE__ (ty_is_rty ty1 && ty_is_rty ty2) span;
  (* Normalize the associated types *)
  match (ty1, ty2) with
  | TLiteral lit1, TLiteral lit2 ->
      sanity_check __FILE__ __LINE__ (lit1 = lit2) span;
      default
  | TAdt tref1, TAdt tref2 ->
      let generics1 = tref1.generics in
      let generics2 = tref2.generics in
      sanity_check __FILE__ __LINE__ (tref1.id = tref2.id) span;
      (* There are no regions in the const generics, so we ignore them,
         but we still check they are the same, for sanity *)
      sanity_check __FILE__ __LINE__
        (generics1.const_generics = generics2.const_generics)
        span;

      (* We also ignore the trait refs *)

      (* The check for the ADTs is very crude: we simply compare the arguments
       * two by two.
       *
       * For instance, when checking if some projections intersect, we simply
       * check if some arguments intersect. As all the type and region
       * parameters should be used somewhere in the ADT (otherwise rustc
       * generates an error), it means that it should be equivalent to checking
       * whether two fields intersect (and anyway comparing the field types is
       * difficult in case of enumerations...).
       * If we didn't have the above property enforced by the rust compiler,
       * this check would still be a reasonable conservative approximation. *)

      (* Check the region parameters *)
      let regions = List.combine generics1.regions generics2.regions in
      let params_b =
        List.fold_left
          (fun b (r1, r2) -> combine b (compare_regions r1 r2))
          default regions
      in
      (* Check the type parameters *)
      let tys = List.combine generics1.types generics2.types in
      let tys_b =
        List.fold_left
          (fun b (ty1, ty2) -> combine b (compare ty1 ty2))
          default tys
      in
      (* Combine *)
      combine params_b tys_b
  | TRef (r1, ty1, kind1), TRef (r2, ty2, kind2) ->
      (* Sanity check *)
      sanity_check __FILE__ __LINE__ (kind1 = kind2) span;
      (* Explanation for the case where we check if projections intersect:
       * the projections intersect if the borrows intersect or their contents
       * intersect. *)
      let regions_b = compare_regions r1 r2 in
      let tys_b = compare ty1 ty2 in
      combine regions_b tys_b
  | TVar id1, TVar id2 ->
      sanity_check __FILE__ __LINE__ (id1 = id2) span;
      default
  | TTraitType _, TTraitType _ ->
      (* The types should have been normalized. If after normalization we
         get trait types, we can consider them as variables *)
      sanity_check __FILE__ __LINE__ (ty1 = ty2) span;
      default
  | _ ->
      log#ltrace
        (lazy
          ("compare_rtys: unexpected inputs:" ^ "\n- ty1: " ^ show_ty ty1
         ^ "\n- ty2: " ^ show_ty ty2));
      internal_error __FILE__ __LINE__ span

(** Check if two different projections intersect. This is necessary when giving
    a symbolic value to an abstraction: we need to check that the regions which
    are already ended inside the abstraction don't intersect the regions over
    which we project in the new abstraction. Note that the two abstractions have
    different views (in terms of regions) of the symbolic value (hence the two
    region types). *)
let projections_intersect (span : Meta.span) (ty1 : rty)
    (rset1 : RegionId.Set.t) (ty2 : rty) (rset2 : RegionId.Set.t) : bool =
  let default = false in
  let combine b1 b2 = b1 || b2 in
  let compare_regions r1 r2 =
    region_in_set r1 rset1 && region_in_set r2 rset2
  in
  compare_rtys span default combine compare_regions ty1 ty2

(** Check if the first projection contains the second projection. We use this
    function when checking invariants.

    The regions in the types shouldn't be erased (this function will raise an
    exception otherwise). *)
let projection_contains (span : Meta.span) (ty1 : rty) (rset1 : RegionId.Set.t)
    (ty2 : rty) (rset2 : RegionId.Set.t) : bool =
  let default = true in
  let combine b1 b2 = b1 && b2 in
  let compare_regions r1 r2 =
    region_in_set r1 rset1 || not (region_in_set r2 rset2)
  in
  compare_rtys span default combine compare_regions ty1 ty2

(** Lookup a loan content.

    The loan is referred to by a borrow id.

    Rem.: if the {!InterpreterUtils.g_loan_content} is
    {!constructor:Aeneas.InterpreterUtils.concrete_or_abs.Concrete}, the
    {!InterpreterUtils.abs_or_var_id} is not necessarily
    {!constructor:Aeneas.InterpreterUtils.abs_or_var_id.LocalId} or
    {!constructor:Aeneas.InterpreterUtils.abs_or_var_id.DummyVarId}: there can
    be concrete loans in abstractions (in the shared values). *)
let lookup_loan_opt (span : Meta.span) (ek : exploration_kind) (l : BorrowId.id)
    (ctx : eval_ctx) : (abs_or_var_id * g_loan_content) option =
  (* We store here whether we are inside an abstraction or a value - note that we
   * could also track that with the environment, it would probably be more idiomatic
   * and cleaner *)
  let abs_or_var : abs_or_var_id option ref = ref None in

  let obj =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_borrow_content env bc =
        match bc with
        | VSharedBorrow bid ->
            (* Nothing specific to do *)
            super#visit_VSharedBorrow env bid
        | VReservedMutBorrow bid ->
            (* Nothing specific to do *)
            super#visit_VReservedMutBorrow env bid
        | VMutBorrow (bid, mv) ->
            (* Control the dive *)
            if ek.enter_mut_borrows then super#visit_VMutBorrow env bid mv
            else ()

      (** We reimplement {!visit_Loan} (rather than the more precise functions
          {!visit_SharedLoan}, etc.) on purpose: as we have an exhaustive match
          below, we are more resilient to definition updates (the compiler is
          our friend). *)
      method! visit_loan_content env lc =
        match lc with
        | VSharedLoan (bids, sv) ->
            (* Check if this is the loan we are looking for, and control the dive *)
            if BorrowId.Set.mem l bids then
              raise (FoundGLoanContent (Concrete lc))
            else if ek.enter_shared_loans then
              super#visit_VSharedLoan env bids sv
            else ()
        | VMutLoan bid ->
            (* Check if this is the loan we are looking for *)
            if bid = l then raise (FoundGLoanContent (Concrete lc))
            else super#visit_VMutLoan env bid

      (** Note that we don't control diving inside the abstractions: if we allow
          to dive inside abstractions, we allow to go anywhere (because there
          are no use cases requiring finer control) *)
      method! visit_aloan_content env lc =
        match lc with
        | AMutLoan (pm, bid, av) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            if bid = l then raise (FoundGLoanContent (Abstract lc))
            else super#visit_AMutLoan env pm bid av
        | ASharedLoan (pm, bids, v, av) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            if BorrowId.Set.mem l bids then
              raise (FoundGLoanContent (Abstract lc))
            else super#visit_ASharedLoan env pm bids v av
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedLoan (_, _)
        | AIgnoredMutLoan (_, _)
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | AIgnoredSharedLoan _ -> super#visit_aloan_content env lc

      method! visit_EBinding env bv v =
        sanity_check __FILE__ __LINE__ (Option.is_none !abs_or_var) span;
        abs_or_var :=
          Some
            (match bv with
            | BVar b -> LocalId b.index
            | BDummy id -> DummyVarId id);
        super#visit_EBinding env bv v;
        abs_or_var := None

      method! visit_EAbs env abs =
        sanity_check __FILE__ __LINE__ (Option.is_none !abs_or_var) span;
        if ek.enter_abs then (
          abs_or_var := Some (AbsId abs.abs_id);
          super#visit_EAbs env abs;
          abs_or_var := None)
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
    | None -> craise __FILE__ __LINE__ span "Inconsistent state")

(** Lookup a loan content.

    The loan is referred to by a borrow id. Raises an exception if no loan was
    found. *)
let lookup_loan (span : Meta.span) (ek : exploration_kind) (l : BorrowId.id)
    (ctx : eval_ctx) : abs_or_var_id * g_loan_content =
  match lookup_loan_opt span ek l ctx with
  | None -> craise __FILE__ __LINE__ span "Unreachable"
  | Some res -> res

(** Update a loan content.

    The loan is referred to by a borrow id.

    This is a helper function: it might break invariants. *)
let update_loan (span : Meta.span) (ek : exploration_kind) (l : BorrowId.id)
    (nlc : loan_content) (ctx : eval_ctx) : eval_ctx =
  (* We use a reference to check that we update exactly one loan: when updating
   * inside values, we check we don't update more than one loan. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let update () : loan_content =
    sanity_check __FILE__ __LINE__ (not !r) span;
    r := true;
    nlc
  in

  let obj =
    object
      inherit [_] map_eval_ctx as super

      method! visit_borrow_content env bc =
        match bc with
        | VSharedBorrow _ | VReservedMutBorrow _ ->
            (* Nothing specific to do *)
            super#visit_borrow_content env bc
        | VMutBorrow (bid, mv) ->
            (* Control the dive into mutable borrows *)
            if ek.enter_mut_borrows then super#visit_VMutBorrow env bid mv
            else VMutBorrow (bid, mv)

      (** We reimplement {!visit_loan_content} (rather than one of the sub-
          functions) on purpose: exhaustive matches are good for maintenance *)
      method! visit_loan_content env lc =
        match lc with
        | VSharedLoan (bids, sv) ->
            (* Shared loan: check if this is the loan we are looking for, and
               control the dive. *)
            if BorrowId.Set.mem l bids then update ()
            else if ek.enter_shared_loans then
              super#visit_VSharedLoan env bids sv
            else VSharedLoan (bids, sv)
        | VMutLoan bid ->
            (* Mut loan: checks if this is the loan we are looking for *)
            if bid = l then update () else super#visit_VMutLoan env bid

      (** Note that once inside the abstractions, we don't control diving (there
          are no use cases requiring finer control). Also, as we give back a
          {!loan_content} (and not an {!aloan_content}) we don't need to do
          reimplement the visit functions for the values inside the abstractions
          (rk.: there may be "concrete" values inside abstractions, so there is
          a utility in diving inside). *)
      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else abs
    end
  in

  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that we updated at least one loan *)
  sanity_check __FILE__ __LINE__ !r span;
  ctx

(** Update a abstraction loan content.

    The loan is referred to by a borrow id.

    This is a helper function: it might break invariants. *)
let update_aloan (span : Meta.span) (ek : exploration_kind) (l : BorrowId.id)
    (nlc : aloan_content) (ctx : eval_ctx) : eval_ctx =
  (* We use a reference to check that we update exactly one loan: when updating
   * inside values, we check we don't update more than one loan. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let update () : aloan_content =
    sanity_check __FILE__ __LINE__ (not !r) span;
    r := true;
    nlc
  in

  let obj =
    object
      inherit [_] map_eval_ctx as super

      method! visit_aloan_content env lc =
        match lc with
        | AMutLoan (pm, bid, av) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            if bid = l then update () else super#visit_AMutLoan env pm bid av
        | ASharedLoan (pm, bids, v, av) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            if BorrowId.Set.mem l bids then update ()
            else super#visit_ASharedLoan env pm bids v av
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedLoan (_, _)
        | AIgnoredMutLoan (_, _)
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | AIgnoredSharedLoan _ -> super#visit_aloan_content env lc

      (** Note that once inside the abstractions, we don't control diving (there
          are no use cases requiring finer control). *)
      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else abs
    end
  in

  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that we updated at least one loan *)
  sanity_check __FILE__ __LINE__ !r span;
  ctx

(** Lookup a borrow content from a borrow id. *)
let lookup_borrow_opt (span : Meta.span) (ek : exploration_kind)
    (l : BorrowId.id) (ctx : eval_ctx) : g_borrow_content option =
  let obj =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_borrow_content env bc =
        match bc with
        | VMutBorrow (bid, mv) ->
            (* Check the borrow id and control the dive *)
            if bid = l then raise (FoundGBorrowContent (Concrete bc))
            else if ek.enter_mut_borrows then super#visit_VMutBorrow env bid mv
            else ()
        | VSharedBorrow bid ->
            (* Check the borrow id *)
            if bid = l then raise (FoundGBorrowContent (Concrete bc)) else ()
        | VReservedMutBorrow bid ->
            (* Check the borrow id *)
            if bid = l then raise (FoundGBorrowContent (Concrete bc)) else ()

      method! visit_loan_content env lc =
        match lc with
        | VMutLoan bid ->
            (* Nothing special to do *) super#visit_VMutLoan env bid
        | VSharedLoan (bids, sv) ->
            (* Control the dive *)
            if ek.enter_shared_loans then super#visit_VSharedLoan env bids sv
            else ()

      method! visit_aborrow_content env bc =
        match bc with
        | AMutBorrow (pm, bid, av) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            if bid = l then raise (FoundGBorrowContent (Abstract bc))
            else super#visit_AMutBorrow env pm bid av
        | ASharedBorrow (pm, bid) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            if bid = l then raise (FoundGBorrowContent (Abstract bc))
            else super#visit_ASharedBorrow env pm bid
        | AIgnoredMutBorrow (_, _)
        | AEndedMutBorrow _
        | AEndedIgnoredMutBorrow
            { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedBorrow -> super#visit_aborrow_content env bc
        | AProjSharedBorrow asb ->
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

    Raise an exception if no loan was found *)
let lookup_borrow (span : Meta.span) (ek : exploration_kind) (l : BorrowId.id)
    (ctx : eval_ctx) : g_borrow_content =
  match lookup_borrow_opt span ek l ctx with
  | None -> craise __FILE__ __LINE__ span "Unreachable"
  | Some lc -> lc

(** Update a borrow content.

    The borrow is referred to by a borrow id.

    This is a helper function: it might break invariants. *)
let update_borrow (span : Meta.span) (ek : exploration_kind) (l : BorrowId.id)
    (nbc : borrow_content) (ctx : eval_ctx) : eval_ctx =
  (* We use a reference to check that we update exactly one borrow: when updating
   * inside values, we check we don't update more than one borrow. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let update () : borrow_content =
    sanity_check __FILE__ __LINE__ (not !r) span;
    r := true;
    nbc
  in

  let obj =
    object
      inherit [_] map_eval_ctx as super

      method! visit_borrow_content env bc =
        match bc with
        | VMutBorrow (bid, mv) ->
            (* Check the id and control dive *)
            if bid = l then update ()
            else if ek.enter_mut_borrows then super#visit_VMutBorrow env bid mv
            else VMutBorrow (bid, mv)
        | VSharedBorrow bid ->
            (* Check the id *)
            if bid = l then update () else super#visit_VSharedBorrow env bid
        | VReservedMutBorrow bid ->
            (* Check the id *)
            if bid = l then update ()
            else super#visit_VReservedMutBorrow env bid

      method! visit_loan_content env lc =
        match lc with
        | VSharedLoan (bids, sv) ->
            (* Control the dive *)
            if ek.enter_shared_loans then super#visit_VSharedLoan env bids sv
            else VSharedLoan (bids, sv)
        | VMutLoan bid ->
            (* Nothing specific to do *)
            super#visit_VMutLoan env bid

      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else abs
    end
  in

  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that we updated at least one borrow *)
  sanity_check __FILE__ __LINE__ !r span;
  ctx

(** Update an abstraction borrow content.

    The borrow is referred to by a borrow id.

    This is a helper function: **it might break invariants**. *)
let update_aborrow (span : Meta.span) (ek : exploration_kind) (l : BorrowId.id)
    (nv : avalue) (ctx : eval_ctx) : eval_ctx =
  (* We use a reference to check that we update exactly one borrow: when updating
     inside values, we check we don't update more than one borrow. Then, upon
     returning we check that we updated at least once. *)
  let r = ref false in
  let update () : avalue =
    sanity_check __FILE__ __LINE__ (not !r) span;
    r := true;
    nv
  in

  let obj =
    object
      inherit [_] map_eval_ctx as super

      method! visit_ABorrow env bc =
        match bc with
        | AMutBorrow (pm, bid, av) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            if bid = l then update ()
            else ABorrow (super#visit_AMutBorrow env pm bid av)
        | ASharedBorrow (pm, bid) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            if bid = l then update ()
            else ABorrow (super#visit_ASharedBorrow env pm bid)
        | AIgnoredMutBorrow _
        | AEndedMutBorrow _
        | AEndedSharedBorrow
        | AEndedIgnoredMutBorrow _ -> super#visit_ABorrow env bc
        | AProjSharedBorrow asb ->
            if borrow_in_asb l asb then update ()
            else ABorrow (super#visit_AProjSharedBorrow env asb)

      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else abs
    end
  in

  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that we updated at least one borrow *)
  cassert __FILE__ __LINE__ !r span "No borrow was updated";
  ctx

(** Auxiliary function: see its usage in [end_borrow_get_borrow_in_value] *)
let update_outer_borrows (outer : AbstractionId.id option * borrow_ids option)
    (x : borrow_ids) : AbstractionId.id option * borrow_ids option =
  let abs, opt = outer in
  (abs, update_if_none opt x)

(** Return the first loan we find in a value *)
let get_first_loan_in_value (v : typed_value) : loan_content option =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_loan_content _ lc = raise (FoundLoanContent lc)
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    None
  with FoundLoanContent lc -> Some lc

(** Return the first loan we find in a list of values *)
let get_first_loan_in_values (vs : typed_value list) : loan_content option =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_loan_content _ lc = raise (FoundLoanContent lc)
    end
  in
  (* We use exceptions *)
  try
    List.iter (obj#visit_typed_value ()) vs;
    None
  with FoundLoanContent lc -> Some lc

(** Return the first borrow we find in a value *)
let get_first_borrow_in_value (v : typed_value) : borrow_content option =
  let obj =
    object
      inherit [_] iter_typed_value
      method! visit_borrow_content _ bc = raise (FoundBorrowContent bc)
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    None
  with FoundBorrowContent bc -> Some bc

(** Return the first loan or borrow content we find in a value (starting with
    the outer ones).

    [with_borrows]:
    - if [true]: return the first loan or borrow we find
    - if [false]: return the first loan we find, do not dive into borrowed
      values *)
let get_first_outer_loan_or_borrow_in_value (with_borrows : bool)
    (v : typed_value) : loan_or_borrow_content option =
  let obj =
    object
      inherit [_] iter_typed_value

      method! visit_borrow_content _ bc =
        if with_borrows then raise (FoundBorrowContent bc) else ()

      method! visit_loan_content _ lc = raise (FoundLoanContent lc)
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    None
  with
  | FoundLoanContent lc -> Some (LoanContent lc)
  | FoundBorrowContent bc -> Some (BorrowContent bc)

let proj_borrows_intersects_proj_loans (span : Meta.span)
    (proj_borrows : RegionId.Set.t * symbolic_value_id * rty)
    (proj_loans : RegionId.Set.t * symbolic_value_id * rty) : bool =
  let b_regions, b_sv_id, b_ty = proj_borrows in
  let l_regions, l_sv_id, l_ty = proj_loans in
  if b_sv_id = l_sv_id then
    projections_intersect span l_ty l_regions b_ty b_regions
  else false

(** Result of looking up aproj_borrows which intersect a given aproj_loans in
    the context.

    Note that because we we force the expansion of primitively copyable values
    before giving them to abstractions, we only have the following
    possibilities:
    - no aproj_borrows, in which case the symbolic value was either dropped or
      is in the context
    - exactly one aproj_borrows over a non-shared value
    - potentially several aproj_borrows over shared values

    The result contains the ids of the abstractions in which the projectors were
    found, as well as the projection types used in those abstractions. *)
type looked_up_aproj_borrows =
  | NonSharedProj of AbstractionId.id * rty
  | SharedProjs of (AbstractionId.id * rty) list

(** Lookup the aproj_borrows (including aproj_shared_borrows) over a symbolic
    value which intersect a given set of regions.

    [lookup_shared]: if [true] also explore projectors over shared values,
    otherwise ignore.

    This is a helper function. *)
let lookup_intersecting_aproj_borrows_opt (span : Meta.span)
    (lookup_shared : bool) (regions : RegionId.Set.t)
    (sv_id : symbolic_value_id) (proj_ty : rty) (ctx : eval_ctx) :
    looked_up_aproj_borrows option =
  let found : looked_up_aproj_borrows option ref = ref None in
  let set_non_shared ((id, ty) : AbstractionId.id * rty) : unit =
    match !found with
    | None -> found := Some (NonSharedProj (id, ty))
    | Some _ -> craise __FILE__ __LINE__ span "Unreachable"
  in
  let add_shared (x : AbstractionId.id * rty) : unit =
    match !found with
    | None -> found := Some (SharedProjs [ x ])
    | Some (SharedProjs pl) -> found := Some (SharedProjs (x :: pl))
    | Some (NonSharedProj _) -> craise __FILE__ __LINE__ span "Unreachable"
  in
  let check_add_proj_borrows (is_shared : bool) abs sv' proj_ty' =
    if
      proj_borrows_intersects_proj_loans span
        (abs.regions.owned, sv', proj_ty')
        (regions, sv_id, proj_ty)
    then
      let x = (abs.abs_id, proj_ty) in
      if is_shared then add_shared x else set_non_shared x
    else ()
  in
  let obj =
    object
      inherit [_] iter_eval_ctx as super
      method! visit_abs _ abs = super#visit_abs (Some abs) abs

      method! visit_abstract_shared_borrow abs asb =
        (* Sanity check *)
        (match !found with
        | Some (NonSharedProj _) -> craise __FILE__ __LINE__ span "Unreachable"
        | _ -> ());
        (* Explore *)
        if lookup_shared then
          let abs = Option.get abs in
          match asb with
          | AsbBorrow _ -> ()
          | AsbProjReborrows (sv_id', proj_ty) ->
              let is_shared = true in
              check_add_proj_borrows is_shared abs sv_id' proj_ty
        else ()

      method! visit_aproj abs sproj =
        (let abs = Option.get abs in
         match sproj with
         | AProjLoans _ | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty -> ()
         | AProjBorrows (sv', proj_rty, _) ->
             let is_shared = false in
             check_add_proj_borrows is_shared abs sv' proj_rty);
        super#visit_aproj abs sproj
    end
  in
  (* Visit *)
  obj#visit_eval_ctx None ctx;
  (* Return *)
  !found

(** Lookup the aproj_borrows (not aproj_borrows_shared!) over a symbolic value
    which intersects a given set of regions.

    Note that there should be **at most one** (one reason is that we force the
    expansion of primitively copyable values before giving them to
    abstractions).

    Returns the id of the owning abstraction, and the projection type used in
    this abstraction. *)
let lookup_intersecting_aproj_borrows_not_shared_opt (span : Meta.span)
    (regions : RegionId.Set.t) (sv_id : symbolic_value_id) (proj_ty : rty)
    (ctx : eval_ctx) : (AbstractionId.id * rty) option =
  let lookup_shared = false in
  match
    lookup_intersecting_aproj_borrows_opt span lookup_shared regions sv_id
      proj_ty ctx
  with
  | None -> None
  | Some (NonSharedProj (abs_id, rty)) -> Some (abs_id, rty)
  | _ -> craise __FILE__ __LINE__ span "Unexpected"

(** Similar to {!lookup_intersecting_aproj_borrows_opt}, but updates the values.

    This is a helper function: **it might break invariants**.

    [include_ancestors]: when exploring an abstraction and computing projection
    intersections, use the ancestor regions. [include_owned]: when exploring an
    abstraction and computing projection intersections, use the owned regions.
*)
let update_intersecting_aproj_borrows (span : Meta.span)
    ~(fail_if_unchanged : bool) ~(include_ancestors : bool)
    ~(include_owned : bool)
    ~(update_shared :
       (abs -> symbolic_value_id -> rty -> abstract_shared_borrows) option)
    ~(update_mut :
       abs ->
       symbolic_value_id ->
       rty ->
       (msymbolic_value_id * aproj) list ->
       aproj) (proj_regions : RegionId.Set.t) (sv_id : symbolic_value_id)
    (proj_ty : rty) (ctx : eval_ctx) : eval_ctx =
  (* Small helpers for sanity checks *)
  let shared = ref None in
  let add_shared () =
    match !shared with
    | None -> shared := Some true
    | Some b -> sanity_check __FILE__ __LINE__ b span
  in
  let set_non_shared () =
    match !shared with
    | None -> shared := Some false
    | Some _ ->
        craise __FILE__ __LINE__ span
          "Found unexpected intersecting proj_borrows"
  in
  let check_proj_borrows is_shared abs sv' proj_ty' =
    let intersect_regions =
      let intersect_regions =
        if include_ancestors then abs.regions.ancestors else RegionId.Set.empty
      in
      if include_owned then
        RegionId.Set.union abs.regions.owned intersect_regions
      else intersect_regions
    in
    if
      proj_borrows_intersects_proj_loans span
        (intersect_regions, sv', proj_ty')
        (proj_regions, sv_id, proj_ty)
    then (
      if is_shared then add_shared () else set_non_shared ();
      true)
    else false
  in
  (* The visitor *)
  let obj =
    object
      inherit [_] map_eval_ctx as super
      method! visit_abs _ abs = super#visit_abs (Some abs) abs

      method! visit_abstract_shared_borrows abs asb =
        (* Sanity check *)
        (match !shared with
        | Some b -> sanity_check __FILE__ __LINE__ b span
        | _ -> ());
        (* Explore *)
        match update_shared with
        | Some update_shared ->
            let abs = Option.get abs in
            let update (asb : abstract_shared_borrow) : abstract_shared_borrows
                =
              match asb with
              | AsbBorrow _ -> [ asb ]
              | AsbProjReborrows (sv', proj_ty) ->
                  let is_shared = true in
                  if check_proj_borrows is_shared abs sv' proj_ty then
                    update_shared abs sv' proj_ty
                  else [ asb ]
            in
            List.concat (List.map update asb)
        | _ -> asb

      method! visit_aproj abs sproj =
        match sproj with
        | AProjLoans _ | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            super#visit_aproj abs sproj
        | AProjBorrows (sv', proj_rty, given_back) ->
            let abs = Option.get abs in
            let is_shared = true in
            if check_proj_borrows is_shared abs sv' proj_rty then
              update_mut abs sv' proj_rty given_back
            else super#visit_aproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check that we updated the context at least once *)
  cassert __FILE__ __LINE__
    ((not fail_if_unchanged) || Option.is_some !shared)
    span "Context was not updated";
  (* Return *)
  ctx

(** Simply calls {!update_intersecting_aproj_borrows} to update a proj_borrows
    over a non-shared value.

    We check that we update *at least* one proj_borrows.

    This is a helper function: it might break invariants. *)
let update_intersecting_aproj_borrows_mut (span : Meta.span)
    ~(include_ancestors : bool) ~(include_owned : bool)
    (proj_regions : RegionId.Set.t) (sv_id : symbolic_value_id) (proj_ty : rty)
    (nv : aproj) (ctx : eval_ctx) : eval_ctx =
  (* Small helpers *)
  let updated = ref false in
  let update_mut _ _ _ _ =
    (* We can update more than one borrow! *)
    updated := true;
    nv
  in
  (* Update *)
  let ctx =
    update_intersecting_aproj_borrows span ~fail_if_unchanged:true
      ~include_ancestors ~include_owned ~update_shared:None ~update_mut
      proj_regions sv_id proj_ty ctx
  in
  (* Check that we updated at least once *)
  sanity_check __FILE__ __LINE__ !updated span;
  (* Return *)
  ctx

(** Simply calls {!update_intersecting_aproj_borrows} to remove the proj_borrows
    over shared values.

    This is a helper function: it might break invariants. *)
let remove_intersecting_aproj_borrows_shared (span : Meta.span)
    ~(include_ancestors : bool) ~(include_owned : bool)
    (regions : RegionId.Set.t) (sv_id : symbolic_value_id) (proj_ty : rty)
    (ctx : eval_ctx) : eval_ctx =
  (* Small helpers *)
  let update_shared = Some (fun _ _ _ -> []) in
  let update_mut _ _ = craise __FILE__ __LINE__ span "Unexpected" in
  (* Update *)
  update_intersecting_aproj_borrows span ~fail_if_unchanged:true
    ~include_ancestors ~include_owned ~update_shared ~update_mut regions sv_id
    proj_ty ctx

(** Updates the proj_loans intersecting some projection.

    This is a helper function: it might break invariants.

    Note that we can update more than one projector of loans! Consider the
    following example:
    {[
      fn f<'a, 'b>(...) -> (&'a mut u32, &'b mut u32));
      fn g<'c>(&'c mut u32, &'c mut u32);

      let p = f(...);
      g(move p);

      // Symbolic context after the call to g:
      // abs'a {'a} { [s@0 <: (&'a mut u32, &'b mut u32)] }
      // abs'b {'b} { [s@0 <: (&'a mut u32, &'b mut u32)] }
      //
      // abs'c {'c} { (s@0 <: (&'c mut u32, &'c mut u32)) }
    ]}

    Note that for sanity, this function checks that we update *at least* one
    projector of loans.

    [proj_ty]: shouldn't contain erased regions.

    [subst]: takes as parameters the abstraction in which we perform the
    substitution and the list of given back values at the projector of loans
    where we perform the substitution (see the fields in {!Values.AProjLoans}).
    Note that the symbolic value at this place is necessarily equal to [sv],
    which is why we don't give it as parameters.

    [include_ancestors]: when exploring an abstraction and computing projection
    intersections, use the ancestor regions. [include_owned]: when exploring an
    abstraction and computing projection intersections, use the owned regions.
*)
let update_intersecting_aproj_loans (span : Meta.span)
    ~(fail_if_unchanged : bool) ~(include_ancestors : bool)
    ~(include_owned : bool) (proj_regions : RegionId.Set.t) (proj_ty : rty)
    (sv_id : symbolic_value_id)
    (subst :
      abs ->
      symbolic_value_id ->
      rty ->
      (msymbolic_value_id * aproj) list ->
      aproj) (ctx : eval_ctx) : eval_ctx =
  (* *)
  sanity_check __FILE__ __LINE__ (ty_is_rty proj_ty) span;
  (* Small helpers for sanity checks *)
  let updated = ref false in
  let update abs abs_sv abs_proj_ty local_given_back : aproj =
    (* Note that we can update more than once! *)
    updated := true;
    subst abs abs_sv abs_proj_ty local_given_back
  in
  (* The visitor *)
  let obj =
    object
      inherit [_] map_eval_ctx as super
      method! visit_abs _ abs = super#visit_abs (Some abs) abs

      method! visit_aproj abs sproj =
        match sproj with
        | AProjBorrows _ | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            super#visit_aproj abs sproj
        | AProjLoans (abs_sv, abs_proj_ty, given_back) ->
            let abs = Option.get abs in
            if sv_id = abs_sv then
              let abs_regions = RegionId.Set.empty in
              let abs_regions =
                if include_ancestors then
                  RegionId.Set.union abs.regions.ancestors abs_regions
                else abs_regions
              in
              let abs_regions =
                if include_owned then
                  RegionId.Set.union abs.regions.owned abs_regions
                else abs_regions
              in
              if
                projections_intersect span proj_ty proj_regions abs_proj_ty
                  abs_regions
              then update abs abs_sv abs_proj_ty given_back
              else super#visit_aproj (Some abs) sproj
            else super#visit_aproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check that we updated the context at least once *)
  sanity_check __FILE__ __LINE__ ((not fail_if_unchanged) || !updated) span;
  (* Return *)
  ctx

(** Helper function: lookup an {!constructor:Values.aproj.AProjLoans} by using
    an abstraction id and a symbolic value.

    We return the information from the looked up projector of loans. See the
    fields in {!constructor:Values.aproj.AProjLoans} (we don't return the
    symbolic value, because it is equal to [sv]).

    Sanity check: we check that there is not more than one projector which
    corresponds to the couple (abstraction id, symbolic value). *)
let lookup_aproj_loans_opt (span : Meta.span) (abs_id : AbstractionId.id)
    (sv_id : symbolic_value_id) (ctx : eval_ctx) :
    (msymbolic_value_id * aproj) list option =
  (* Small helpers for sanity checks *)
  let found = ref None in
  let set_found x =
    (* There is at most one projector which corresponds to the description *)
    sanity_check __FILE__ __LINE__ (Option.is_none !found) span;
    found := Some x
  in
  (* The visitor *)
  let obj =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_abs _ abs =
        if abs.abs_id = abs_id then super#visit_abs (Some abs) abs else ()

      method! visit_aproj (abs : abs option) sproj =
        (match sproj with
        | AProjBorrows _ | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            super#visit_aproj abs sproj
        | AProjLoans (abs_sv, _, given_back) ->
            let abs = Option.get abs in
            sanity_check __FILE__ __LINE__ (abs.abs_id = abs_id) span;
            if abs_sv = sv_id then set_found given_back else ());
        super#visit_aproj abs sproj
    end
  in
  (* Apply *)
  obj#visit_eval_ctx None ctx;
  (* Return *)
  !found

let lookup_aproj_loans (span : Meta.span) (abs_id : AbstractionId.id)
    (sv_id : symbolic_value_id) (ctx : eval_ctx) :
    (msymbolic_value_id * aproj) list =
  Option.get (lookup_aproj_loans_opt span abs_id sv_id ctx)

(** Helper function: might break invariants.

    Update a projector over loans. The projector is identified by a symbolic
    value and an abstraction id.

    Sanity check: we check that there is exactly one projector which corresponds
    to the couple (abstraction id, symbolic value). *)
let update_aproj_loans (span : Meta.span) (abs_id : AbstractionId.id)
    (sv_id : symbolic_value_id) (nproj : aproj) (ctx : eval_ctx) : eval_ctx =
  (* Small helpers for sanity checks *)
  let found = ref false in
  let update () =
    (* We update at most once *)
    sanity_check __FILE__ __LINE__ (not !found) span;
    found := true;
    nproj
  in
  (* The visitor *)
  let obj =
    object
      inherit [_] map_eval_ctx as super

      method! visit_abs _ abs =
        if abs.abs_id = abs_id then super#visit_abs (Some abs) abs else abs

      method! visit_aproj (abs : abs option) sproj =
        match sproj with
        | AProjBorrows _ | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            super#visit_aproj abs sproj
        | AProjLoans (abs_sv, _, _) ->
            let abs = Option.get abs in
            sanity_check __FILE__ __LINE__ (abs.abs_id = abs_id) span;
            if abs_sv = sv_id then update ()
            else super#visit_aproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Sanity check *)
  sanity_check __FILE__ __LINE__ !found span;
  (* Return *)
  ctx

(** Helper function: might break invariants.

    Update a projector over borrows. The projector is identified by a symbolic
    value and an abstraction id.

    Sanity check: we check that there is exactly one projector which corresponds
    to the couple (abstraction id, symbolic value).

    TODO: factorize with {!update_aproj_loans}? *)
let update_aproj_borrows (span : Meta.span) (abs_id : AbstractionId.id)
    (sv : symbolic_value) (nproj : aproj) (ctx : eval_ctx) : eval_ctx =
  (* Small helpers for sanity checks *)
  let found = ref false in
  let update () =
    (* We update at most once *)
    sanity_check __FILE__ __LINE__ (not !found) span;
    found := true;
    nproj
  in
  (* The visitor *)
  let obj =
    object
      inherit [_] map_eval_ctx as super

      method! visit_abs _ abs =
        if abs.abs_id = abs_id then super#visit_abs (Some abs) abs else abs

      method! visit_aproj (abs : abs option) sproj =
        match sproj with
        | AProjLoans _ | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            super#visit_aproj abs sproj
        | AProjBorrows (abs_sv, _proj_ty, _given_back) ->
            let abs = Option.get abs in
            sanity_check __FILE__ __LINE__ (abs.abs_id = abs_id) span;
            if abs_sv = sv.sv_id then update ()
            else super#visit_aproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Sanity check *)
  sanity_check __FILE__ __LINE__ !found span;
  (* Return *)
  ctx

(** Helper function: might break invariants.

    Converts an {!Values.aproj.AProjLoans} to an
    {!Values.aproj.AEndedProjLoans}. The projector is identified by a symbolic
    value and an abstraction id.

    **Remark:** the loan projector is allowed not to exist in the context
    anymore, in which case this function does nothing. *)
let update_aproj_loans_to_ended (span : Meta.span) (abs_id : AbstractionId.id)
    (sv_id : symbolic_value_id) (ctx : eval_ctx) : eval_ctx =
  (* Lookup the projector of loans *)
  match lookup_aproj_loans_opt span abs_id sv_id ctx with
  | Some given_back ->
      (* Create the new value for the projector *)
      let nproj = AEndedProjLoans (sv_id, given_back) in
      (* Insert it *)
      let ctx = update_aproj_loans span abs_id sv_id nproj ctx in
      (* Return *)
      ctx
  | _ ->
      (* The loan projector doesn't exist anymore: we have nothing to do *)
      ctx

let no_aproj_over_symbolic_in_context (span : Meta.span)
    (sv_id : symbolic_value_id) (ctx : eval_ctx) : unit =
  (* The visitor *)
  let obj =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_aproj env sproj =
        (match sproj with
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty -> ()
        | AProjLoans (abs_sv, _, _) | AProjBorrows (abs_sv, _, _) ->
            if abs_sv = sv_id then raise Found else ());
        super#visit_aproj env sproj
    end
  in
  (* Apply *)
  try obj#visit_eval_ctx () ctx
  with Found ->
    craise __FILE__ __LINE__ span "update_aproj_loans_to_ended: failed"

(** Helper function

    Return the loan (aloan, loan, proj_loans over a symbolic value) we find in
    an abstraction, if there is.

    **Remark:** we don't take the *ignored* mut/shared loans into account. *)
let get_first_non_ignored_aloan_in_abstraction (span : Meta.span) (abs : abs) :
    borrow_ids_or_proj_symbolic_value option =
  (* Explore to find a loan *)
  let obj =
    object
      inherit [_] iter_abs as super

      method! visit_aloan_content env lc =
        match lc with
        | AMutLoan (pm, bid, _) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            raise (FoundBorrowIds (Borrow bid))
        | ASharedLoan (pm, bids, _, _) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            sanity_check __FILE__ __LINE__ (pm = PNone) span;
            raise (FoundBorrowIds (Borrows bids))
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedLoan (_, _) -> super#visit_aloan_content env lc
        | AIgnoredMutLoan (_, _) ->
            (* Ignore *)
            super#visit_aloan_content env lc
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | AIgnoredSharedLoan _ ->
            (* Ignore *)
            super#visit_aloan_content env lc

      (** We may need to visit loan contents because of shared values *)
      method! visit_loan_content _ lc =
        match lc with
        | VMutLoan _ ->
            (* The mut loan linked to the mutable borrow present in a shared
             * value in an abstraction should be in an AProjBorrows *)
            craise __FILE__ __LINE__ span "Unreachable"
        | VSharedLoan (bids, _) -> raise (FoundBorrowIds (Borrows bids))

      method! visit_aproj env sproj =
        (match sproj with
        | AProjBorrows (_, _, _)
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty -> ()
        | AProjLoans (sv, ty, given_back) ->
            raise (FoundAProjLoans (sv, ty, given_back)));
        super#visit_aproj env sproj
    end
  in
  try
    (* Check if there are loans *)
    obj#visit_abs () abs;
    (* No loans *)
    None
  with
  (* There are loans *)
  | FoundBorrowIds bids -> Some (BorrowIds bids)
  | FoundAProjLoans (sv, proj_ty, _) ->
      (* There are loan projections over symbolic values *)
      Some (SymbolicValue (sv, proj_ty))

let lookup_shared_value_opt (span : Meta.span) (ctx : eval_ctx)
    (bid : BorrowId.id) : typed_value option =
  match lookup_loan_opt span ek_all bid ctx with
  | None -> None
  | Some (_, lc) -> (
      match lc with
      | Concrete (VSharedLoan (_, sv)) | Abstract (ASharedLoan (_, _, sv, _)) ->
          Some sv
      | _ -> None)

let lookup_shared_value (span : Meta.span) (ctx : eval_ctx) (bid : BorrowId.id)
    : typed_value =
  Option.get (lookup_shared_value_opt span ctx bid)

(** A marked borrow id *)
type marked_borrow_id = proj_marker * BorrowId.id [@@deriving show, ord]

module MarkedBorrowIdOrd = struct
  type t = marked_borrow_id

  let compare = compare_marked_borrow_id
  let to_string = show_marked_borrow_id
  let pp_t = pp_marked_borrow_id
  let show_t = show_marked_borrow_id
end

module MarkedBorrowIdSet = Collections.MakeSet (MarkedBorrowIdOrd)
module MarkedBorrowIdMap = Collections.MakeMap (MarkedBorrowIdOrd)

module MarkedBorrowId : sig
  type t

  val to_string : t -> string

  module Set : Collections.Set with type elt = t
  module Map : Collections.Map with type key = t
end
with type t = marked_borrow_id = struct
  type t = marked_borrow_id

  let to_string = show_marked_borrow_id

  module Set = MarkedBorrowIdSet
  module Map = MarkedBorrowIdMap
end

(** A marked and normalized symbolic value (loan/borrow) projection.

    A normalized symbolic value projection is a projection of a symoblic value
    for which the projection type has been normalized in the following way: the
    projected regions have the identifier 0, and the non-projected regions are
    erased.

    For instance, if we consider the region abstractions below:
    {[
      abs0 {'a} { s <: S<'a, 'b> }
      abs1 {'b} { s <: S<'a, 'b> }
    ]}

    Then normalizing (the type of) the symbolic value [s] for ['a] gives
    [S<'0, '_>], while normalizing it for ['b] gives [S<'_, '0>].

    We use normalized types to compare loan/borrow projections of symbolic
    values, and for lookups (normalized types can easily be used as keys in
    maps). *)
type marked_norm_symb_proj = {
  pm : proj_marker;
  sv_id : symbolic_value_id;
  norm_proj_ty : ty;
}
[@@deriving show, ord]

let marked_norm_symb_proj_to_string (ctx : eval_ctx) (p : marked_norm_symb_proj)
    : string =
  let { pm; sv_id; norm_proj_ty } = p in
  Print.Values.symbolic_value_id_to_pretty_string sv_id
  ^ " <: "
  ^ ty_to_string ctx norm_proj_ty
  |> Print.Values.add_proj_marker pm

module MarkedNormSymbProjOrd = struct
  type t = marked_norm_symb_proj

  let compare = compare_marked_norm_symb_proj
  let to_string = show_marked_norm_symb_proj
  let pp_t = pp_marked_norm_symb_proj
  let show_t = show_marked_norm_symb_proj
end

module MarkedNormSymbProjSet = Collections.MakeSet (MarkedNormSymbProjOrd)
module MarkedNormSymbProjMap = Collections.MakeMap (MarkedNormSymbProjOrd)

module MarkedNormSymbProj : sig
  type t

  val to_string : t -> string

  module Set : Collections.Set with type elt = t
  module Map : Collections.Map with type key = t
end
with type t = marked_norm_symb_proj = struct
  type t = marked_norm_symb_proj

  let to_string = show_marked_norm_symb_proj

  module Set = MarkedNormSymbProjSet
  module Map = MarkedNormSymbProjMap
end

type norm_symb_proj = { sv_id : symbolic_value_id; norm_proj_ty : ty }
[@@deriving show, ord]

module NormSymbProjOrd = struct
  type t = norm_symb_proj

  let compare = compare_norm_symb_proj
  let to_string = show_norm_symb_proj
  let pp_t = pp_norm_symb_proj
  let show_t = show_norm_symb_proj
end

module NormSymbProjSet = Collections.MakeSet (NormSymbProjOrd)
module NormSymbProjMap = Collections.MakeMap (NormSymbProjOrd)

module NormSymbProj : sig
  type t

  val to_string : t -> string

  module Set : Collections.Set with type elt = t
  module Map : Collections.Map with type key = t
end
with type t = norm_symb_proj = struct
  type t = norm_symb_proj

  let to_string = show_norm_symb_proj

  module Set = NormSymbProjSet
  module Map = NormSymbProjMap
end

let marked_norm_symb_proj_to_unmarked (m : marked_norm_symb_proj) :
    norm_symb_proj =
  { sv_id = m.sv_id; norm_proj_ty = m.norm_proj_ty }

(** Normalize a projection type by replacing the projected regions with ['0] and
    the non-projected ones with ['_].

    For instance, when normalizing the projection type [S<'a, 'b>] for the
    projection region ['a]. *)
let normalize_proj_ty (regions : RegionId.Set.t) (ty : rty) : rty =
  let visitor =
    object
      inherit [_] map_ty

      method! visit_region _ r =
        match r with
        | RVar (Free r) ->
            if RegionId.Set.mem r regions then RVar (Free (RegionId.of_int 0))
            else RErased
        | RVar (Bound _) | RStatic | RErased -> r
    end
  in
  visitor#visit_ty () ty

(** Compute the union of two normalized projection types *)
let rec norm_proj_tys_union (span : Meta.span) (ty1 : rty) (ty2 : rty) : rty =
  match (ty1, ty2) with
  | TAdt tref1, TAdt tref2 ->
      sanity_check __FILE__ __LINE__ (tref1.id = tref2.id) span;
      TAdt
        {
          id = tref1.id;
          generics =
            norm_proj_generic_args_union span tref1.generics tref2.generics;
        }
  | TVar id1, TVar id2 ->
      sanity_check __FILE__ __LINE__ (id1 = id2) span;
      TVar id1
  | TLiteral lit1, TLiteral lit2 ->
      sanity_check __FILE__ __LINE__ (lit1 = lit2) span;
      TLiteral lit1
  | TNever, TNever -> TNever
  | TRef (r1, ty1, rk1), TRef (r2, ty2, rk2) ->
      sanity_check __FILE__ __LINE__ (rk1 = rk2) span;
      TRef
        ( norm_proj_regions_union span r1 r2,
          norm_proj_tys_union span ty1 ty2,
          rk1 )
  | TRawPtr (ty1, rk1), TRawPtr (ty2, rk2) ->
      sanity_check __FILE__ __LINE__ (rk1 = rk2) span;
      TRawPtr (norm_proj_tys_union span ty1 ty2, rk1)
  | TTraitType (tr1, item1), TTraitType (tr2, item2) ->
      sanity_check __FILE__ __LINE__ (item1 = item2) span;
      TTraitType (norm_proj_trait_refs_union span tr1 tr2, item1)
  | ( TFnPtr
        { binder_regions = binder_regions1; binder_value = inputs1, output1 },
      TFnPtr
        { binder_regions = binder_regions2; binder_value = inputs2, output2 } )
    ->
      (* TODO: general case *)
      sanity_check __FILE__ __LINE__ (binder_regions1 = []) span;
      sanity_check __FILE__ __LINE__ (binder_regions2 = []) span;
      let binder_value =
        ( List.map2 (norm_proj_tys_union span) inputs1 inputs2,
          norm_proj_tys_union span output1 output2 )
      in
      TFnPtr { binder_regions = []; binder_value }
  | _ -> internal_error __FILE__ __LINE__ span

and norm_proj_generic_args_union span (generics1 : generic_args)
    (generics2 : generic_args) : generic_args =
  let {
    regions = regions1;
    types = types1;
    const_generics = const_generics1;
    trait_refs = trait_refs1;
  } =
    generics1
  in
  let {
    regions = regions2;
    types = types2;
    const_generics = const_generics2;
    trait_refs = trait_refs2;
  } =
    generics2
  in
  {
    regions = List.map2 (norm_proj_regions_union span) regions1 regions2;
    types = List.map2 (norm_proj_tys_union span) types1 types2;
    const_generics =
      List.map2
        (norm_proj_const_generics_union span)
        const_generics1 const_generics2;
    trait_refs =
      List.map2 (norm_proj_trait_refs_union span) trait_refs1 trait_refs2;
  }

and norm_proj_regions_union (span : Meta.span) (r1 : region) (r2 : region) :
    region =
  match (r1, r2) with
  | RVar (Free _), RVar (Free _) ->
      (* There is an intersection: the regions should be disjoint *)
      internal_error __FILE__ __LINE__ span
  | RVar (Free rid), RErased | RErased, RVar (Free rid) ->
      sanity_check __FILE__ __LINE__ (rid = RegionId.zero) span;
      RVar (Free rid)
  | _ -> internal_error __FILE__ __LINE__ span

and norm_proj_trait_refs_union (span : Meta.span) (tr1 : trait_ref)
    (tr2 : trait_ref) : trait_ref =
  let { trait_id = trait_id1; trait_decl_ref = decl_ref1 } = tr1 in
  let { trait_id = trait_id2; trait_decl_ref = decl_ref2 } = tr2 in
  sanity_check __FILE__ __LINE__ (trait_id1 = trait_id2) span;
  (* There might be regions but let's ignore this for now... *)
  sanity_check __FILE__ __LINE__ (decl_ref1 = decl_ref2) span;
  tr1

and norm_proj_const_generics_union (span : Meta.span) (cg1 : const_generic)
    (cg2 : const_generic) : const_generic =
  sanity_check __FILE__ __LINE__ (cg1 = cg2) span;
  cg1

let norm_proj_ty_contains span (ty1 : rty) (ty2 : rty) : bool =
  let set = RegionId.Set.singleton RegionId.zero in
  projection_contains span ty1 set ty2 set

(** Refresh the live region ids appearing in a type, and return the new type
    with the map from old regions to fresh regions. *)
let refresh_live_regions_in_ty (span : Meta.span) (ctx : eval_ctx) (ty : rty) :
    RegionId.id RegionId.Map.t * rty =
  let regions = ref RegionId.Map.empty in

  let get_region rid =
    (* Introduce a fresh region, if the region is alive *)
    if not (RegionId.Set.mem rid ctx.ended_regions) then (
      match RegionId.Map.find_opt rid !regions with
      | Some rid -> rid
      | None ->
          let nrid = fresh_region_id () in
          regions := RegionId.Map.add rid nrid !regions;
          nrid)
    else rid
  in
  let visitor =
    object
      inherit [_] map_ty

      method! visit_RVar _ var =
        match var with
        | Free rid -> RVar (Free (get_region rid))
        | Bound _ -> internal_error __FILE__ __LINE__ span
    end
  in
  let ty = visitor#visit_ty () ty in
  (!regions, ty)
