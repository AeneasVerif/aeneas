(** This file defines the basic blocks to implement the semantics of borrows.
    Note that those functions are not only used in InterpBorrows, but also in
    Invariants or InterpProjectors *)

open Types
open Values
open Contexts
open Utils
open TypesUtils
open InterpUtils

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

type borrow_id_or_proj_symbolic_value =
  | BorrowId of borrow_id
  | SymbolicValue of symbolic_proj
[@@deriving show]

exception FoundBorrowId of BorrowId.id

type priority_borrow_or_abs =
  | OuterMutBorrow of borrow_id
  | OuterSharedLoan of borrow_id
  | OuterAbs of AbsId.id
  | InnerLoan of loan_id
[@@deriving show]

let update_if_none opt x =
  match opt with
  | None -> Some x
  | _ -> opt

(** Utility exception *)
exception FoundPriority of priority_borrow_or_abs

(** Utility exception *)
exception FoundSharedBorrowId of borrow_id * shared_borrow_id

type loan_or_borrow_content =
  | LoanContent of loan_content
  | BorrowContent of borrow_content
[@@deriving show]

type borrow_loan_abs_id =
  | BorrowId of unique_borrow_id
  | LoanId of loan_id
  | AbsId of AbsId.id

type borrow_loan_abs_ids = borrow_loan_abs_id list

let borrow_loan_abs_id_to_string (id : borrow_loan_abs_id) : string =
  match id with
  | AbsId id -> "abs@" ^ AbsId.to_string id
  | BorrowId id -> unique_borrow_id_to_string id
  | LoanId id -> "l@" ^ BorrowId.to_string id

let borrow_loan_abs_ids_chain_to_string (ids : borrow_loan_abs_ids) : string =
  let ids = List.rev ids in
  let ids = List.map borrow_loan_abs_id_to_string ids in
  String.concat " -> " ids

(** Add a borrow or abs id to a chain of ids, while checking that we don't loop
*)
let add_borrow_loan_abs_id_to_chain (span : Meta.span) (msg : string)
    (id : borrow_loan_abs_id) (ids : borrow_loan_abs_ids) : borrow_loan_abs_ids
    =
  if List.mem id ids then
    [%craise] span
      (msg ^ "detected a loop in the chain of ids: "
      ^ borrow_loan_abs_ids_chain_to_string (id :: ids))
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
  [%sanity_check] span (ty_is_rty ty1 && ty_is_rty ty2);
  (* Normalize the associated types *)
  match (ty1, ty2) with
  | TLiteral lit1, TLiteral lit2 ->
      [%sanity_check] span (lit1 = lit2);
      default
  | TAdt tref1, TAdt tref2 ->
      let generics1 = tref1.generics in
      let generics2 = tref2.generics in
      [%sanity_check] span (tref1.id = tref2.id);
      (* There are no regions in the const generics, so we ignore them,
         but we still check they are the same, for sanity *)
      [%sanity_check] span (generics1.const_generics = generics2.const_generics);

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
      [%sanity_check] span (kind1 = kind2);
      (* Explanation for the case where we check if projections intersect:
       * the projections intersect if the borrows intersect or their contents
       * intersect. *)
      let regions_b = compare_regions r1 r2 in
      let tys_b = compare ty1 ty2 in
      combine regions_b tys_b
  | TVar id1, TVar id2 ->
      [%sanity_check] span (id1 = id2);
      default
  | TTraitType _, TTraitType _ ->
      (* The types should have been normalized. If after normalization we
         get trait types, we can consider them as variables *)
      [%sanity_check] span (ty1 = ty2);
      default
  | _ ->
      [%ltrace
        "unexpected inputs:" ^ "\n- ty1: " ^ show_ty ty1 ^ "\n- ty2: "
        ^ show_ty ty2];
      [%internal_error] span

(** Check if two different projections intersect.

    This is necessary when giving a symbolic value to an abstraction: we need to
    check that the regions which are already ended inside the abstraction don't
    intersect the regions over which we project in the new abstraction. Note
    that the two abstractions have different views (in terms of regions) of the
    symbolic value (hence the two region types). *)
let projections_intersect (span : Meta.span) ?(allow_erased = false)
    (rset1 : RegionId.Set.t) (ty1 : rty) (rset2 : RegionId.Set.t) (ty2 : rty) :
    bool =
  let default = false in
  let combine b1 b2 = b1 || b2 in
  let compare_regions r1 r2 =
    region_in_set ~allow_erased r1 rset1 && region_in_set ~allow_erased r2 rset2
  in
  compare_rtys span default combine compare_regions ty1 ty2

(** Check if the first projection contains the second projection. We use this
    function when checking invariants.

    The regions in the types shouldn't be erased (this function will raise an
    exception otherwise). *)
let projection_contains (span : Meta.span) (rset1 : RegionId.Set.t) (ty1 : rty)
    (rset2 : RegionId.Set.t) (ty2 : rty) : bool =
  let default = true in
  let combine b1 b2 = b1 && b2 in
  let compare_regions r1 r2 =
    region_in_set r1 rset1 || not (region_in_set r2 rset2)
  in
  compare_rtys span default combine compare_regions ty1 ty2

(** Lookup a loan content.

    The loan is referred to by a borrow id.

    Rem.: if the {!InterpUtils.g_loan_content} is
    {!constructor:Aeneas.InterpUtils.concrete_or_abs.Concrete}, the
    {!InterpUtils.abs_or_var_id} is not necessarily
    {!constructor:Aeneas.InterpUtils.abs_or_var_id.LocalId} or
    {!constructor:Aeneas.InterpUtils.abs_or_var_id.DummyVarId}: there can be
    concrete loans in abstractions (in the shared values). *)
let lookup_loan_opt (span : Meta.span) (ek : exploration_kind) (l : BorrowId.id)
    (env : env) : (abs_or_var_id * g_loan_content) option =
  (* We store here whether we are inside an abstraction or a value - note that we
   * could also track that with the environment, it would probably be more idiomatic
   * and cleaner *)
  let abs_or_var : abs_or_var_id option ref = ref None in

  let obj =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_borrow_content env bc =
        match bc with
        | VSharedBorrow (bid, sid) ->
            (* Nothing specific to do *)
            super#visit_VSharedBorrow env bid sid
        | VReservedMutBorrow (bid, sid) ->
            (* Nothing specific to do *)
            super#visit_VReservedMutBorrow env bid sid
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
        | VSharedLoan (lid, sv) ->
            (* Check if this is the loan we are looking for, and control the dive *)
            if l = lid then raise (FoundGLoanContent (Concrete lc))
            else if ek.enter_shared_loans then
              super#visit_VSharedLoan env lid sv
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
            [%sanity_check] span (pm = PNone);
            if bid = l then raise (FoundGLoanContent (Abstract lc))
            else super#visit_AMutLoan env pm bid av
        | ASharedLoan (pm, lid, v, av) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            [%sanity_check] span (pm = PNone);
            if l = lid then raise (FoundGLoanContent (Abstract lc))
            else super#visit_ASharedLoan env pm lid v av
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedLoan (_, _)
        | AIgnoredMutLoan (_, _)
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | AIgnoredSharedLoan _ -> super#visit_aloan_content env lc

      method! visit_EBinding env bv v =
        [%sanity_check] span (Option.is_none !abs_or_var);
        abs_or_var :=
          Some
            (match bv with
            | BVar b -> LocalId b.index
            | BDummy id -> DummyVarId id);
        super#visit_EBinding env bv v;
        abs_or_var := None

      method! visit_EAbs env abs =
        [%sanity_check] span (Option.is_none !abs_or_var);
        if ek.enter_abs then (
          abs_or_var := Some (AbsId abs.abs_id);
          super#visit_EAbs env abs;
          abs_or_var := None)
        else ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_env () env;
    None
  with FoundGLoanContent lc -> (
    match !abs_or_var with
    | Some abs_or_var -> Some (abs_or_var, lc)
    | None -> [%craise] span "Inconsistent state")

(** Lookup a loan content.

    The loan is referred to by a borrow id. Raises an exception if no loan was
    found. *)
let lookup_loan (span : Meta.span) (ek : exploration_kind) (l : BorrowId.id)
    (env : env) : abs_or_var_id * g_loan_content =
  match lookup_loan_opt span ek l env with
  | None -> [%craise] span "Unreachable"
  | Some res -> res

let ctx_lookup_loan_opt span ek l ctx = lookup_loan_opt span ek l ctx.env
let ctx_lookup_loan span ek l ctx = lookup_loan span ek l ctx.env

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
    [%sanity_check] span (not !r);
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
        | VSharedLoan (lid, sv) ->
            (* Shared loan: check if this is the loan we are looking for, and
               control the dive. *)
            if l = lid then update ()
            else if ek.enter_shared_loans then
              super#visit_VSharedLoan env lid sv
            else VSharedLoan (lid, sv)
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
  [%sanity_check] span !r;
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
    [%sanity_check] span (not !r);
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
            [%sanity_check] span (pm = PNone);
            if bid = l then update () else super#visit_AMutLoan env pm bid av
        | ASharedLoan (pm, lid, v, av) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            [%sanity_check] span (pm = PNone);
            if l = lid then update ()
            else super#visit_ASharedLoan env pm lid v av
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
  [%sanity_check] span !r;
  ctx

(** Lookup a borrow content from a borrow id. *)
let lookup_borrow_opt (span : Meta.span) (ek : exploration_kind)
    (l : unique_borrow_id) (ctx : eval_ctx) : g_borrow_content option =
  let obj =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_borrow_content env bc =
        match bc with
        | VMutBorrow (bid, mv) ->
            (* Check the borrow id and control the dive *)
            if UMut bid = l then raise (FoundGBorrowContent (Concrete bc))
            else if ek.enter_mut_borrows then super#visit_VMutBorrow env bid mv
            else ()
        | VSharedBorrow (_, uid) ->
            (* Check the borrow id *)
            if UShared uid = l then raise (FoundGBorrowContent (Concrete bc))
            else ()
        | VReservedMutBorrow (_, uid) ->
            (* Check the borrow id *)
            if UShared uid = l then raise (FoundGBorrowContent (Concrete bc))
            else ()

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
            [%sanity_check] span (pm = PNone);
            if UMut bid = l then raise (FoundGBorrowContent (Abstract bc))
            else super#visit_AMutBorrow env pm bid av
        | ASharedBorrow (pm, bid, uid) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            [%sanity_check] span (pm = PNone);
            if UShared uid = l then raise (FoundGBorrowContent (Abstract bc))
            else super#visit_ASharedBorrow env pm bid uid
        | AIgnoredMutBorrow (_, _)
        | AEndedMutBorrow _
        | AEndedIgnoredMutBorrow
            { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedBorrow -> super#visit_aborrow_content env bc
        | AProjSharedBorrow asb -> (
            match l with
            | UShared l ->
                if borrow_in_asb l asb then
                  raise (FoundGBorrowContent (Abstract bc))
                else ()
            | UMut _ -> ())

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

    Raise an borrow if no loan was found *)
let lookup_borrow (span : Meta.span) (ek : exploration_kind)
    (l : unique_borrow_id) (ctx : eval_ctx) : g_borrow_content =
  match lookup_borrow_opt span ek l ctx with
  | None -> [%craise] span "Unreachable"
  | Some lc -> lc

(** Lookup a borrow content appearing in an abstraction expression.

    Note that abstraction expressions only track *mutable* borrows, which is why
    we identify the borrow with a [borrow_id] and not a [unique_borrow_id]. *)
let lookup_eborrow_opt (span : Meta.span) (ek : exploration_kind)
    (l : borrow_id) (ctx : eval_ctx) : eborrow_content option =
  let obj =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_eborrow_content env bc =
        match bc with
        | EMutBorrow (pm, bid, av) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            [%sanity_check] span (pm = PNone);
            if bid = l then raise (FoundEBorrowContent bc)
            else super#visit_EMutBorrow env pm bid av
        | EIgnoredMutBorrow (_, _)
        | EEndedMutBorrow _ | EEndedIgnoredMutBorrow _ ->
            super#visit_eborrow_content env bc

      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_eval_ctx () ctx;
    None
  with FoundEBorrowContent bc -> Some bc

(** Lookup a borrow content appearing in an abstraction expression.

    Raise an exception if no borrow was found *)
let lookup_eborrow (span : Meta.span) (ek : exploration_kind) (l : borrow_id)
    (ctx : eval_ctx) : eborrow_content =
  match lookup_eborrow_opt span ek l ctx with
  | None -> [%craise] span "Unreachable"
  | Some lc -> lc

(** Lookup all the shared and reserved borrows associated with a given loan id
*)
let lookup_shared_reserved_borrows (l : loan_id) (ctx : eval_ctx) :
    shared_borrow_id list =
  let borrows = ref [] in
  let obj =
    object
      inherit [_] iter_eval_ctx

      method! visit_VSharedBorrow _ l' uid =
        (* Check the borrow id *)
        if l' = l then borrows := uid :: !borrows else ()

      method! visit_VReservedMutBorrow _ l' uid =
        (* Check the borrow id *)
        if l' = l then borrows := uid :: !borrows else ()

      method! visit_ASharedBorrow _ _ l' uid =
        (* Check the borrow id *)
        if l' = l then borrows := uid :: !borrows else ()
    end
  in
  obj#visit_eval_ctx () ctx;
  List.rev !borrows

(** Update a borrow content.

    The borrow is referred to by a borrow id.

    This is a helper function: it might break invariants. *)
let update_borrow (span : Meta.span) (ek : exploration_kind)
    (l : unique_borrow_id) (nbc : borrow_content) (ctx : eval_ctx) : eval_ctx =
  (* We use a reference to check that we update exactly one borrow: when updating
     inside values, we check we don't update more than one borrow. Then, upon
     returning we check that we updated at least once. *)
  let r = ref false in
  let update () : borrow_content =
    [%sanity_check] span (not !r);
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
            if UMut bid = l then update ()
            else if ek.enter_mut_borrows then super#visit_VMutBorrow env bid mv
            else VMutBorrow (bid, mv)
        | VSharedBorrow (bid, sid) ->
            (* Check the id *)
            if UShared sid = l then update ()
            else super#visit_VSharedBorrow env bid sid
        | VReservedMutBorrow (bid, sid) ->
            (* Check the id *)
            if UShared sid = l then update ()
            else super#visit_VReservedMutBorrow env bid sid

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
  [%sanity_check] span !r;
  ctx

(** Update an abstraction borrow content.

    The borrow is referred to by a borrow id.

    This is a helper function: **it might break invariants**. *)
let update_aborrow (span : Meta.span) (ek : exploration_kind)
    (l : unique_borrow_id) (nv : avalue) (nev : evalue option) (ctx : eval_ctx)
    : eval_ctx =
  (* We use a reference to check that we update exactly one borrow: when updating
     inside values, we check we don't update more than one borrow. Then, upon
     returning we check that we updated at least once. *)
  let r = ref false in
  let update () : avalue =
    [%sanity_check] span (not !r);
    r := true;
    nv
  in

  let r_evalue = ref false in
  let update_evalue () : evalue =
    [%sanity_check] span (not !r_evalue);
    r_evalue := true;
    match nev with
    | None -> [%internal_error] span
    | Some nv -> nv
  in

  let obj =
    object
      inherit [_] map_eval_ctx as super

      method! visit_ABorrow env bc =
        match bc with
        | AMutBorrow (pm, bid, av) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            [%sanity_check] span (pm = PNone);
            if UMut bid = l then update ()
            else ABorrow (super#visit_AMutBorrow env pm bid av)
        | ASharedBorrow (pm, bid, sid) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            [%sanity_check] span (pm = PNone);
            if UShared sid = l then update ()
            else ABorrow (super#visit_ASharedBorrow env pm bid sid)
        | AIgnoredMutBorrow _
        | AEndedMutBorrow _
        | AEndedSharedBorrow
        | AEndedIgnoredMutBorrow _ -> super#visit_ABorrow env bc
        | AProjSharedBorrow asb -> (
            match l with
            | UShared l ->
                if borrow_in_asb l asb then update ()
                else ABorrow (super#visit_AProjSharedBorrow env asb)
            | UMut _ -> super#visit_ABorrow env bc)

      method! visit_EBorrow env bc =
        match bc with
        | EMutBorrow (pm, bid, av) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            [%sanity_check] span (pm = PNone);
            if UMut bid = l then update_evalue ()
            else EBorrow (super#visit_EMutBorrow env pm bid av)
        | EIgnoredMutBorrow _ | EEndedMutBorrow _ | EEndedIgnoredMutBorrow _ ->
            super#visit_EBorrow env bc

      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else abs
    end
  in

  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that we updated at least one borrow *)
  [%cassert] span !r "No borrow was updated";
  ctx

type mut_borrow_or_shared_loan_id =
  | MutBorrow of borrow_id  (** Mutable borrow *)
  | SharedLoan of loan_id  (** Shared loan *)

type outer = {
  abs_id : AbsId.id option;
  borrow_loan : mut_borrow_or_shared_loan_id option;
}

(** Auxiliary function: see its usage in [end_borrow_get_borrow_in_value] *)
let update_outer_borrow (outer : outer) (x : mut_borrow_or_shared_loan_id) :
    outer =
  { outer with borrow_loan = update_if_none outer.borrow_loan x }

(** Return the first loan we find in a value *)
let get_first_loan_in_value (v : tvalue) : loan_content option =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_loan_content _ lc = raise (FoundLoanContent lc)
    end
  in
  (* We use exceptions *)
  try
    obj#visit_tvalue () v;
    None
  with FoundLoanContent lc -> Some lc

(** Return the first loan we find in a list of values *)
let get_first_loan_in_values (vs : tvalue list) : loan_content option =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_loan_content _ lc = raise (FoundLoanContent lc)
    end
  in
  (* We use exceptions *)
  try
    List.iter (obj#visit_tvalue ()) vs;
    None
  with FoundLoanContent lc -> Some lc

(** Return the first borrow we find in a value *)
let get_first_borrow_in_value (v : tvalue) : borrow_content option =
  let obj =
    object
      inherit [_] iter_tvalue
      method! visit_borrow_content _ bc = raise (FoundBorrowContent bc)
    end
  in
  (* We use exceptions *)
  try
    obj#visit_tvalue () v;
    None
  with FoundBorrowContent bc -> Some bc

(** Return the first loan or borrow content we find in a value (starting with
    the outer ones).

    [with_borrows]:
    - if [true]: return the first loan or borrow we find
    - if [false]: return the first loan we find, do not dive into borrowed
      values *)
let get_first_outer_loan_or_borrow_in_value (with_borrows : bool) (v : tvalue) :
    loan_or_borrow_content option =
  let obj =
    object
      inherit [_] iter_tvalue

      method! visit_borrow_content _ bc =
        if with_borrows then raise (FoundBorrowContent bc) else ()

      method! visit_loan_content _ lc = raise (FoundLoanContent lc)
    end
  in
  (* We use exceptions *)
  try
    obj#visit_tvalue () v;
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
    projections_intersect span l_regions l_ty b_regions b_ty
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
  | NonSharedProj of AbsId.id * rty
  | SharedProjs of (AbsId.id * rty) list

(** Lookup the aproj_borrows (including aproj_shared_borrows) over a symbolic
    value which intersect a given set of regions.

    [lookup_shared]: if [true] also explore projectors over shared values,
    otherwise ignore.

    This is a helper function. *)
let lookup_intersecting_aproj_borrows_opt (span : Meta.span)
    (lookup_shared : bool) (regions : RegionId.Set.t) (proj : symbolic_proj)
    (ctx : eval_ctx) : looked_up_aproj_borrows option =
  let found : looked_up_aproj_borrows option ref = ref None in
  let set_non_shared ((id, ty) : AbsId.id * rty) : unit =
    match !found with
    | None -> found := Some (NonSharedProj (id, ty))
    | Some _ -> [%craise] span "Unreachable"
  in
  let add_shared (x : AbsId.id * rty) : unit =
    match !found with
    | None -> found := Some (SharedProjs [ x ])
    | Some (SharedProjs pl) -> found := Some (SharedProjs (x :: pl))
    | Some (NonSharedProj _) -> [%craise] span "Unreachable"
  in
  let check_add_proj_borrows (is_shared : bool) (abs : abs)
      (proj' : symbolic_proj) =
    if
      proj_borrows_intersects_proj_loans span
        (abs.regions.owned, proj'.sv_id, proj'.proj_ty)
        (regions, proj.sv_id, proj.proj_ty)
    then
      let x = (abs.abs_id, proj.proj_ty) in
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
        | Some (NonSharedProj _) -> [%craise] span "Unreachable"
        | _ -> ());
        (* Explore *)
        if lookup_shared then
          let abs = Option.get abs in
          match asb with
          | AsbBorrow _ -> ()
          | AsbProjReborrows proj' ->
              let is_shared = true in
              check_add_proj_borrows is_shared abs proj'
        else ()

      method! visit_aproj abs sproj =
        (let abs = Option.get abs in
         match sproj with
         | AProjLoans _ | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty -> ()
         | AProjBorrows { proj = proj'; _ } ->
             let is_shared = false in
             check_add_proj_borrows is_shared abs proj');
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
    (regions : RegionId.Set.t) (proj : symbolic_proj) (ctx : eval_ctx) :
    (AbsId.id * rty) option =
  let lookup_shared = false in
  match
    lookup_intersecting_aproj_borrows_opt span lookup_shared regions proj ctx
  with
  | None -> None
  | Some (NonSharedProj (abs_id, rty)) -> Some (abs_id, rty)
  | _ -> [%craise] span "Unexpected"

(** Similar to {!lookup_intersecting_aproj_borrows_opt}, but updates the values.

    This is a helper function: **it might break invariants**.

    [include_ancestors]: when exploring an abstraction and computing projection
    intersections, use the ancestor regions. [include_owned]: when exploring an
    abstraction and computing projection intersections, use the owned regions.

    Note that we take care of also updating abstraction regions (we only require
    a function to update mutable borrows in expressions and no function to
    update shared borrows because abstraction expressions do not track shared
    borrows/loans). *)
let update_intersecting_aproj_borrows (span : Meta.span)
    ~(fail_if_unchanged : bool) ~(include_owned : bool)
    ~(include_outlive : bool)
    ~(update_shared :
       (owned:bool ->
       outlive:bool ->
       abs ->
       symbolic_proj ->
       abstract_shared_borrows)
       option)
    ~(update_mut : owned:bool -> outlive:bool -> abs -> aproj_borrows -> aproj)
    ~(update_emut : owned:bool -> outlive:bool -> abs -> eproj_borrows -> eproj)
    (proj_regions : RegionId.Set.t) (proj : symbolic_proj) (ctx : eval_ctx) :
    eval_ctx =
  (* Small helpers for sanity checks *)
  let shared = ref None in
  let add_shared () =
    match !shared with
    | None -> shared := Some true
    | Some b -> [%sanity_check] span b
  in
  let set_non_shared () =
    match !shared with
    | None -> shared := Some false
    | Some _ -> [%craise] span "Found unexpected intersecting proj_borrows"
  in
  (* Return: [(intersects_owned, intersects_outlive)] *)
  let check_proj_borrows_core is_shared abs (proj'_sv_id : symbolic_value_id)
      (proj'_ty : ty) : bool * bool =
    if proj.sv_id = proj'_sv_id then (
      let intersects_owned =
        projections_intersect span proj_regions proj.proj_ty abs.regions.owned
          proj'_ty
      in

      (* Sanity check: if the projectors use the same symbolic id then:
         - either the projections intersect
         - or the loan projector must intersect the outlive projection type of the borrow projector

         Moreover, those two situations are mutually exclusive.

         For example:
          1. Ex.: we are ending [abs1] below:
          {[
            abs0 {'a} { AProjLoans (s0 : &'a mut T) [] }
            abs1 {'b} { AProjBorrows (s0 : &'b mut T) }
          ]}
          we can end the loan projector in [abs0].

          2. Ex.: we are ending [abs2] below, and considering [abs1]: we have to
          project the inner borrows inside of [abs1]. However we do not project
          anything into [abs0] (see the case above).
          {[
            abs0 {'a} { AProjLoans (s0 : &'a mut &'_ mut T) [] }
            abs1 {'b} { AProjLoans (s0 : &'_ mut &'b mut T) [] }
            abs2 {'c} { AProjBorrows (s0 : &'c mut &'_ mut T) }
            abs3 {'d} { AProjBorrows (s0 : &'_ mut &'d mut T) }
          ]}
      *)
      if !Config.sanity_checks && not intersects_owned then (
        let outlive_regions =
          TypesAnalysis.compute_outlive_proj_ty (Some span)
            ctx.type_ctx.type_decls proj_regions proj.proj_ty
        in
        let intersect_outlive =
          projections_intersect span outlive_regions proj.proj_ty
            abs.regions.owned proj'_ty
        in
        [%sanity_check] span (intersects_owned || intersect_outlive);
        [%sanity_check] span ((not intersects_owned) || not intersect_outlive));

      let intersects_outlive = include_outlive && not intersects_owned in
      let intersects_owned = include_owned && intersects_owned in
      let intersects = intersects_owned || intersects_outlive in
      if intersects then if is_shared then add_shared () else set_non_shared ();
      (intersects_owned, intersects_outlive))
    else (false, false)
  in

  let check_proj_borrows is_shared abs (proj' : symbolic_proj) : bool * bool =
    check_proj_borrows_core is_shared abs proj'.sv_id proj'.proj_ty
  in
  let check_eproj_borrows is_shared abs (proj' : esymbolic_proj) : bool * bool =
    check_proj_borrows_core is_shared abs proj'.sv_id proj'.proj_ty
  in
  (* The visitor *)
  let obj =
    object
      inherit [_] map_eval_ctx as super
      method! visit_abs _ abs = super#visit_abs (Some abs) abs

      method! visit_abstract_shared_borrows abs asb =
        (* Sanity check *)
        (match !shared with
        | Some b -> [%sanity_check] span b
        | _ -> ());
        (* Explore *)
        match update_shared with
        | Some update_shared ->
            let abs = Option.get abs in
            let update (asb : abstract_shared_borrow) : abstract_shared_borrows
                =
              match asb with
              | AsbBorrow _ -> [ asb ]
              | AsbProjReborrows proj' ->
                  let is_shared = true in
                  let owned, outlive = check_proj_borrows is_shared abs proj' in
                  if owned || outlive then
                    update_shared ~owned ~outlive abs proj'
                  else [ asb ]
            in
            List.concat (List.map update asb)
        | _ -> asb

      method! visit_aproj abs sproj =
        match sproj with
        | AProjLoans _ | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            super#visit_aproj abs sproj
        | AProjBorrows proj' ->
            let abs = Option.get abs in
            let is_shared = true in
            let owned, outlive = check_proj_borrows is_shared abs proj'.proj in
            if owned || outlive then update_mut ~owned ~outlive abs proj'
            else super#visit_aproj (Some abs) sproj

      method! visit_eproj abs sproj =
        match sproj with
        | EProjLoans _ | EEndedProjLoans _ | EEndedProjBorrows _ | EEmpty ->
            super#visit_eproj abs sproj
        | EProjBorrows proj' ->
            let abs = Option.get abs in
            let is_shared = true in
            let owned, outlive = check_eproj_borrows is_shared abs proj'.proj in
            if owned || outlive then update_emut ~owned ~outlive abs proj'
            else super#visit_eproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check that we updated the context at least once *)
  [%cassert] span
    ((not fail_if_unchanged) || Option.is_some !shared)
    "Context was not updated";
  (* Return *)
  ctx

(** Simply calls {!update_intersecting_aproj_borrows} to remove the proj_borrows
    over shared values.

    This is a helper function: it might break invariants. *)
let remove_intersecting_aproj_borrows_shared (span : Meta.span)
    ~(include_owned : bool) ~(include_outlive : bool) (regions : RegionId.Set.t)
    (proj : symbolic_proj) (ctx : eval_ctx) : eval_ctx =
  (* Small helpers *)
  let update_shared = Some (fun ~owned:_ ~outlive:_ _ _ -> []) in
  let update_mut ~owned:_ ~outlive:_ _ = [%craise] span "Unexpected" in
  let update_emut ~owned:_ ~outlive:_ _ = [%craise] span "Unexpected" in
  (* Update *)
  update_intersecting_aproj_borrows span ~fail_if_unchanged:true ~include_owned
    ~include_outlive ~update_shared ~update_mut ~update_emut regions proj ctx

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
    ~(fail_if_unchanged : bool) ~(include_owned : bool)
    ~(include_outlive : bool) (proj_regions : RegionId.Set.t)
    (proj : symbolic_proj)
    (subst : owned:bool -> outlive:bool -> abs -> aproj_loans -> aproj)
    (esubst : owned:bool -> outlive:bool -> abs -> eproj_loans -> eproj)
    (ctx : eval_ctx) : eval_ctx =
  (* *)
  [%sanity_check] span (ty_is_rty proj.proj_ty);
  (* Small helpers for sanity checks *)
  let updated = ref false in
  let update ~owned ~outlive abs aproj_loans : aproj =
    (* Note that we can update more than once! *)
    updated := true;
    subst ~owned ~outlive abs aproj_loans
  in
  let updated_evalue = ref false in
  let update_evalue ~owned ~outlive abs aproj_loans : eproj =
    (* Note that we can update more than once! *)
    updated_evalue := true;
    esubst ~owned ~outlive abs aproj_loans
  in
  (* Helper for sanity check: if the symbolic ids are the same then:
     - either the projections types intersect
     - or the borrow projection intersects the outlive loan projection
       and those two situations are mutually exclusive
  *)
  let check_proj abs aproj_ty owned =
    if !Config.sanity_checks then (
      let outlive_regions =
        TypesAnalysis.compute_outlive_proj_ty (Some span)
          ctx.type_ctx.type_decls proj_regions proj.proj_ty
      in
      let outlive =
        projections_intersect span outlive_regions proj.proj_ty
          abs.regions.owned aproj_ty
      in
      [%ldebug
        "- proj_regions: "
        ^ RegionId.Set.to_string None proj_regions
        ^ "\n- proj.proj_ty: "
        ^ ty_to_string ctx proj.proj_ty
        ^ "\n- abs.regions.owned: "
        ^ RegionId.Set.to_string None abs.regions.owned
        ^ "\n- aproj_loans.proj.proj_ty: " ^ ty_to_string ctx aproj_ty
        ^ "\n- outlive_regions: "
        ^ RegionId.Set.to_string None outlive_regions];
      [%sanity_check] span (owned || outlive);
      [%sanity_check] span ((not owned) || not outlive))
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
        | AProjLoans aproj_loans ->
            let abs = Option.get abs in
            if proj.sv_id = aproj_loans.proj.sv_id then (
              let owned =
                projections_intersect span proj_regions proj.proj_ty
                  abs.regions.owned aproj_loans.proj.proj_ty
              in

              (* Sanity check *)
              check_proj abs aproj_loans.proj.proj_ty owned;

              let outlive = include_outlive && not owned in
              let owned = include_owned && owned in
              update ~owned ~outlive abs aproj_loans)
            else super#visit_aproj (Some abs) sproj

      method! visit_eproj abs sproj =
        match sproj with
        | EProjBorrows _ | EEndedProjLoans _ | EEndedProjBorrows _ | EEmpty ->
            super#visit_eproj abs sproj
        | EProjLoans aproj_loans ->
            let abs = Option.get abs in
            if proj.sv_id = aproj_loans.proj.sv_id then (
              let owned =
                projections_intersect span proj_regions proj.proj_ty
                  abs.regions.owned aproj_loans.proj.proj_ty
              in

              (* Sanity check *)
              check_proj abs aproj_loans.proj.proj_ty owned;

              let outlive = include_outlive && not owned in
              let owned = include_owned && owned in
              update_evalue ~owned ~outlive abs aproj_loans)
            else super#visit_eproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check that we updated the context at least once *)
  [%sanity_check] span ((not fail_if_unchanged) || !updated);
  (* Return *)
  ctx

(** Helper function: lookup an {!constructor:Values.aproj.AProjLoans} by using
    an abstraction id and a symbolic value.

    We return the information from the looked up projector of loans. See the
    fields in {!constructor:Values.aproj.AProjLoans} (we don't return the
    symbolic value, because it is equal to [sv]).

    Sanity check: we check that there is not more than one projector which
    corresponds to the couple (abstraction id, symbolic value). *)
let lookup_aproj_loans_opt (span : Meta.span) (abs_id : AbsId.id)
    (sv_id : symbolic_value_id) (ctx : eval_ctx) :
    (aproj_loans * eproj_loans option) option =
  (* Small helpers for sanity checks *)
  let found = ref None in
  let set_found x =
    (* There is at most one projector which corresponds to the description *)
    [%sanity_check] span (Option.is_none !found);
    found := Some x
  in
  let found_eproj = ref None in
  let set_found_eproj x =
    (* There is at most one projector which corresponds to the description *)
    [%sanity_check] span (Option.is_none !found_eproj);
    found_eproj := Some x
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
        | AProjLoans aproj_loan ->
            let abs = Option.get abs in
            [%sanity_check] span (abs.abs_id = abs_id);
            if aproj_loan.proj.sv_id = sv_id then set_found aproj_loan else ());
        super#visit_aproj abs sproj

      method! visit_eproj (abs : abs option) sproj =
        (match sproj with
        | EProjBorrows _ | EEndedProjLoans _ | EEndedProjBorrows _ | EEmpty ->
            super#visit_eproj abs sproj
        | EProjLoans aproj_loan ->
            let abs = Option.get abs in
            [%sanity_check] span (abs.abs_id = abs_id);
            if aproj_loan.proj.sv_id = sv_id then set_found_eproj aproj_loan
            else ());
        super#visit_eproj abs sproj
    end
  in
  (* Apply *)
  obj#visit_eval_ctx None ctx;
  (* Return *)
  [%sanity_check] span (!found_eproj = None || Option.is_some !found);
  match !found with
  | None -> None
  | Some aproj -> Some (aproj, !found_eproj)

let lookup_aproj_loans (span : Meta.span) (abs_id : AbsId.id)
    (sv_id : symbolic_value_id) (ctx : eval_ctx) :
    aproj_loans * eproj_loans option =
  Option.get (lookup_aproj_loans_opt span abs_id sv_id ctx)

(** Helper function: might break invariants.

    Update a projector over loans. The projector is identified by a symbolic
    value and an abstraction id.

    Sanity check: we check that there is exactly one projector which corresponds
    to the couple (abstraction id, symbolic value).

    This function updates abstraction values *and* abstraction expressions. *)
let update_aproj_loans (span : Meta.span) (abs_id : AbsId.id)
    (sv_id : symbolic_value_id) (nproj : aproj) (neproj : eproj option)
    (ctx : eval_ctx) : eval_ctx =
  (* Small helpers for sanity checks *)
  let found = ref false in
  let update () =
    (* We update at most once *)
    [%sanity_check] span (not !found);
    found := true;
    nproj
  in
  let found_eproj = ref false in
  let update_eproj () =
    (* We update at most once *)
    [%sanity_check] span (not !found_eproj);
    found_eproj := true;
    match neproj with
    | None -> [%internal_error] span
    | Some proj -> proj
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
        | AProjLoans { proj = abs_proj; _ } ->
            let abs = Option.get abs in
            [%sanity_check] span (abs.abs_id = abs_id);
            if abs_proj.sv_id = sv_id then update ()
            else super#visit_aproj (Some abs) sproj

      method! visit_eproj (abs : abs option) sproj =
        match sproj with
        | EProjBorrows _ | EEndedProjLoans _ | EEndedProjBorrows _ | EEmpty ->
            super#visit_eproj abs sproj
        | EProjLoans { proj = abs_proj; _ } ->
            let abs = Option.get abs in
            [%sanity_check] span (abs.abs_id = abs_id);
            if abs_proj.sv_id = sv_id then update_eproj ()
            else super#visit_eproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Sanity check *)
  [%sanity_check] span !found;
  (* Return *)
  ctx

(** Helper function: might break invariants.

    Update a projector over borrows. The projector is identified by a symbolic
    value and an abstraction id.

    Sanity check: we check that there is exactly one projector which corresponds
    to the couple (abstraction id, symbolic value).

    TODO: factorize with {!update_aproj_loans}? *)
let update_aproj_borrows (span : Meta.span) (abs_id : AbsId.id)
    (sv : symbolic_value) (nproj : aproj) (neproj : eproj) (ctx : eval_ctx) :
    eval_ctx =
  (* Small helpers for sanity checks *)
  let found = ref false in
  let update () =
    (* We update at most once *)
    [%sanity_check] span (not !found);
    found := true;
    nproj
  in
  let found_eproj = ref false in
  let update_eproj () =
    (* We update at most once *)
    [%sanity_check] span (not !found_eproj);
    found_eproj := true;
    neproj
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
        | AProjBorrows { proj = abs_proj; _ } ->
            let abs = Option.get abs in
            [%sanity_check] span (abs.abs_id = abs_id);
            if abs_proj.sv_id = sv.sv_id then update ()
            else super#visit_aproj (Some abs) sproj

      method! visit_eproj (abs : abs option) sproj =
        match sproj with
        | EProjLoans _ | EEndedProjLoans _ | EEndedProjBorrows _ | EEmpty ->
            super#visit_eproj abs sproj
        | EProjBorrows { proj = abs_proj; _ } ->
            let abs = Option.get abs in
            [%sanity_check] span (abs.abs_id = abs_id);
            if abs_proj.sv_id = sv.sv_id then update_eproj ()
            else super#visit_eproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Sanity check *)
  [%sanity_check] span !found;
  (* Return *)
  ctx

(** Helper function: might break invariants.

    Converts an {!Values.aproj.AProjLoans} to an
    {!Values.aproj.AEndedProjLoans}. The projector is identified by a symbolic
    value and an abstraction id.

    **Remark:** the loan projector is allowed not to exist in the context
    anymore, in which case this function does nothing. *)
let update_aproj_loans_to_ended (span : Meta.span) (abs_id : AbsId.id)
    (sv_id : symbolic_value_id) (ctx : eval_ctx) : eval_ctx =
  (* Lookup the projector of loans *)
  match lookup_aproj_loans_opt span abs_id sv_id ctx with
  | Some ({ proj = _; consumed; borrows }, eproj) ->
      (* Create the new value for the projector *)
      let nproj = AEndedProjLoans { proj = sv_id; consumed; borrows } in
      let neproj =
        match eproj with
        | Some { proj = _; consumed; borrows } ->
            Some (EEndedProjLoans { proj = sv_id; consumed; borrows })
        | None -> None
      in
      (* Insert it *)
      let ctx = update_aproj_loans span abs_id sv_id nproj neproj ctx in
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
        | AProjLoans { proj = abs_proj; _ }
        | AProjBorrows { proj = abs_proj; _ } ->
            if abs_proj.sv_id = sv_id then raise Found else ());
        super#visit_aproj env sproj

      method! visit_eproj env sproj =
        (match sproj with
        | EEndedProjLoans _ | EEndedProjBorrows _ | EEmpty -> ()
        | EProjLoans { proj = abs_proj; _ }
        | EProjBorrows { proj = abs_proj; _ } ->
            if abs_proj.sv_id = sv_id then raise Found else ());
        super#visit_eproj env sproj
    end
  in
  (* Apply *)
  try obj#visit_eval_ctx () ctx
  with Found -> [%craise] span "update_aproj_loans_to_ended: failed"

let abs_has_non_ended_eborrows (abs : abs) : bool =
  let visitor =
    object
      inherit [_] iter_abs as super

      method! visit_eborrow_content env bc =
        (match bc with
        | EMutBorrow _ -> raise Found
        | EIgnoredMutBorrow _ | EEndedMutBorrow _ | EEndedIgnoredMutBorrow _ ->
            ());
        super#visit_eborrow_content env bc

      method! visit_eproj env sproj =
        (match sproj with
        | EProjBorrows _ -> raise Found
        | EProjLoans _ | EEndedProjLoans _ | EEndedProjBorrows _ | EEmpty -> ());
        super#visit_eproj env sproj
    end
  in
  try
    visitor#visit_abs () abs;
    false
  with Found -> true

let abs_has_non_ended_eloans (abs : abs) : bool =
  let visitor =
    object
      inherit [_] iter_abs as super

      method! visit_eloan_content env lc =
        (match lc with
        | EMutLoan _ -> raise Found
        | EEndedMutLoan _ | EIgnoredMutLoan _ | EEndedIgnoredMutLoan _ -> ());
        super#visit_eloan_content env lc

      method! visit_eproj env sproj =
        (match sproj with
        | EProjLoans _ -> raise Found
        | EProjBorrows _ | EEndedProjLoans _ | EEndedProjBorrows _ | EEmpty ->
            ());
        super#visit_eproj env sproj
    end
  in
  try
    visitor#visit_abs () abs;
    false
  with Found -> true

(** Helper function

    Return the loan (aloan, loan, proj_loans over a symbolic value) we find in
    an abstraction, if there is.

    **Remark:** we don't take the *ignored* mut/shared loans into account. *)
let get_first_non_ignored_aloan_in_abstraction (span : Meta.span) (abs : abs) :
    borrow_id_or_proj_symbolic_value option =
  (* Explore to find a loan *)
  let obj =
    object
      inherit [_] iter_abs as super

      method! visit_aloan_content env lc =
        match lc with
        | AMutLoan (pm, bid, _) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            [%sanity_check] span (pm = PNone);
            raise (FoundBorrowId bid)
        | ASharedLoan (pm, bid, _, _) ->
            (* Sanity check: projection markers can only appear when we're doing a join *)
            [%sanity_check] span (pm = PNone);
            raise (FoundBorrowId bid)
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
            [%craise] span "Unreachable"
        | VSharedLoan (bid, _) -> raise (FoundBorrowId bid)

      method! visit_aproj env sproj =
        (match sproj with
        | AProjBorrows _ | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty ->
            ()
        | AProjLoans proj -> raise (FoundAProjLoans proj));
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
  | FoundBorrowId bid -> Some (BorrowId bid)
  | FoundAProjLoans { proj; _ } ->
      (* There are loan projections over symbolic values *)
      Some (SymbolicValue proj)

let lookup_shared_value_opt (span : Meta.span) (env : env) (bid : BorrowId.id) :
    tvalue option =
  match lookup_loan_opt span ek_all bid env with
  | None -> None
  | Some (_, lc) -> (
      match lc with
      | Concrete (VSharedLoan (_, sv)) | Abstract (ASharedLoan (_, _, sv, _)) ->
          Some sv
      | _ -> None)

let lookup_shared_value (span : Meta.span) (env : env) (bid : BorrowId.id) :
    tvalue =
  Option.get (lookup_shared_value_opt span env bid)

let ctx_lookup_shared_value span ctx = lookup_shared_value span ctx.env

(** A marked borrow id *)
type marked_borrow_id = proj_marker * borrow_id [@@deriving show, ord]

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

(** A marked borrow id *)
type marked_unique_borrow_id = proj_marker * borrow_id * shared_borrow_id option
[@@deriving show, ord]

module MarkedUniqueBorrowIdOrd = struct
  type t = marked_unique_borrow_id

  let compare = compare_marked_unique_borrow_id
  let to_string = show_marked_unique_borrow_id
  let pp_t = pp_marked_unique_borrow_id
  let show_t = show_marked_unique_borrow_id
end

module MarkedUniqueBorrowIdSet = Collections.MakeSet (MarkedUniqueBorrowIdOrd)
module MarkedUniqueBorrowIdMap = Collections.MakeMap (MarkedUniqueBorrowIdOrd)

module MarkedUniqueBorrowId : sig
  type t

  val to_string : t -> string

  module Set : Collections.Set with type elt = t
  module Map : Collections.Map with type key = t
end
with type t = marked_unique_borrow_id = struct
  type t = marked_unique_borrow_id

  let to_string = show_marked_unique_borrow_id

  module Set = MarkedUniqueBorrowIdSet
  module Map = MarkedUniqueBorrowIdMap
end

(** A marked loan id *)
type marked_loan_id = proj_marker * loan_id [@@deriving show, ord]

module MarkedLoanIdOrd = MarkedBorrowIdOrd
module MarkedLoanIdSet = MarkedBorrowIdSet
module MarkedLoanIdMap = MarkedBorrowIdMap
module MarkedLoanId = MarkedBorrowId

let marked_unique_borrow_to_loan_id (x : marked_unique_borrow_id) :
    marked_loan_id =
  let pm, bid, _ = x in
  (pm, bid)

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
      [%sanity_check] span (tref1.id = tref2.id);
      TAdt
        {
          id = tref1.id;
          generics =
            norm_proj_generic_args_union span tref1.generics tref2.generics;
        }
  | TVar id1, TVar id2 ->
      [%sanity_check] span (id1 = id2);
      TVar id1
  | TLiteral lit1, TLiteral lit2 ->
      [%sanity_check] span (lit1 = lit2);
      TLiteral lit1
  | TNever, TNever -> TNever
  | TRef (r1, ty1, rk1), TRef (r2, ty2, rk2) ->
      [%sanity_check] span (rk1 = rk2);
      TRef
        ( norm_proj_regions_union span r1 r2,
          norm_proj_tys_union span ty1 ty2,
          rk1 )
  | TRawPtr (ty1, rk1), TRawPtr (ty2, rk2) ->
      [%sanity_check] span (rk1 = rk2);
      TRawPtr (norm_proj_tys_union span ty1 ty2, rk1)
  | TTraitType (tr1, item1), TTraitType (tr2, item2) ->
      [%sanity_check] span (item1 = item2);
      TTraitType (norm_proj_trait_refs_union span tr1 tr2, item1)
  | ( TFnPtr
        { binder_regions = binder_regions1; binder_value = inputs1, output1 },
      TFnPtr
        { binder_regions = binder_regions2; binder_value = inputs2, output2 } )
    ->
      (* TODO: general case *)
      [%sanity_check] span (binder_regions1 = []);
      [%sanity_check] span (binder_regions2 = []);
      let binder_value =
        ( List.map2 (norm_proj_tys_union span) inputs1 inputs2,
          norm_proj_tys_union span output1 output2 )
      in
      TFnPtr { binder_regions = []; binder_value }
  | _ -> [%internal_error] span

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
      [%internal_error] span
  | RVar (Free rid), RErased | RErased, RVar (Free rid) ->
      [%sanity_check] span (rid = RegionId.zero);
      RVar (Free rid)
  | _ -> [%internal_error] span

and norm_proj_trait_refs_union (span : Meta.span) (tr1 : trait_ref)
    (tr2 : trait_ref) : trait_ref =
  let { kind = trait_id1; trait_decl_ref = decl_ref1 } = tr1 in
  let { kind = trait_id2; trait_decl_ref = decl_ref2 } = tr2 in
  [%sanity_check] span (trait_id1 = trait_id2);
  (* There might be regions but let's ignore this for now... *)
  [%sanity_check] span (decl_ref1 = decl_ref2);
  tr1

and norm_proj_const_generics_union (span : Meta.span) (cg1 : const_generic)
    (cg2 : const_generic) : const_generic =
  [%sanity_check] span (cg1 = cg2);
  cg1

let norm_proj_ty_contains span (ty1 : rty) (ty2 : rty) : bool =
  let set = RegionId.Set.singleton RegionId.zero in
  projection_contains span set ty1 set ty2

let norm_proj_tys_intersect span (ty1 : norm_proj_ty) (ty2 : norm_proj_ty) :
    bool =
  let rset = RegionId.Set.singleton RegionId.zero in
  projections_intersect ~allow_erased:true span rset ty1 rset ty2

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
          let nrid = ctx.fresh_region_id () in
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
        | Bound _ -> [%internal_error] span
    end
  in
  let ty = visitor#visit_ty () ty in
  (!regions, ty)

(** Set a list of abstractions as (non-)endable *)
let update_endable (ctx : eval_ctx) (abs_ids : abs_id list) ~(can_end : bool) :
    eval_ctx =
  let abs_ids = AbsId.Set.of_list abs_ids in
  let update (e : env_elem) : env_elem =
    match e with
    | EAbs abs ->
        if AbsId.Set.mem abs.abs_id abs_ids then EAbs { abs with can_end }
        else EAbs abs
    | _ -> e
  in
  { ctx with env = List.map update ctx.env }
