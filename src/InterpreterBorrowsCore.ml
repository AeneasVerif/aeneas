(* This file defines the basic blocks to implement the semantics of borrows.
 * Note that those functions are not only used in InterpreterBorrows, but
 * also in Invariants or InterpreterProjectors *)

module T = Types
module V = Values
module C = Contexts
module Subst = Substitute
module L = Logging
open Utils
open TypesUtils
open InterpreterUtils

(** The local logger *)
let log = L.borrows_log

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

type borrow_ids = Borrows of V.BorrowId.Set.t | Borrow of V.BorrowId.id
[@@deriving show]

exception FoundBorrowIds of borrow_ids

type priority_borrows_or_abs =
  | OuterBorrows of borrow_ids
  | OuterAbs of V.AbstractionId.id
  | InnerLoans of borrow_ids
[@@deriving show]

let update_if_none opt x = match opt with None -> Some x | _ -> opt

exception FoundPriority of priority_borrows_or_abs
(** Utility exception *)

type loan_or_borrow_content =
  | LoanContent of V.loan_content
  | BorrowContent of V.borrow_content
[@@deriving show]

type borrow_or_abs_id =
  | BorrowId of V.BorrowId.id
  | AbsId of V.AbstractionId.id

type borrow_or_abs_ids = borrow_or_abs_id list

let borrow_or_abs_id_to_string (id : borrow_or_abs_id) : string =
  match id with
  | AbsId id -> "abs@" ^ V.AbstractionId.to_string id
  | BorrowId id -> "l@" ^ V.BorrowId.to_string id

let borrow_or_abs_ids_chain_to_string (ids : borrow_or_abs_ids) : string =
  let ids = List.rev ids in
  let ids = List.map borrow_or_abs_id_to_string ids in
  String.concat " -> " ids

(** Add a borrow or abs id to a chain of ids, while checking that we don't loop *)
let add_borrow_or_abs_id_to_chain (msg : string) (id : borrow_or_abs_id)
    (ids : borrow_or_abs_ids) : borrow_or_abs_ids =
  if List.mem id ids then
    failwith
      (msg ^ "detected a loop in the chain of ids: "
      ^ borrow_or_abs_ids_chain_to_string (id :: ids))
  else id :: ids

(** Helper function.
  
    This function allows to define in a generic way a comparison of region types.
    See [projections_interesect] for instance.
    
    [default]: default boolean to return, when comparing types with no regions
    [combine]: how to combine booleans
    [compare_regions]: how to compare regions
 *)
let rec compare_rtys (default : bool) (combine : bool -> bool -> bool)
    (compare_regions : T.RegionId.id T.region -> T.RegionId.id T.region -> bool)
    (ty1 : T.rty) (ty2 : T.rty) : bool =
  let compare = compare_rtys default combine compare_regions in
  match (ty1, ty2) with
  | T.Bool, T.Bool | T.Char, T.Char | T.Str, T.Str -> default
  | T.Integer int_ty1, T.Integer int_ty2 ->
      assert (int_ty1 = int_ty2);
      default
  | T.Adt (id1, regions1, tys1), T.Adt (id2, regions2, tys2) ->
      assert (id1 = id2);

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
      let regions = List.combine regions1 regions2 in
      let params_b =
        List.fold_left
          (fun b (r1, r2) -> combine b (compare_regions r1 r2))
          default regions
      in
      (* Check the type parameters *)
      let tys = List.combine tys1 tys2 in
      let tys_b =
        List.fold_left
          (fun b (ty1, ty2) -> combine b (compare ty1 ty2))
          default tys
      in
      (* Combine *)
      combine params_b tys_b
  | T.Array ty1, T.Array ty2 | T.Slice ty1, T.Slice ty2 -> compare ty1 ty2
  | T.Ref (r1, ty1, kind1), T.Ref (r2, ty2, kind2) ->
      (* Sanity check *)
      assert (kind1 = kind2);
      (* Explanation for the case where we check if projections intersect:
       * the projections intersect if the borrows intersect or their contents
       * intersect. *)
      let regions_b = compare_regions r1 r2 in
      let tys_b = compare ty1 ty2 in
      combine regions_b tys_b
  | T.TypeVar id1, T.TypeVar id2 ->
      assert (id1 = id2);
      default
  | _ ->
      log#lerror
        (lazy
          ("compare_rtys: unexpected inputs:" ^ "\n- ty1: " ^ T.show_rty ty1
         ^ "\n- ty2: " ^ T.show_rty ty2));
      failwith "Unreachable"

(** Check if two different projections intersect. This is necessary when
    giving a symbolic value to an abstraction: we need to check that
    the regions which are already ended inside the abstraction don't
    intersect the regions over which we project in the new abstraction.
    Note that the two abstractions have different views (in terms of regions)
    of the symbolic value (hence the two region types).
*)
let projections_intersect (ty1 : T.rty) (rset1 : T.RegionId.Set.t) (ty2 : T.rty)
    (rset2 : T.RegionId.Set.t) : bool =
  let default = false in
  let combine b1 b2 = b1 || b2 in
  let compare_regions r1 r2 =
    region_in_set r1 rset1 && region_in_set r2 rset2
  in
  compare_rtys default combine compare_regions ty1 ty2

(** Check if the first projection contains the second projection.
    We use this function when checking invariants.
*)
let projection_contains (ty1 : T.rty) (rset1 : T.RegionId.Set.t) (ty2 : T.rty)
    (rset2 : T.RegionId.Set.t) : bool =
  let default = true in
  let combine b1 b2 = b1 && b2 in
  let compare_regions r1 r2 =
    region_in_set r1 rset1 || not (region_in_set r2 rset2)
  in
  compare_rtys default combine compare_regions ty1 ty2

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
        | V.SharedBorrow (mv, bid) ->
            (* Nothing specific to do *)
            super#visit_SharedBorrow env mv bid
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
        | V.AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | V.AEndedSharedLoan (_, _)
        | V.AIgnoredMutLoan (_, _)
        | V.AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | V.AIgnoredSharedLoan _ ->
            super#visit_aloan_content env lc
      (** Note that we don't control diving inside the abstractions: if we
          allow to dive inside abstractions, we allow to go anywhere
          (because there are no use cases requiring finer control) *)

      method! visit_Var env bv v =
        assert (Option.is_none !abs_or_var);
        abs_or_var :=
          Some
            (VarId (match bv with Some bv -> Some bv.C.index | None -> None));
        super#visit_Var env bv v;
        abs_or_var := None

      method! visit_Abs env abs =
        assert (Option.is_none !abs_or_var);
        if ek.enter_abs then (
          abs_or_var := Some (AbsId abs.V.abs_id);
          super#visit_Abs env abs;
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
        | V.SharedBorrow (_, _) | V.InactivatedMutBorrow _ ->
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
        | V.AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | V.AEndedSharedLoan (_, _)
        | V.AIgnoredMutLoan (_, _)
        | V.AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | V.AIgnoredSharedLoan _ ->
            super#visit_aloan_content env lc

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
        | V.SharedBorrow (_, bid) ->
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
        | V.AMutBorrow (mv, bid, av) ->
            if bid = l then raise (FoundGBorrowContent (Abstract bc))
            else super#visit_AMutBorrow env mv bid av
        | V.ASharedBorrow bid ->
            if bid = l then raise (FoundGBorrowContent (Abstract bc))
            else super#visit_ASharedBorrow env bid
        | V.AIgnoredMutBorrow (_, _)
        | V.AEndedMutBorrow _
        | V.AEndedIgnoredMutBorrow
            { given_back_loans_proj = _; child = _; given_back_meta = _ } ->
            super#visit_aborrow_content env bc
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
        | V.SharedBorrow (mv, bid) ->
            (* Check the id *)
            if bid = l then update () else super#visit_SharedBorrow env mv bid
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
        | V.AMutBorrow (mv, bid, av) ->
            if bid = l then update ()
            else V.ABorrow (super#visit_AMutBorrow env mv bid av)
        | V.ASharedBorrow bid ->
            if bid = l then update ()
            else V.ABorrow (super#visit_ASharedBorrow env bid)
        | V.AIgnoredMutBorrow _ | V.AEndedMutBorrow _
        | V.AEndedIgnoredMutBorrow _ ->
            super#visit_ABorrow env bc
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
let update_outer_borrows (outer : V.AbstractionId.id option * borrow_ids option)
    (x : borrow_ids) : V.AbstractionId.id option * borrow_ids option =
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

(** Return the first borrow we find in a value *)
let get_first_borrow_in_value (v : V.typed_value) : V.borrow_content option =
  let obj =
    object
      inherit [_] V.iter_typed_value

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
    - if true: return the first loan or borrow we find
    - if false: return the first loan we find, do not dive into borrowed values
 *)
let get_first_outer_loan_or_borrow_in_value (with_borrows : bool)
    (v : V.typed_value) : loan_or_borrow_content option =
  let obj =
    object
      inherit [_] V.iter_typed_value

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

type gproj_borrows =
  | AProjBorrows of V.AbstractionId.id * V.symbolic_value
  | ProjBorrows of V.symbolic_value

let proj_borrows_intersects_proj_loans
    (proj_borrows : T.RegionId.Set.t * V.symbolic_value * T.rty)
    (proj_loans : T.RegionId.Set.t * V.symbolic_value) : bool =
  let b_regions, b_sv, b_ty = proj_borrows in
  let l_regions, l_sv = proj_loans in
  if same_symbolic_id b_sv l_sv then
    projections_intersect l_sv.V.sv_ty l_regions b_ty b_regions
  else false

(** Result of looking up aproj_borrows which intersect a given aproj_loans in
    the context.

    Note that because we we force the expansion of primitively copyable values
    before giving them to abstractions, we only have the following possibilities:
    - no aproj_borrows, in which case the symbolic value was either dropped
      or is in the context
    - exactly one aproj_borrows over a non-shared value
    - potentially several aproj_borrows over shared values
    
    The result contains the ids of the abstractions in which the projectors were
    found, as well as the projection types used in those abstractions.
*)
type looked_up_aproj_borrows =
  | NonSharedProj of V.AbstractionId.id * T.rty
  | SharedProjs of (V.AbstractionId.id * T.rty) list

(** Lookup the aproj_borrows (including aproj_shared_borrows) over a
    symbolic value which intersect a given set of regions.
        
    [lookup_shared]: if `true` also explore projectors over shared values,
    otherwise ignore.
    
    This is a helper function.
*)
let lookup_intersecting_aproj_borrows_opt (lookup_shared : bool)
    (regions : T.RegionId.Set.t) (sv : V.symbolic_value) (ctx : C.eval_ctx) :
    looked_up_aproj_borrows option =
  let found : looked_up_aproj_borrows option ref = ref None in
  let set_non_shared ((id, ty) : V.AbstractionId.id * T.rty) : unit =
    match !found with
    | None -> found := Some (NonSharedProj (id, ty))
    | Some _ -> failwith "Unreachable"
  in
  let add_shared (x : V.AbstractionId.id * T.rty) : unit =
    match !found with
    | None -> found := Some (SharedProjs [ x ])
    | Some (SharedProjs pl) -> found := Some (SharedProjs (x :: pl))
    | Some (NonSharedProj _) -> failwith "Unreachable"
  in
  let check_add_proj_borrows (is_shared : bool) abs sv' proj_ty =
    if
      proj_borrows_intersects_proj_loans
        (abs.V.regions, sv', proj_ty)
        (regions, sv)
    then
      let x = (abs.abs_id, proj_ty) in
      if is_shared then add_shared x else set_non_shared x
    else ()
  in
  let obj =
    object
      inherit [_] C.iter_eval_ctx as super

      method! visit_abs _ abs = super#visit_abs (Some abs) abs

      method! visit_abstract_shared_borrows abs asb =
        (* Sanity check *)
        (match !found with
        | Some (NonSharedProj _) -> failwith "Unreachable"
        | _ -> ());
        (* Explore *)
        if lookup_shared then
          let abs = Option.get abs in
          let check asb =
            match asb with
            | V.AsbBorrow _ -> ()
            | V.AsbProjReborrows (sv', proj_ty) ->
                let is_shared = true in
                check_add_proj_borrows is_shared abs sv' proj_ty
          in
          List.iter check asb
        else ()

      method! visit_aproj abs sproj =
        (let abs = Option.get abs in
         match sproj with
         | AProjLoans _ | AEndedProjLoans _ | AEndedProjBorrows _
         | AIgnoredProjBorrows ->
             ()
         | AProjBorrows (sv', proj_rty) ->
             let is_shared = false in
             check_add_proj_borrows is_shared abs sv' proj_rty);
        super#visit_aproj abs sproj
    end
  in
  (* Visit *)
  obj#visit_eval_ctx None ctx;
  (* Return *)
  !found

(** Lookup the aproj_borrows (not aproj_borrows_shared!) over a symbolic
    value which intersects a given set of regions.
    
    Note that there should be **at most one** (one reason is that we force
    the expansion of primitively copyable values before giving them to
    abstractions).
    
    Returns the id of the owning abstraction, and the projection type used in
    this abstraction.
*)
let lookup_intersecting_aproj_borrows_not_shared_opt
    (regions : T.RegionId.Set.t) (sv : V.symbolic_value) (ctx : C.eval_ctx) :
    (V.AbstractionId.id * T.rty) option =
  let lookup_shared = false in
  match lookup_intersecting_aproj_borrows_opt lookup_shared regions sv ctx with
  | None -> None
  | Some (NonSharedProj (abs_id, rty)) -> Some (abs_id, rty)
  | _ -> failwith "Unexpected"

(** Similar to [lookup_intersecting_aproj_borrows_opt], but updates the
    values.

    This is a helper function: it might break invariants.
 *)
let update_intersecting_aproj_borrows (can_update_shared : bool)
    (update_shared : V.AbstractionId.id -> T.rty -> V.abstract_shared_borrows)
    (update_non_shared : V.AbstractionId.id -> T.rty -> V.aproj)
    (regions : T.RegionId.Set.t) (sv : V.symbolic_value) (ctx : C.eval_ctx) :
    C.eval_ctx =
  (* Small helpers for sanity checks *)
  let shared = ref None in
  let add_shared () =
    match !shared with None -> shared := Some true | Some b -> assert b
  in
  let set_non_shared () =
    match !shared with
    | None -> shared := Some false
    | Some _ -> failwith "Found unexpected intersecting proj_borrows"
  in
  let check_proj_borrows is_shared abs sv' proj_ty =
    if
      proj_borrows_intersects_proj_loans
        (abs.V.regions, sv', proj_ty)
        (regions, sv)
    then (
      if is_shared then add_shared () else set_non_shared ();
      true)
    else false
  in
  (* The visitor *)
  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_abs _ abs = super#visit_abs (Some abs) abs

      method! visit_abstract_shared_borrows abs asb =
        (* Sanity check *)
        (match !shared with Some b -> assert b | _ -> ());
        (* Explore *)
        if can_update_shared then
          let abs = Option.get abs in
          let update (asb : V.abstract_shared_borrow) :
              V.abstract_shared_borrows =
            match asb with
            | V.AsbBorrow _ -> [ asb ]
            | V.AsbProjReborrows (sv', proj_ty) ->
                let is_shared = true in
                if check_proj_borrows is_shared abs sv' proj_ty then
                  update_shared abs.abs_id proj_ty
                else [ asb ]
          in
          List.concat (List.map update asb)
        else asb

      method! visit_aproj abs sproj =
        match sproj with
        | AProjLoans _ | AEndedProjLoans _ | AEndedProjBorrows _
        | AIgnoredProjBorrows ->
            super#visit_aproj abs sproj
        | AProjBorrows (sv', proj_rty) ->
            let abs = Option.get abs in
            let is_shared = true in
            if check_proj_borrows is_shared abs sv' proj_rty then
              update_non_shared abs.abs_id proj_rty
            else super#visit_aproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check that we updated the context at least once *)
  assert (Option.is_some !shared);
  (* Return *)
  ctx

(** Simply calls [update_intersecting_aproj_borrows] to update a
    proj_borrows over a non-shared value.
    
    We check that we update *at least* one proj_borrows.

    This is a helper function: it might break invariants.
 *)
let update_intersecting_aproj_borrows_non_shared (regions : T.RegionId.Set.t)
    (sv : V.symbolic_value) (nv : V.aproj) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Small helpers *)
  let can_update_shared = false in
  let update_shared _ _ = failwith "Unexpected" in
  let updated = ref false in
  let update_non_shared _ _ =
    (* We can update more than one borrow! *)
    updated := true;
    nv
  in
  (* Update *)
  let ctx =
    update_intersecting_aproj_borrows can_update_shared update_shared
      update_non_shared regions sv ctx
  in
  (* Check that we updated at least once *)
  assert !updated;
  (* Return *)
  ctx

(** Simply calls [update_intersecting_aproj_borrows] to remove the
    proj_borrows over shared values.

    This is a helper function: it might break invariants.
 *)
let remove_intersecting_aproj_borrows_shared (regions : T.RegionId.Set.t)
    (sv : V.symbolic_value) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Small helpers *)
  let can_update_shared = true in
  let update_shared _ _ = [] in
  let update_non_shared _ _ = failwith "Unexpected" in
  (* Update *)
  update_intersecting_aproj_borrows can_update_shared update_shared
    update_non_shared regions sv ctx

(** Updates the proj_loans intersecting some projection.

    This is a helper function: it might break invariants.
    
    Note that we can update more than one projector of loans! Consider the
    following example:
    ```
    fn f<'a, 'b>(...) -> (&'a mut u32, &'b mut u32));
    fn g<'c>(&'c mut u32, &'c mut u32);

    let p = f(...);
    g(move p);

    // Symbolic context after the call to g:
    // abs'a {'a} { [s@0 <: (&'a mut u32, &'b mut u32)] }
    // abs'b {'b} { [s@0 <: (&'a mut u32, &'b mut u32)] }
    //
    // abs'c {'c} { (s@0 <: (&'c mut u32, &'c mut u32)) }
    ```
    
    Note that for sanity, this function checks that we update *at least* one
    projector of loans.
        
    [subst]: takes as parameters the abstraction in which we perform the
    substitution and the list of given back values at the projector of
    loans where we perform the substitution (see the fields in [AProjLoans]).
    Note that the symbolic value at this place is necessarily equal to [sv],
    which is why we don't give it as parameters.
 *)
let update_intersecting_aproj_loans (proj_regions : T.RegionId.Set.t)
    (proj_ty : T.rty) (sv : V.symbolic_value)
    (subst : V.abs -> (V.msymbolic_value * V.aproj) list -> V.aproj)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* Small helpers for sanity checks *)
  let updated = ref false in
  let update abs local_given_back : V.aproj =
    (* Note that we can update more than once! *)
    updated := true;
    subst abs local_given_back
  in
  (* The visitor *)
  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_abs _ abs = super#visit_abs (Some abs) abs

      method! visit_aproj abs sproj =
        match sproj with
        | AProjBorrows _ | AEndedProjLoans _ | AEndedProjBorrows _
        | AIgnoredProjBorrows ->
            super#visit_aproj abs sproj
        | AProjLoans (sv', given_back) ->
            let abs = Option.get abs in
            if same_symbolic_id sv sv' then (
              assert (sv.sv_ty = sv'.sv_ty);
              if
                projections_intersect proj_ty proj_regions sv'.V.sv_ty
                  abs.regions
              then update abs given_back
              else super#visit_aproj (Some abs) sproj)
            else super#visit_aproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check that we updated the context at least once *)
  assert !updated;
  (* Return *)
  ctx

(** Helper function: lookup an [AProjLoans] by using an abstraction id and a
    symbolic value.
    
    We return the information from the looked up projector of loans. See the
    fields in [AProjLoans] (we don't return the symbolic value, because it
    is equal to [sv]).
    
    Sanity check: we check that there is exactly one projector which corresponds
    to the couple (abstraction id, symbolic value).
 *)
let lookup_aproj_loans (abs_id : V.AbstractionId.id) (sv : V.symbolic_value)
    (ctx : C.eval_ctx) : (V.msymbolic_value * V.aproj) list =
  (* Small helpers for sanity checks *)
  let found = ref None in
  let set_found x =
    (* There is at most one projector which corresponds to the description *)
    assert (Option.is_none !found);
    found := Some x
  in
  (* The visitor *)
  let obj =
    object
      inherit [_] C.iter_eval_ctx as super

      method! visit_abs _ abs =
        if abs.abs_id = abs_id then super#visit_abs (Some abs) abs else ()

      method! visit_aproj (abs : V.abs option) sproj =
        (match sproj with
        | AProjBorrows _ | AEndedProjLoans _ | AEndedProjBorrows _
        | AIgnoredProjBorrows ->
            super#visit_aproj abs sproj
        | AProjLoans (sv', given_back) ->
            let abs = Option.get abs in
            assert (abs.abs_id = abs_id);
            if sv'.sv_id = sv.sv_id then (
              assert (sv' = sv);
              set_found given_back)
            else ());
        super#visit_aproj abs sproj
    end
  in
  (* Apply *)
  obj#visit_eval_ctx None ctx;
  (* Return *)
  Option.get !found

(** Helper function: might break invariants.

    Update a projector over loans. The projector is identified by a symbolic
    value and an abstraction id.

    Sanity check: we check that there is exactly one projector which corresponds
    to the couple (abstraction id, symbolic value).
 *)
let update_aproj_loans (abs_id : V.AbstractionId.id) (sv : V.symbolic_value)
    (nproj : V.aproj) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Small helpers for sanity checks *)
  let found = ref false in
  let update () =
    (* We update at most once *)
    assert (not !found);
    found := true;
    nproj
  in
  (* The visitor *)
  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_abs _ abs =
        if abs.abs_id = abs_id then super#visit_abs (Some abs) abs else abs

      method! visit_aproj (abs : V.abs option) sproj =
        match sproj with
        | AProjBorrows _ | AEndedProjLoans _ | AEndedProjBorrows _
        | AIgnoredProjBorrows ->
            super#visit_aproj abs sproj
        | AProjLoans (sv', _) ->
            let abs = Option.get abs in
            assert (abs.abs_id = abs_id);
            if sv'.sv_id = sv.sv_id then (
              assert (sv' = sv);
              update ())
            else super#visit_aproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Sanity check *)
  assert !found;
  (* Return *)
  ctx

(** Helper function: might break invariants.

    Update a projector over borrows. The projector is identified by a symbolic
    value and an abstraction id.

    Sanity check: we check that there is exactly one projector which corresponds
    to the couple (abstraction id, symbolic value).
    
    TODO: factorize with [update_aproj_loans]?
 *)
let update_aproj_borrows (abs_id : V.AbstractionId.id) (sv : V.symbolic_value)
    (nproj : V.aproj) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Small helpers for sanity checks *)
  let found = ref false in
  let update () =
    (* We update at most once *)
    assert (not !found);
    found := true;
    nproj
  in
  (* The visitor *)
  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_abs _ abs =
        if abs.abs_id = abs_id then super#visit_abs (Some abs) abs else abs

      method! visit_aproj (abs : V.abs option) sproj =
        match sproj with
        | AProjLoans _ | AEndedProjLoans _ | AEndedProjBorrows _
        | AIgnoredProjBorrows ->
            super#visit_aproj abs sproj
        | AProjBorrows (sv', _proj_ty) ->
            let abs = Option.get abs in
            assert (abs.abs_id = abs_id);
            if sv'.sv_id = sv.sv_id then (
              assert (sv' = sv);
              update ())
            else super#visit_aproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Sanity check *)
  assert !found;
  (* Return *)
  ctx

(** Helper function: might break invariants.

    Converts an [AProjLoans] to an [AEndedProjLoans]. The projector is identified
    by a symbolic value and an abstraction id.
 *)
let update_aproj_loans_to_ended (abs_id : V.AbstractionId.id)
    (sv : V.symbolic_value) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Lookup the projector of loans *)
  let given_back = lookup_aproj_loans abs_id sv ctx in
  (* Create the new value for the projector *)
  let nproj = V.AEndedProjLoans (sv, given_back) in
  (* Insert it *)
  let ctx = update_aproj_loans abs_id sv nproj ctx in
  (* Return *)
  ctx

let no_aproj_over_symbolic_in_context (sv : V.symbolic_value) (ctx : C.eval_ctx)
    : unit =
  (* The visitor *)
  let obj =
    object
      inherit [_] C.iter_eval_ctx as super

      method! visit_aproj env sproj =
        (match sproj with
        | AEndedProjLoans _ | AEndedProjBorrows _ | AIgnoredProjBorrows -> ()
        | AProjLoans (sv', _) | AProjBorrows (sv', _) ->
            if sv'.sv_id = sv.sv_id then raise Found else ());
        super#visit_aproj env sproj
    end
  in
  (* Apply *)
  try obj#visit_eval_ctx () ctx
  with Found -> failwith "update_aproj_loans_to_ended: failed"
