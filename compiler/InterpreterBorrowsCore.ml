(** This file defines the basic blocks to implement the semantics of borrows.
    Note that those functions are not only used in InterpreterBorrows, but
    also in Invariants or InterpreterProjectors
 *)

open Types
open Values
open Contexts
open Utils
open TypesUtils
open InterpreterUtils
open Errors

(** The local logger *)
let log = Logging.borrows_log

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

type borrow_ids = Borrows of BorrowId.Set.t | Borrow of BorrowId.id
[@@deriving show]

type borrow_ids_or_symbolic_value =
  | BorrowIds of borrow_ids
  | SymbolicValue of symbolic_value
[@@deriving show]

exception FoundBorrowIds of borrow_ids

type priority_borrows_or_abs =
  | OuterBorrows of borrow_ids
  | OuterAbs of AbstractionId.id
  | InnerLoans of borrow_ids
[@@deriving show]

let update_if_none opt x = match opt with None -> Some x | _ -> opt

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

(** Add a borrow or abs id to a chain of ids, while checking that we don't loop *)
let add_borrow_or_abs_id_to_chain (msg : string) (id : borrow_or_abs_id)
    (ids : borrow_or_abs_ids) : borrow_or_abs_ids =
  if List.mem id ids then
    raise
      (Failure
         (msg ^ "detected a loop in the chain of ids: "
         ^ borrow_or_abs_ids_chain_to_string (id :: ids)))
  else id :: ids

(** Helper function.
  
    This function allows to define in a generic way a comparison of **region types**.
    See [projections_intersect] for instance.

    Important: the regions in the types mustn't be erased.

    [default]: default boolean to return, when comparing types with no regions
    [combine]: how to combine booleans
    [compare_regions]: how to compare regions

    TODO: is there a way of deriving such a comparison?
    TODO: rename
 *)
let rec compare_rtys (meta : Meta.meta) (default : bool) (combine : bool -> bool -> bool)
    (compare_regions : region -> region -> bool) (ty1 : rty) (ty2 : rty) : bool
    =
  let compare = compare_rtys meta default combine compare_regions in
  (* Sanity check - TODO: don't do this at every recursive call *)
  cassert (ty_is_rty ty1 && ty_is_rty ty2) meta "ty1 or ty2 are not rty TODO";
  (* Normalize the associated types *)
  match (ty1, ty2) with
  | TLiteral lit1, TLiteral lit2 ->
      cassert (lit1 = lit2) meta "Tlitrals are not equal TODO";
      default
  | TAdt (id1, generics1), TAdt (id2, generics2) ->
      cassert (id1 = id2) meta "ids are not equal TODO";
      (* There are no regions in the const generics, so we ignore them,
         but we still check they are the same, for sanity *)
      cassert (generics1.const_generics = generics2.const_generics) meta "const generics are not the same";

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
      cassert (kind1 = kind2) meta "kind1 and kind2 are not equal TODO";
      (* Explanation for the case where we check if projections intersect:
       * the projections intersect if the borrows intersect or their contents
       * intersect. *)
      let regions_b = compare_regions r1 r2 in
      let tys_b = compare ty1 ty2 in
      combine regions_b tys_b
  | TVar id1, TVar id2 ->
      cassert (id1 = id2) meta "Ids are not the same TODO";
      default
  | TTraitType _, TTraitType _ ->
      (* The types should have been normalized. If after normalization we
         get trait types, we can consider them as variables *)
      cassert (ty1 = ty2) meta "The types are not normalized";
      default
  | _ ->
      log#lerror
        (lazy
          ("compare_rtys: unexpected inputs:" ^ "\n- ty1: " ^ show_ty ty1
         ^ "\n- ty2: " ^ show_ty ty2));
      craise meta "Unreachable"

(** Check if two different projections intersect. This is necessary when
    giving a symbolic value to an abstraction: we need to check that
    the regions which are already ended inside the abstraction don't
    intersect the regions over which we project in the new abstraction.
    Note that the two abstractions have different views (in terms of regions)
    of the symbolic value (hence the two region types).
*)
let projections_intersect (meta : Meta.meta) (ty1 : rty) (rset1 : RegionId.Set.t) (ty2 : rty)
    (rset2 : RegionId.Set.t) : bool =
  let default = false in
  let combine b1 b2 = b1 || b2 in
  let compare_regions r1 r2 =
    region_in_set r1 rset1 && region_in_set r2 rset2
  in
  compare_rtys meta default combine compare_regions ty1 ty2

(** Check if the first projection contains the second projection.
    We use this function when checking invariants.

    The regions in the types shouldn't be erased (this function will raise an exception
    otherwise).
*)
let projection_contains (meta : Meta.meta) (ty1 : rty) (rset1 : RegionId.Set.t) (ty2 : rty)
    (rset2 : RegionId.Set.t) : bool =
  let default = true in
  let combine b1 b2 = b1 && b2 in
  let compare_regions r1 r2 =
    region_in_set r1 rset1 || not (region_in_set r2 rset2)
  in
  compare_rtys meta default combine compare_regions ty1 ty2

(** Lookup a loan content.

    The loan is referred to by a borrow id.

    Rem.: if the {!InterpreterUtils.g_loan_content} is {!constructor:Aeneas.InterpreterUtils.concrete_or_abs.Concrete},
    the {!InterpreterUtils.abs_or_var_id} is not necessarily {!constructor:Aeneas.InterpreterUtils.abs_or_var_id.VarId} or
    {!constructor:Aeneas.InterpreterUtils.abs_or_var_id.DummyVarId}: there can be concrete loans in abstractions (in the shared values).
 *)
let lookup_loan_opt (meta : Meta.meta) (ek : exploration_kind) (l : BorrowId.id) (ctx : eval_ctx) :
    (abs_or_var_id * g_loan_content) option =
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
          below, we are more resilient to definition updates (the compiler
          is our friend).
      *)
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

      (** Note that we don't control diving inside the abstractions: if we
          allow to dive inside abstractions, we allow to go anywhere
          (because there are no use cases requiring finer control) *)
      method! visit_aloan_content env lc =
        match lc with
        | AMutLoan (bid, av) ->
            if bid = l then raise (FoundGLoanContent (Abstract lc))
            else super#visit_AMutLoan env bid av
        | ASharedLoan (bids, v, av) ->
            if BorrowId.Set.mem l bids then
              raise (FoundGLoanContent (Abstract lc))
            else super#visit_ASharedLoan env bids v av
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedLoan (_, _)
        | AIgnoredMutLoan (_, _)
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | AIgnoredSharedLoan _ ->
            super#visit_aloan_content env lc

      method! visit_EBinding env bv v =
        cassert (Option.is_none !abs_or_var) meta "TODO :  error message ";
        abs_or_var :=
          Some
            (match bv with
            | BVar b -> VarId b.index
            | BDummy id -> DummyVarId id);
        super#visit_EBinding env bv v;
        abs_or_var := None

      method! visit_EAbs env abs =
        cassert (Option.is_none !abs_or_var) meta "TODO :  error message ";
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
    | None -> craise meta "Inconsistent state")

(** Lookup a loan content.

    The loan is referred to by a borrow id.
    Raises an exception if no loan was found.
 *)
let lookup_loan (meta : Meta.meta)  (ek : exploration_kind) (l : BorrowId.id) (ctx : eval_ctx) :
    abs_or_var_id * g_loan_content =
  match lookup_loan_opt meta ek l ctx with
  | None -> craise meta "Unreachable"
  | Some res -> res

(** Update a loan content.

    The loan is referred to by a borrow id.

    This is a helper function: it might break invariants.
 *)
let update_loan (meta : Meta.meta) (ek : exploration_kind) (l : BorrowId.id) (nlc : loan_content)
    (ctx : eval_ctx) : eval_ctx =
  (* We use a reference to check that we update exactly one loan: when updating
   * inside values, we check we don't update more than one loan. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let update () : loan_content =
    cassert (not !r) meta "TODO :  error message ";
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

      (** Note that once inside the abstractions, we don't control diving
          (there are no use cases requiring finer control).
          Also, as we give back a {!loan_content} (and not an {!aloan_content})
          we don't need to do reimplement the visit functions for the values
          inside the abstractions (rk.: there may be "concrete" values inside
          abstractions, so there is a utility in diving inside). *)
      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else abs
    end
  in

  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that we updated at least one loan *)
  cassert !r meta "No loan was updated";
  ctx

(** Update a abstraction loan content.

    The loan is referred to by a borrow id.

    This is a helper function: it might break invariants.
 *)
let update_aloan (meta : Meta.meta ) (ek : exploration_kind) (l : BorrowId.id) (nlc : aloan_content)
    (ctx : eval_ctx) : eval_ctx =
  (* We use a reference to check that we update exactly one loan: when updating
   * inside values, we check we don't update more than one loan. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let update () : aloan_content =
    cassert (not !r) meta "TODO :  error message ";
    r := true;
    nlc
  in

  let obj =
    object
      inherit [_] map_eval_ctx as super

      method! visit_aloan_content env lc =
        match lc with
        | AMutLoan (bid, av) ->
            if bid = l then update () else super#visit_AMutLoan env bid av
        | ASharedLoan (bids, v, av) ->
            if BorrowId.Set.mem l bids then update ()
            else super#visit_ASharedLoan env bids v av
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedLoan (_, _)
        | AIgnoredMutLoan (_, _)
        | AEndedIgnoredMutLoan
            { given_back = _; child = _; given_back_meta = _ }
        | AIgnoredSharedLoan _ ->
            super#visit_aloan_content env lc

      (** Note that once inside the abstractions, we don't control diving
          (there are no use cases requiring finer control). *)
      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else abs
    end
  in

  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that we updated at least one loan *)
  cassert !r meta "No loan was uodated";
  ctx

(** Lookup a borrow content from a borrow id. *)
let lookup_borrow_opt (ek : exploration_kind) (l : BorrowId.id) (ctx : eval_ctx)
    : g_borrow_content option =
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
        | AMutBorrow (bid, av) ->
            if bid = l then raise (FoundGBorrowContent (Abstract bc))
            else super#visit_AMutBorrow env bid av
        | ASharedBorrow bid ->
            if bid = l then raise (FoundGBorrowContent (Abstract bc))
            else super#visit_ASharedBorrow env bid
        | AIgnoredMutBorrow (_, _)
        | AEndedMutBorrow _
        | AEndedIgnoredMutBorrow
            { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedBorrow ->
            super#visit_aborrow_content env bc
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

    Raise an exception if no loan was found
*)
let lookup_borrow (meta : Meta.meta) (ek : exploration_kind) (l : BorrowId.id) (ctx : eval_ctx) :
    g_borrow_content =
  match lookup_borrow_opt ek l ctx with
  | None -> craise meta "Unreachable"
  | Some lc -> lc

(** Update a borrow content.

    The borrow is referred to by a borrow id.

    This is a helper function: it might break invariants.   
 *)
let update_borrow (meta : Meta.meta) (ek : exploration_kind) (l : BorrowId.id)
    (nbc : borrow_content) (ctx : eval_ctx) : eval_ctx =
  (* We use a reference to check that we update exactly one borrow: when updating
   * inside values, we check we don't update more than one borrow. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let update () : borrow_content =
    cassert (not !r) meta "TODO :  error message ";
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
  cassert !r meta "No borrow was updated";
  ctx

(** Update an abstraction borrow content.

    The borrow is referred to by a borrow id.

    This is a helper function: it might break invariants.     
 *)
let update_aborrow (meta : Meta.meta) (ek : exploration_kind) (l : BorrowId.id) (nv : avalue)
    (ctx : eval_ctx) : eval_ctx =
  (* We use a reference to check that we update exactly one borrow: when updating
   * inside values, we check we don't update more than one borrow. Then, upon
   * returning we check that we updated at least once. *)
  let r = ref false in
  let update () : avalue =
    cassert (not !r) meta "";
    r := true;
    nv
  in

  let obj =
    object
      inherit [_] map_eval_ctx as super

      method! visit_ABorrow env bc =
        match bc with
        | AMutBorrow (bid, av) ->
            if bid = l then update ()
            else ABorrow (super#visit_AMutBorrow env bid av)
        | ASharedBorrow bid ->
            if bid = l then update ()
            else ABorrow (super#visit_ASharedBorrow env bid)
        | AIgnoredMutBorrow _ | AEndedMutBorrow _ | AEndedSharedBorrow
        | AEndedIgnoredMutBorrow _ ->
            super#visit_ABorrow env bc
        | AProjSharedBorrow asb ->
            if borrow_in_asb l asb then update ()
            else ABorrow (super#visit_AProjSharedBorrow env asb)

      method! visit_abs env abs =
        if ek.enter_abs then super#visit_abs env abs else abs
    end
  in

  let ctx = obj#visit_eval_ctx () ctx in
  (* Check that we updated at least one borrow *)
  cassert !r meta "No borrow was updated";
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
    - if [false]: return the first loan we find, do not dive into borrowed values
 *)
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

let proj_borrows_intersects_proj_loans (meta : Meta.meta)
    (proj_borrows : RegionId.Set.t * symbolic_value * rty)
    (proj_loans : RegionId.Set.t * symbolic_value) : bool =
  let b_regions, b_sv, b_ty = proj_borrows in
  let l_regions, l_sv = proj_loans in
  if same_symbolic_id b_sv l_sv then
    projections_intersect meta l_sv.sv_ty l_regions b_ty b_regions
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
  | NonSharedProj of AbstractionId.id * rty
  | SharedProjs of (AbstractionId.id * rty) list

(** Lookup the aproj_borrows (including aproj_shared_borrows) over a
    symbolic value which intersect a given set of regions.
        
    [lookup_shared]: if [true] also explore projectors over shared values,
    otherwise ignore.
    
    This is a helper function.
*)
let lookup_intersecting_aproj_borrows_opt (meta : Meta.meta) (lookup_shared : bool)
    (regions : RegionId.Set.t) (sv : symbolic_value) (ctx : eval_ctx) :
    looked_up_aproj_borrows option =
  let found : looked_up_aproj_borrows option ref = ref None in
  let set_non_shared ((id, ty) : AbstractionId.id * rty) : unit =
    match !found with
    | None -> found := Some (NonSharedProj (id, ty))
    | Some _ -> craise meta "Unreachable"
  in
  let add_shared (x : AbstractionId.id * rty) : unit =
    match !found with
    | None -> found := Some (SharedProjs [ x ])
    | Some (SharedProjs pl) -> found := Some (SharedProjs (x :: pl))
    | Some (NonSharedProj _) -> craise meta "Unreachable"
  in
  let check_add_proj_borrows (is_shared : bool) abs sv' proj_ty =
    if
      proj_borrows_intersects_proj_loans
        meta
        (abs.regions, sv', proj_ty)
        (regions, sv)
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
        | Some (NonSharedProj _) -> craise meta "Unreachable"
        | _ -> ());
        (* Explore *)
        if lookup_shared then
          let abs = Option.get abs in
          match asb with
          | AsbBorrow _ -> ()
          | AsbProjReborrows (sv', proj_ty) ->
              let is_shared = true in
              check_add_proj_borrows is_shared abs sv' proj_ty
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
let lookup_intersecting_aproj_borrows_not_shared_opt (meta : Meta.meta) (regions : RegionId.Set.t)
    (sv : symbolic_value) (ctx : eval_ctx) : (AbstractionId.id * rty) option =
  let lookup_shared = false in
  match lookup_intersecting_aproj_borrows_opt meta lookup_shared regions sv ctx with
  | None -> None
  | Some (NonSharedProj (abs_id, rty)) -> Some (abs_id, rty)
  | _ -> craise meta "Unexpected"

(** Similar to {!lookup_intersecting_aproj_borrows_opt}, but updates the
    values.

    This is a helper function: it might break invariants.
 *)
let update_intersecting_aproj_borrows (meta : Meta.meta) (can_update_shared : bool)
    (update_shared : AbstractionId.id -> rty -> abstract_shared_borrows)
    (update_non_shared : AbstractionId.id -> rty -> aproj)
    (regions : RegionId.Set.t) (sv : symbolic_value) (ctx : eval_ctx) : eval_ctx
    =
  (* Small helpers for sanity checks *)
  let shared = ref None in
  let add_shared () =
    match !shared with None -> shared := Some true | Some b -> cassert b meta "TODO :  error message "
  in
  let set_non_shared () =
    match !shared with
    | None -> shared := Some false
    | Some _ -> craise meta "Found unexpected intersecting proj_borrows"
  in
  let check_proj_borrows is_shared abs sv' proj_ty =
    if
      proj_borrows_intersects_proj_loans
        meta
        (abs.regions, sv', proj_ty)
        (regions, sv)
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
        (match !shared with Some b -> cassert b meta "TODO :  error message " | _ -> ());
        (* Explore *)
        if can_update_shared then
          let abs = Option.get abs in
          let update (asb : abstract_shared_borrow) : abstract_shared_borrows =
            match asb with
            | AsbBorrow _ -> [ asb ]
            | AsbProjReborrows (sv', proj_ty) ->
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
  cassert (Option.is_some !shared) meta "Context was not updated at least once";
  (* Return *)
  ctx

(** Simply calls {!update_intersecting_aproj_borrows} to update a
    proj_borrows over a non-shared value.
    
    We check that we update *at least* one proj_borrows.

    This is a helper function: it might break invariants.
 *)
let update_intersecting_aproj_borrows_non_shared (meta : Meta.meta) (regions : RegionId.Set.t)
    (sv : symbolic_value) (nv : aproj) (ctx : eval_ctx) : eval_ctx =
  (* Small helpers *)
  let can_update_shared = false in
  let update_shared _ _ = craise meta "Unexpected" in
  let updated = ref false in
  let update_non_shared _ _ =
    (* We can update more than one borrow! *)
    updated := true;
    nv
  in
  (* Update *)
  let ctx =
    update_intersecting_aproj_borrows meta can_update_shared update_shared
      update_non_shared regions sv ctx
  in
  (* Check that we updated at least once *)
  cassert !updated meta "Not updated at least once";
  (* Return *)
  ctx

(** Simply calls {!update_intersecting_aproj_borrows} to remove the
    proj_borrows over shared values.

    This is a helper function: it might break invariants.
 *)
let remove_intersecting_aproj_borrows_shared (meta : Meta.meta) (regions : RegionId.Set.t)
    (sv : symbolic_value) (ctx : eval_ctx) : eval_ctx =
  (* Small helpers *)
  let can_update_shared = true in
  let update_shared _ _ = [] in
  let update_non_shared _ _ = craise meta "Unexpected" in
  (* Update *)
  update_intersecting_aproj_borrows meta can_update_shared update_shared
    update_non_shared regions sv ctx

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
    substitution and the list of given back values at the projector of
    loans where we perform the substitution (see the fields in {!Values.AProjLoans}).
    Note that the symbolic value at this place is necessarily equal to [sv],
    which is why we don't give it as parameters.
 *)
let update_intersecting_aproj_loans (meta : Meta.meta) (proj_regions : RegionId.Set.t)
    (proj_ty : rty) (sv : symbolic_value)
    (subst : abs -> (msymbolic_value * aproj) list -> aproj) (ctx : eval_ctx) :
    eval_ctx =
  (* *)
  cassert (ty_is_rty proj_ty) meta "proj_ty is not rty TODO";
  (* Small helpers for sanity checks *)
  let updated = ref false in
  let update abs local_given_back : aproj =
    (* Note that we can update more than once! *)
    updated := true;
    subst abs local_given_back
  in
  (* The visitor *)
  let obj =
    object
      inherit [_] map_eval_ctx as super
      method! visit_abs _ abs = super#visit_abs (Some abs) abs

      method! visit_aproj abs sproj =
        match sproj with
        | AProjBorrows _ | AEndedProjLoans _ | AEndedProjBorrows _
        | AIgnoredProjBorrows ->
            super#visit_aproj abs sproj
        | AProjLoans (sv', given_back) ->
            let abs = Option.get abs in
            if same_symbolic_id sv sv' then (
              cassert (sv.sv_ty = sv'.sv_ty) meta "TODO :  error message ";
              if
                projections_intersect meta proj_ty proj_regions sv'.sv_ty abs.regions
              then update abs given_back
              else super#visit_aproj (Some abs) sproj)
            else super#visit_aproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Check that we updated the context at least once *)
  cassert !updated meta "Context was not updated at least once";
  (* Return *)
  ctx

(** Helper function: lookup an {!constructor:Values.aproj.AProjLoans} by using an abstraction id and a
    symbolic value.

    We return the information from the looked up projector of loans. See the
    fields in {!constructor:Values.aproj.AProjLoans} (we don't return the symbolic value, because it
    is equal to [sv]).

    Sanity check: we check that there is exactly one projector which corresponds
    to the couple (abstraction id, symbolic value).
 *)
let lookup_aproj_loans (meta : Meta.meta) (abs_id : AbstractionId.id) (sv : symbolic_value)
    (ctx : eval_ctx) : (msymbolic_value * aproj) list =
  (* Small helpers for sanity checks *)
  let found = ref None in
  let set_found x =
    (* There is at most one projector which corresponds to the description *)
    cassert (Option.is_none !found) meta "More than one projecto corresponds to the description";
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
        | AProjBorrows _ | AEndedProjLoans _ | AEndedProjBorrows _
        | AIgnoredProjBorrows ->
            super#visit_aproj abs sproj
        | AProjLoans (sv', given_back) ->
            let abs = Option.get abs in
            cassert (abs.abs_id = abs_id) meta "TODO :  error message ";
            if sv'.sv_id = sv.sv_id then (
              cassert (sv' = sv) meta "TODO :  error message ";
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
let update_aproj_loans (meta : Meta.meta) (abs_id : AbstractionId.id) (sv : symbolic_value)
    (nproj : aproj) (ctx : eval_ctx) : eval_ctx =
  (* Small helpers for sanity checks *)
  let found = ref false in
  let update () =
    (* We update at most once *)
    cassert (not !found) meta "Updated more than once";
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
        | AProjBorrows _ | AEndedProjLoans _ | AEndedProjBorrows _
        | AIgnoredProjBorrows ->
            super#visit_aproj abs sproj
        | AProjLoans (sv', _) ->
            let abs = Option.get abs in
            cassert (abs.abs_id = abs_id) meta "TODO :  error message ";
            if sv'.sv_id = sv.sv_id then (
              cassert (sv' = sv) meta "TODO :  error message ";
              update ())
            else super#visit_aproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Sanity check *)
  cassert !found meta "TODO :  error message ";
  (* Return *)
  ctx

(** Helper function: might break invariants.

    Update a projector over borrows. The projector is identified by a symbolic
    value and an abstraction id.

    Sanity check: we check that there is exactly one projector which corresponds
    to the couple (abstraction id, symbolic value).
    
    TODO: factorize with {!update_aproj_loans}?
 *)
let update_aproj_borrows (meta : Meta.meta) (abs_id : AbstractionId.id) (sv : symbolic_value)
    (nproj : aproj) (ctx : eval_ctx) : eval_ctx =
  (* Small helpers for sanity checks *)
  let found = ref false in
  let update () =
    (* We update at most once *)
    cassert (not !found) meta "Updated more than once";
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
        | AProjLoans _ | AEndedProjLoans _ | AEndedProjBorrows _
        | AIgnoredProjBorrows ->
            super#visit_aproj abs sproj
        | AProjBorrows (sv', _proj_ty) ->
            let abs = Option.get abs in
            cassert (abs.abs_id = abs_id) meta "TODO :  error message ";
            if sv'.sv_id = sv.sv_id then (
              cassert (sv' = sv) meta "TODO :  error message ";
              update ())
            else super#visit_aproj (Some abs) sproj
    end
  in
  (* Apply *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Sanity check *)
  cassert !found meta "TODO :  error message ";
  (* Return *)
  ctx

(** Helper function: might break invariants.

    Converts an {!Values.aproj.AProjLoans} to an {!Values.aproj.AEndedProjLoans}. The projector is identified
    by a symbolic value and an abstraction id.
 *)
let update_aproj_loans_to_ended (meta : Meta.meta) (abs_id : AbstractionId.id)
    (sv : symbolic_value) (ctx : eval_ctx) : eval_ctx =
  (* Lookup the projector of loans *)
  let given_back = lookup_aproj_loans meta abs_id sv ctx in
  (* Create the new value for the projector *)
  let nproj = AEndedProjLoans (sv, given_back) in
  (* Insert it *)
  let ctx =  update_aproj_loans meta abs_id sv nproj ctx in
  (* Return *)
  ctx

let no_aproj_over_symbolic_in_context (meta : Meta.meta)  (sv : symbolic_value) (ctx : eval_ctx) :
    unit =
  (* The visitor *)
  let obj =
    object
      inherit [_] iter_eval_ctx as super

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
  with Found -> craise meta "update_aproj_loans_to_ended: failed"

(** Helper function

    Return the loan (aloan, loan, proj_loans over a symbolic value) we find
    in an abstraction, if there is.
    
    **Remark:** we don't take the *ignored* mut/shared loans into account.
 *)
let get_first_non_ignored_aloan_in_abstraction (meta : Meta.meta)  (abs : abs) :
    borrow_ids_or_symbolic_value option =
  (* Explore to find a loan *)
  let obj =
    object
      inherit [_] iter_abs as super

      method! visit_aloan_content env lc =
        match lc with
        | AMutLoan (bid, _) -> raise (FoundBorrowIds (Borrow bid))
        | ASharedLoan (bids, _, _) -> raise (FoundBorrowIds (Borrows bids))
        | AEndedMutLoan { given_back = _; child = _; given_back_meta = _ }
        | AEndedSharedLoan (_, _) ->
            super#visit_aloan_content env lc
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
            craise meta "Unreachable"
        | VSharedLoan (bids, _) -> raise (FoundBorrowIds (Borrows bids))

      method! visit_aproj env sproj =
        (match sproj with
        | AProjBorrows (_, _)
        | AEndedProjLoans _ | AEndedProjBorrows _ | AIgnoredProjBorrows ->
            ()
        | AProjLoans (sv, _) -> raise (ValuesUtils.FoundSymbolicValue sv));
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
  | ValuesUtils.FoundSymbolicValue sv ->
      (* There are loan projections over symbolic values *)
      Some (SymbolicValue sv)

let lookup_shared_value_opt (meta : Meta.meta) (ctx : eval_ctx) (bid : BorrowId.id) :
    typed_value option =
  match lookup_loan_opt meta ek_all bid ctx with
  | None -> None
  | Some (_, lc) -> (
      match lc with
      | Concrete (VSharedLoan (_, sv)) | Abstract (ASharedLoan (_, sv, _)) ->
          Some sv
      | _ -> None)

let lookup_shared_value (meta : Meta.meta) (ctx : eval_ctx) (bid : BorrowId.id) : typed_value =
  Option.get (lookup_shared_value_opt meta ctx bid)
