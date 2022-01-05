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
open Utils

(** Some utilities *)

let eval_ctx_to_string = Print.Contexts.eval_ctx_to_string

let ety_to_string = Print.EvalCtxCfimAst.ety_to_string

let typed_value_to_string = Print.EvalCtxCfimAst.typed_value_to_string

let place_to_string = Print.EvalCtxCfimAst.place_to_string

let operand_to_string = Print.EvalCtxCfimAst.operand_to_string

let statement_to_string ctx =
  Print.EvalCtxCfimAst.statement_to_string ctx "" "  "

let same_symbolic_id (sv0 : V.symbolic_value) (sv1 : V.symbolic_value) : bool =
  sv0.V.sv_id = sv1.V.sv_id

(* TODO: move *)
let mk_var (index : V.VarId.id) (name : string option) (var_ty : T.ety) : A.var
    =
  { A.index; name; var_ty }

(** Small helper *)
let mk_place_from_var_id (var_id : V.VarId.id) : E.place =
  { var_id; projection = [] }

(** Deconstruct a type of the form `Box<T>` to retrieve the `T` inside *)
let ty_get_box (box_ty : T.ety) : T.ety =
  match box_ty with
  | T.Adt (T.Assumed T.Box, [], [ boxed_ty ]) -> boxed_ty
  | _ -> failwith "Not a boxed type"

(** Deconstruct a type of the form `&T` or `&mut T` to retrieve the `T` (and
    the borrow kind, etc.)
 *)
let ty_get_ref (ty : T.ety) : T.erased_region * T.ety * T.ref_kind =
  match ty with
  | T.Ref (r, ty, ref_kind) -> (r, ty, ref_kind)
  | _ -> failwith "Not a ref type"

let mk_ref_ty (r : 'r) (ty : 'r T.ty) (ref_kind : T.ref_kind) : 'r T.ty =
  T.Ref (r, ty, ref_kind)

(** Make a box type *)
let mk_box_ty (ty : 'r T.ty) : 'r T.ty = T.Adt (T.Assumed T.Box, [], [ ty ])

(** Box a value *)
let mk_box_value (v : V.typed_value) : V.typed_value =
  let box_ty = mk_box_ty v.V.ty in
  let box_v = V.Adt { variant_id = None; field_values = [ v ] } in
  mk_typed_value box_ty box_v

(** Create a fresh symbolic proj comp *)
let mk_fresh_symbolic_proj_comp (ended_regions : T.RegionId.set_t) (ty : T.rty)
    (ctx : C.eval_ctx) : C.eval_ctx * V.symbolic_proj_comp =
  let ctx, sv_id = C.fresh_symbolic_value_id ctx in
  let svalue = { V.sv_id; V.sv_ty = ty } in
  let sv = { V.svalue; rset_ended = ended_regions } in
  (ctx, sv)

(** Create a fresh symbolic value (as a complementary projector) *)
let mk_fresh_symbolic_proj_comp_value (ended_regions : T.RegionId.set_t)
    (ty : T.rty) (ctx : C.eval_ctx) : C.eval_ctx * V.typed_value =
  let ctx, sv = mk_fresh_symbolic_proj_comp ended_regions ty ctx in
  let value : V.value = V.Symbolic sv in
  let ty : T.ety = Subst.erase_regions ty in
  let sv : V.typed_value = { V.value; ty } in
  (ctx, sv)

let mk_typed_value_from_proj_comp (sv : V.symbolic_proj_comp) : V.typed_value =
  let ty = Subst.erase_regions sv.V.svalue.V.sv_ty in
  let value = V.Symbolic sv in
  { V.value; ty }

let mk_typed_value_from_symbolic_value (svalue : V.symbolic_value) :
    V.typed_value =
  let spc = { V.svalue; rset_ended = T.RegionId.Set.empty } in
  mk_typed_value_from_proj_comp spc

let mk_aproj_loans_from_proj_comp (sv : V.symbolic_proj_comp) : V.typed_avalue =
  let ty = sv.V.svalue.V.sv_ty in
  let proj = V.AProjLoans sv.V.svalue in
  let value = V.ASymbolic proj in
  { V.value; ty }

(** TODO: move *)
let borrow_is_asb (bid : V.BorrowId.id) (asb : V.abstract_shared_borrow) : bool
    =
  match asb with
  | V.AsbBorrow bid' -> bid' = bid
  | V.AsbProjReborrows _ -> false

(** TODO: move *)
let borrow_in_asb (bid : V.BorrowId.id) (asb : V.abstract_shared_borrows) : bool
    =
  List.exists (borrow_is_asb bid) asb

(** TODO: move *)
let remove_borrow_from_asb (bid : V.BorrowId.id)
    (asb : V.abstract_shared_borrows) : V.abstract_shared_borrows =
  let removed = ref 0 in
  let asb =
    List.filter
      (fun asb ->
        if not (borrow_is_asb bid asb) then true
        else (
          removed := !removed + 1;
          false))
      asb
  in
  assert (!removed = 1);
  asb

(* TODO: cleanup this a bit, once we have a better understanding about what we need *)
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

(** We sometimes need to return a value whose type may vary depending on
    whether we find it in a "concrete" value or an abstraction (ex.: loan
    contents when we perform environment lookups by using borrow ids) *)
type ('a, 'b) concrete_or_abs = Concrete of 'a | Abstract of 'b

type g_loan_content = (V.loan_content, V.aloan_content) concrete_or_abs
(** Generic loan content: concrete or abstract *)

type g_borrow_content = (V.borrow_content, V.aborrow_content) concrete_or_abs
(** Generic borrow content: concrete or abstract *)

type abs_or_var_id = AbsId of V.AbstractionId.id | VarId of V.VarId.id

exception FoundBorrowContent of V.borrow_content
(** Utility exception *)

exception FoundLoanContent of V.loan_content
(** Utility exception *)

exception FoundABorrowContent of V.aborrow_content
(** Utility exception *)

exception FoundGBorrowContent of g_borrow_content
(** Utility exception *)

exception FoundGLoanContent of g_loan_content
(** Utility exception *)

(** Check if a value contains a borrow *)
let borrows_in_value (v : V.typed_value) : bool =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_borrow_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if a value contains inactivated mutable borrows *)
let inactivated_in_value (v : V.typed_value) : bool =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_InactivatedMutBorrow _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Check if a value contains a loan *)
let loans_in_value (v : V.typed_value) : bool =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_loan_content _env _ = raise Found
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

let symbolic_value_id_in_ctx (sv_id : V.SymbolicValueId.id) (ctx : C.eval_ctx) :
    bool =
  let obj =
    object
      inherit [_] C.iter_eval_ctx

      method! visit_Symbolic _ sv =
        if sv.V.svalue.V.sv_id = sv_id then raise Found else ()

      method! visit_ASymbolic _ aproj =
        match aproj with
        | AProjLoans sv | AProjBorrows (sv, _) ->
            if sv.V.sv_id = sv_id then raise Found else ()

      method! visit_abstract_shared_borrows _ asb =
        let visit (asb : V.abstract_shared_borrow) : unit =
          match asb with
          | V.AsbBorrow _ -> ()
          | V.AsbProjReborrows (sv, _) ->
              if sv.V.sv_id = sv_id then raise Found else ()
        in
        List.iter visit asb
    end
  in
  (* We use exceptions *)
  try
    obj#visit_eval_ctx () ctx;
    false
  with Found -> true

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

(** TODO: move to InterpreterSymbolic or sth *)
type symbolic_expansion =
  | SeConcrete of V.constant_value
  | SeAdt of (T.VariantId.id option * V.symbolic_proj_comp list)
  | SeMutRef of V.BorrowId.id * V.symbolic_proj_comp
  | SeSharedRef of V.BorrowId.set_t * V.symbolic_proj_comp
