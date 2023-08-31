module T = Types
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module A = LlbcAst
module L = Logging
open Utils
open TypesUtils
module PA = Print.EvalCtxLlbcAst
open Cps

(** Some utilities *)

(** Auxiliary function - call a function which requires a continuation,
    and return the let context given to the continuation *)
let get_cf_ctx_no_synth (f : cm_fun) (ctx : C.eval_ctx) : C.eval_ctx =
  let nctx = ref None in
  let cf ctx =
    assert (!nctx = None);
    nctx := Some ctx;
    None
  in
  let _ = f cf ctx in
  Option.get !nctx

let eval_ctx_to_string_no_filter = Print.Contexts.eval_ctx_to_string_no_filter
let eval_ctx_to_string = Print.Contexts.eval_ctx_to_string
let ety_to_string = PA.ety_to_string
let rty_to_string = PA.rty_to_string
let symbolic_value_to_string = PA.symbolic_value_to_string
let borrow_content_to_string = PA.borrow_content_to_string
let loan_content_to_string = PA.loan_content_to_string
let aborrow_content_to_string = PA.aborrow_content_to_string
let aloan_content_to_string = PA.aloan_content_to_string
let aproj_to_string = PA.aproj_to_string
let typed_value_to_string = PA.typed_value_to_string
let typed_avalue_to_string = PA.typed_avalue_to_string
let place_to_string = PA.place_to_string
let operand_to_string = PA.operand_to_string
let statement_to_string ctx = PA.statement_to_string ctx "" "  "
let statement_to_string_with_tab ctx = PA.statement_to_string ctx "  " "  "
let env_elem_to_string ctx = PA.env_elem_to_string ctx "" "  "
let env_to_string ctx env = eval_ctx_to_string { ctx with env }
let abs_to_string ctx = PA.abs_to_string ctx "" "  "

let same_symbolic_id (sv0 : V.symbolic_value) (sv1 : V.symbolic_value) : bool =
  sv0.V.sv_id = sv1.V.sv_id

let mk_var (index : E.VarId.id) (name : string option) (var_ty : T.ety) : A.var
    =
  { A.index; name; var_ty }

(** Small helper - TODO: move *)
let mk_place_from_var_id (var_id : E.VarId.id) : E.place =
  { var_id; projection = [] }

(** Create a fresh symbolic value *)
let mk_fresh_symbolic_value (sv_kind : V.sv_kind) (ty : T.rty) :
    V.symbolic_value =
  let sv_id = C.fresh_symbolic_value_id () in
  let svalue = { V.sv_kind; V.sv_id; V.sv_ty = ty } in
  svalue

(** Create a fresh symbolic value *)
let mk_fresh_symbolic_typed_value (sv_kind : V.sv_kind) (rty : T.rty) :
    V.typed_value =
  let ty = Subst.erase_regions rty in
  (* Generate the fresh a symbolic value *)
  let value = mk_fresh_symbolic_value sv_kind rty in
  let value = V.Symbolic value in
  { V.value; V.ty }

(** Create a fresh symbolic value *)
let mk_fresh_symbolic_typed_value_from_ety (sv_kind : V.sv_kind) (ety : T.ety) :
    V.typed_value =
  let ty = TypesUtils.ety_no_regions_to_rty ety in
  mk_fresh_symbolic_typed_value sv_kind ty

(** Create a typed value from a symbolic value. *)
let mk_typed_value_from_symbolic_value (svalue : V.symbolic_value) :
    V.typed_value =
  let av = V.Symbolic svalue in
  let av : V.typed_value =
    { V.value = av; V.ty = Subst.erase_regions svalue.V.sv_ty }
  in
  av

(** Create a loans projector value from a symbolic value.
    
    Checks if the projector will actually project some regions. If not,
    returns {!V.AIgnored} ([_]).
    
    TODO: update to handle 'static
 *)
let mk_aproj_loans_value_from_symbolic_value (regions : T.RegionId.Set.t)
    (svalue : V.symbolic_value) : V.typed_avalue =
  if ty_has_regions_in_set regions svalue.sv_ty then
    let av = V.ASymbolic (V.AProjLoans (svalue, [])) in
    let av : V.typed_avalue = { V.value = av; V.ty = svalue.V.sv_ty } in
    av
  else { V.value = V.AIgnored; ty = svalue.V.sv_ty }

(** Create a borrows projector from a symbolic value *)
let mk_aproj_borrows_from_symbolic_value (proj_regions : T.RegionId.Set.t)
    (svalue : V.symbolic_value) (proj_ty : T.rty) : V.aproj =
  if ty_has_regions_in_set proj_regions proj_ty then
    V.AProjBorrows (svalue, proj_ty)
  else V.AIgnoredProjBorrows

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

(** We sometimes need to return a value whose type may vary depending on
    whether we find it in a "concrete" value or an abstraction (ex.: loan
    contents when we perform environment lookups by using borrow ids)

    TODO: change the name "abstract"
 *)
type ('a, 'b) concrete_or_abs = Concrete of 'a | Abstract of 'b
[@@deriving show]

(** Generic loan content: concrete or abstract *)
type g_loan_content = (V.loan_content, V.aloan_content) concrete_or_abs
[@@deriving show]

(** Generic borrow content: concrete or abstract *)
type g_borrow_content = (V.borrow_content, V.aborrow_content) concrete_or_abs
[@@deriving show]

type abs_or_var_id =
  | AbsId of V.AbstractionId.id
  | VarId of E.VarId.id
  | DummyVarId of C.DummyVarId.id

(** Utility exception *)
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
exception FoundAProjBorrows of V.symbolic_value * T.rty

let symbolic_value_id_in_ctx (sv_id : V.SymbolicValueId.id) (ctx : C.eval_ctx) :
    bool =
  let obj =
    object
      inherit [_] C.iter_eval_ctx as super

      method! visit_Symbolic _ sv =
        if sv.V.sv_id = sv_id then raise Found else ()

      method! visit_aproj env aproj =
        (match aproj with
        | AProjLoans (sv, _) | AProjBorrows (sv, _) ->
            if sv.V.sv_id = sv_id then raise Found else ()
        | AEndedProjLoans _ | AEndedProjBorrows _ | AIgnoredProjBorrows -> ());
        super#visit_aproj env aproj

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

(** Check that a symbolic value doesn't contain ended regions.

    Note that we don't check that the set of ended regions is empty: we
    check that the set of ended regions doesn't intersect the set of
    regions used in the type (this is more general).
*)
let symbolic_value_has_ended_regions (ended_regions : T.RegionId.Set.t)
    (s : V.symbolic_value) : bool =
  let regions = rty_regions s.V.sv_ty in
  not (T.RegionId.Set.disjoint regions ended_regions)

(** Check if a {!type:V.value} contains [⊥].

    Note that this function is very general: it also checks wether
    symbolic values contain already ended regions.
 *)
let bottom_in_value (ended_regions : T.RegionId.Set.t) (v : V.typed_value) :
    bool =
  let obj =
    object
      inherit [_] V.iter_typed_value
      method! visit_Bottom _ = raise Found

      method! visit_symbolic_value _ s =
        if symbolic_value_has_ended_regions ended_regions s then raise Found
        else ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

let value_has_ret_symbolic_value_with_borrow_under_mut (ctx : C.eval_ctx)
    (v : V.typed_value) : bool =
  let obj =
    object
      inherit [_] V.iter_typed_value

      method! visit_symbolic_value _ s =
        match s.sv_kind with
        | V.FunCallRet | V.LoopOutput | V.LoopJoin ->
            if ty_has_borrow_under_mut ctx.type_context.type_infos s.sv_ty then
              raise Found
            else ()
        | V.SynthInput | V.SynthInputGivenBack | V.FunCallGivenBack
        | V.SynthRetGivenBack | V.Global | V.LoopGivenBack | V.Aggregate
        | V.ConstGeneric ->
            ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Return the place used in an rvalue, if that makes sense.
    This is used to compute meta-data, to find pretty names.
 *)
let rvalue_get_place (rv : E.rvalue) : E.place option =
  match rv with
  | Use (Copy p | Move p) -> Some p
  | Use (Constant _) -> None
  | RvRef (p, _) -> Some p
  | UnaryOp _ | BinaryOp _ | Global _ | Discriminant _ | Aggregate _ -> None

(** See {!ValuesUtils.symbolic_value_has_borrows} *)
let symbolic_value_has_borrows (ctx : C.eval_ctx) (sv : V.symbolic_value) : bool
    =
  ValuesUtils.symbolic_value_has_borrows ctx.type_context.type_infos sv

(** See {!ValuesUtils.value_has_borrows}. *)
let value_has_borrows (ctx : C.eval_ctx) (v : V.value) : bool =
  ValuesUtils.value_has_borrows ctx.type_context.type_infos v

(** See {!ValuesUtils.value_has_loans_or_borrows}. *)
let value_has_loans_or_borrows (ctx : C.eval_ctx) (v : V.value) : bool =
  ValuesUtils.value_has_loans_or_borrows ctx.type_context.type_infos v

(** See {!ValuesUtils.value_has_loans}. *)
let value_has_loans (v : V.value) : bool = ValuesUtils.value_has_loans v

(** See {!compute_typed_value_ids}, {!compute_context_ids}, etc. *)
type ids_sets = {
  aids : V.AbstractionId.Set.t;
  blids : V.BorrowId.Set.t;  (** All the borrow/loan ids *)
  borrow_ids : V.BorrowId.Set.t;  (** Only the borrow ids *)
  loan_ids : V.BorrowId.Set.t;  (** Only the loan ids *)
  dids : C.DummyVarId.Set.t;
  rids : T.RegionId.Set.t;
  sids : V.SymbolicValueId.Set.t;
}
[@@deriving show]

(** See {!compute_typed_value_ids}, {!compute_context_ids}, etc.

    TODO: there misses information.
 *)
type ids_to_values = {
  sids_to_values : V.symbolic_value V.SymbolicValueId.Map.t;
}

let compute_ids () =
  let blids = ref V.BorrowId.Set.empty in
  let borrow_ids = ref V.BorrowId.Set.empty in
  let loan_ids = ref V.BorrowId.Set.empty in
  let aids = ref V.AbstractionId.Set.empty in
  let dids = ref C.DummyVarId.Set.empty in
  let rids = ref T.RegionId.Set.empty in
  let sids = ref V.SymbolicValueId.Set.empty in
  let sids_to_values = ref V.SymbolicValueId.Map.empty in

  let get_ids () =
    {
      aids = !aids;
      blids = !blids;
      borrow_ids = !borrow_ids;
      loan_ids = !loan_ids;
      dids = !dids;
      rids = !rids;
      sids = !sids;
    }
  in
  let get_ids_to_values () = { sids_to_values = !sids_to_values } in
  let obj =
    object
      inherit [_] C.iter_eval_ctx as super
      method! visit_dummy_var_id _ did = dids := C.DummyVarId.Set.add did !dids

      method! visit_borrow_id _ id =
        blids := V.BorrowId.Set.add id !blids;
        borrow_ids := V.BorrowId.Set.add id !borrow_ids

      method! visit_loan_id _ id =
        blids := V.BorrowId.Set.add id !blids;
        loan_ids := V.BorrowId.Set.add id !loan_ids

      method! visit_abstraction_id _ id =
        aids := V.AbstractionId.Set.add id !aids

      method! visit_region_id _ id = rids := T.RegionId.Set.add id !rids

      method! visit_symbolic_value env sv =
        sids := V.SymbolicValueId.Set.add sv.sv_id !sids;
        sids_to_values := V.SymbolicValueId.Map.add sv.sv_id sv !sids_to_values;
        super#visit_symbolic_value env sv

      method! visit_symbolic_value_id _ id =
        (* TODO: can we get there without going through [visit_symbolic_value] first? *)
        sids := V.SymbolicValueId.Set.add id !sids
    end
  in
  (obj, get_ids, get_ids_to_values)

(** Compute the sets of ids found in a list of typed values. *)
let compute_typed_values_ids (xl : V.typed_value list) :
    ids_sets * ids_to_values =
  let compute, get_ids, get_ids_to_values = compute_ids () in
  List.iter (compute#visit_typed_value ()) xl;
  (get_ids (), get_ids_to_values ())

(** Compute the sets of ids found in a typed value. *)
let compute_typed_value_ids (x : V.typed_value) : ids_sets * ids_to_values =
  compute_typed_values_ids [ x ]

(** Compute the sets of ids found in a list of abstractions. *)
let compute_absl_ids (xl : V.abs list) : ids_sets * ids_to_values =
  let compute, get_ids, get_ids_to_values = compute_ids () in
  List.iter (compute#visit_abs ()) xl;
  (get_ids (), get_ids_to_values ())

(** Compute the sets of ids found in an abstraction. *)
let compute_abs_ids (x : V.abs) : ids_sets * ids_to_values =
  compute_absl_ids [ x ]

(** Compute the sets of ids found in an environment. *)
let compute_env_ids (x : C.env) : ids_sets * ids_to_values =
  let compute, get_ids, get_ids_to_values = compute_ids () in
  compute#visit_env () x;
  (get_ids (), get_ids_to_values ())

(** Compute the sets of ids found in an environment element. *)
let compute_env_elem_ids (x : C.env_elem) : ids_sets * ids_to_values =
  compute_env_ids [ x ]

(** Compute the sets of ids found in a list of contexts. *)
let compute_contexts_ids (ctxl : C.eval_ctx list) : ids_sets * ids_to_values =
  let compute, get_ids, get_ids_to_values = compute_ids () in
  List.iter (compute#visit_eval_ctx ()) ctxl;
  (get_ids (), get_ids_to_values ())

(** Compute the sets of ids found in a context. *)
let compute_context_ids (ctx : C.eval_ctx) : ids_sets * ids_to_values =
  compute_contexts_ids [ ctx ]
