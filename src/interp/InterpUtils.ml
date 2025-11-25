open Types
open Values
open Expressions
open Contexts
open LlbcAst
open Utils
open TypesUtils
open ValuesUtils

(* TODO: we should probably rename the file to ContextsUtils *)

(** The local logger *)
let log = Logging.interp_log

(** Some utilities *)

let eval_ctx_to_string = Print.Contexts.eval_ctx_to_string
let name_to_string = Print.EvalCtx.name_to_string
let symbolic_value_to_string = Print.EvalCtx.symbolic_value_to_string

let symbolic_value_id_to_pretty_string =
  Print.Values.symbolic_value_id_to_pretty_string

let borrow_content_to_string = Print.EvalCtx.borrow_content_to_string
let loan_content_to_string = Print.EvalCtx.loan_content_to_string
let aborrow_content_to_string = Print.EvalCtx.aborrow_content_to_string
let eborrow_content_to_string = Print.EvalCtx.eborrow_content_to_string
let aloan_content_to_string = Print.EvalCtx.aloan_content_to_string
let eloan_content_to_string = Print.EvalCtx.eloan_content_to_string
let aproj_to_string = Print.EvalCtx.aproj_to_string
let eproj_to_string = Print.EvalCtx.eproj_to_string
let tvalue_to_string = Print.EvalCtx.tvalue_to_string
let tavalue_to_string = Print.EvalCtx.tavalue_to_string
let tevalue_to_string = Print.EvalCtx.tevalue_to_string
let tepat_to_string = Print.EvalCtx.tepat_to_string
let place_to_string = Print.EvalCtx.place_to_string
let operand_to_string = Print.EvalCtx.operand_to_string
let fun_sig_to_string = Print.EvalCtx.fun_sig_to_string
let inst_fun_sig_to_string = Print.EvalCtx.inst_fun_sig_to_string
let ty_to_string = Print.EvalCtx.ty_to_string
let constant_expr_to_string = Print.EvalCtx.constant_expr_to_string
let unop_to_string = Print.EvalCtx.unop_to_string
let binop_to_string = Print.Expressions.binop_to_string
let generic_args_to_string = Print.EvalCtx.generic_args_to_string
let trait_ref_to_string = Print.EvalCtx.trait_ref_to_string
let trait_impl_ref_to_string = Print.EvalCtx.trait_impl_ref_to_string
let trait_decl_ref_to_string = Print.EvalCtx.trait_decl_ref_to_string

let fn_ptr_to_string (ctx : eval_ctx) (fn_ptr : fn_ptr) : string =
  let env = Print.Contexts.eval_ctx_to_fmt_env ctx in
  Print.Types.fn_ptr_to_string env fn_ptr

let trait_decl_ref_region_binder_to_string =
  Print.EvalCtx.trait_decl_ref_region_binder_to_string

let fn_ptr_kind_to_string = Print.EvalCtx.fn_ptr_kind_to_string
let fun_decl_to_string = Print.EvalCtx.fun_decl_to_string
let call_to_string = Print.EvalCtx.call_to_string

let trait_impl_to_string ctx =
  Print.EvalCtx.trait_impl_to_string
    { ctx with type_vars = []; const_generic_vars = [] }

let statement_to_string ctx = Print.EvalCtx.statement_to_string ctx "" "  "

let statement_to_string_with_tab ctx =
  Print.EvalCtx.statement_to_string ctx "  " "  "

let env_elem_to_string span ctx =
  Print.EvalCtx.env_elem_to_string ~span:(Some span) ctx "" "  "

let env_to_string span ctx ?(filter = true) env =
  eval_ctx_to_string ~span:(Some span) { ctx with env } ~filter

let abs_to_string span ?(with_ended = false) ctx =
  Print.EvalCtx.abs_to_string ~span:(Some span) ~with_ended ctx "" "  "

let abs_cont_to_string span ?(with_ended = true) ?(indent = "")
    ?(indent_incr = "  ") ctx =
  Print.EvalCtx.abs_cont_to_string ~span:(Some span) ~with_ended ctx indent
    indent_incr

let same_symbolic_id (sv0 : symbolic_value) (sv1 : symbolic_value) : bool =
  sv0.sv_id = sv1.sv_id

let mk_var (index : LocalId.id) (name : string option) (local_ty : ty) : local =
  { index; name; local_ty }

(** Small helper - TODO: move *)
let mk_place_from_var_id (ctx : eval_ctx) (span : Meta.span)
    (var_id : LocalId.id) : place =
  let _, typed_val = env_lookup_var span ctx.env var_id in
  { kind = PlaceLocal var_id; ty = typed_val.ty }

(** Create a fresh symbolic value *)
let mk_fresh_symbolic_value_opt_span (span : Meta.span option)
    fresh_symbolic_value_id (ty : ty) : symbolic_value =
  (* Sanity check *)
  [%sanity_check_opt_span] span (ty_is_rty ty);
  let sv_id = fresh_symbolic_value_id () in
  let svalue = { sv_id; sv_ty = ty } in
  svalue

let mk_fresh_symbolic_value span (ctx : eval_ctx) =
  mk_fresh_symbolic_value_opt_span (Some span) ctx.fresh_symbolic_value_id

let mk_fresh_symbolic_value_from_no_regions_ty (span : Meta.span) ctx (ty : ty)
    : symbolic_value =
  [%sanity_check] span (ty_no_regions ty);
  mk_fresh_symbolic_value span ctx ty

(** Create a fresh symbolic value *)
let mk_fresh_symbolic_tvalue_opt_span (span : Meta.span option) ctx (rty : ty) :
    tvalue =
  [%sanity_check_opt_span] span (ty_is_rty rty);
  let ty = Substitute.erase_regions rty in
  (* Generate the fresh a symbolic value *)
  let value = mk_fresh_symbolic_value_opt_span span ctx rty in
  let value = VSymbolic value in
  { value; ty }

let mk_fresh_symbolic_tvalue span ctx =
  mk_fresh_symbolic_tvalue_opt_span (Some span) ctx.fresh_symbolic_value_id

let mk_fresh_symbolic_tvalue_from_no_regions_ty (span : Meta.span) ctx (ty : ty)
    : tvalue =
  [%sanity_check] span (ty_no_regions ty);
  mk_fresh_symbolic_tvalue span ctx ty

let symbolic_tvalue_get_id file line (span : Meta.span) (v : tvalue) =
  match v.value with
  | VSymbolic v -> v.sv_id
  | _ -> Errors.internal_error file line span

let get_symbolic_tvalue (span : Meta.span) (v : tvalue) : symbolic_value =
  match v.value with
  | VSymbolic v -> v
  | _ -> [%internal_error] span

(** Create a loans projector value from a symbolic value.

    Checks if the projector will actually project some regions. If not, returns
    {!Values.AIgnored} ([_]).

    TODO: update to handle 'static *)
let mk_aproj_loans_value_from_symbolic_value (proj_regions : RegionId.Set.t)
    (svalue : symbolic_value) (proj_ty : ty) : tavalue =
  if ty_has_regions_in_set proj_regions proj_ty then
    let av =
      ASymbolic
        ( PNone,
          AProjLoans
            {
              proj = { sv_id = svalue.sv_id; proj_ty };
              consumed = [];
              borrows = [];
            } )
    in
    let av : tavalue = { value = av; ty = svalue.sv_ty } in
    av
  else
    {
      value = AIgnored (Some (mk_tvalue_from_symbolic_value svalue));
      ty = svalue.sv_ty;
    }

let mk_eproj_loans_value_from_symbolic_value
    (type_infos : TypesAnalysis.type_infos) (proj_regions : RegionId.Set.t)
    (svalue : symbolic_value) (proj_ty : ty) : tevalue =
  if ty_has_mut_borrow_for_region_in_set type_infos proj_regions proj_ty then
    let av =
      ESymbolic
        ( PNone,
          EProjLoans
            {
              proj = { sv_id = svalue.sv_id; proj_ty };
              consumed = [];
              borrows = [];
            } )
    in
    let av : tevalue = { value = av; ty = svalue.sv_ty } in
    av
  else { value = EIgnored; ty = svalue.sv_ty }

(** Create a borrows projector from a symbolic value *)
let mk_aproj_borrows_from_symbolic_value (span : Meta.span)
    (proj_regions : RegionId.Set.t) (svalue : symbolic_value) (proj_ty : ty) :
    aproj =
  [%sanity_check] span (ty_is_rty proj_ty);
  if ty_has_regions_in_set proj_regions proj_ty then
    AProjBorrows { proj = { sv_id = svalue.sv_id; proj_ty }; loans = [] }
  else AEmpty

let mk_eproj_borrows_from_symbolic_value (span : Meta.span)
    (proj_regions : RegionId.Set.t) (svalue : symbolic_value) (proj_ty : ty) :
    eproj =
  [%sanity_check] span (ty_is_rty proj_ty);
  if ty_has_regions_in_set proj_regions proj_ty then
    EProjBorrows { proj = { sv_id = svalue.sv_id; proj_ty }; loans = [] }
  else EEmpty

(** TODO: move *)
let borrow_is_asb (bid : SharedBorrowId.id) (asb : abstract_shared_borrow) :
    bool =
  match asb with
  | AsbBorrow (_, bid') -> bid' = bid
  | AsbProjReborrows _ -> false

(** TODO: move *)
let borrow_in_asb (bid : SharedBorrowId.id) (asb : abstract_shared_borrows) :
    bool =
  List.exists (borrow_is_asb bid) asb

(** TODO: move *)
let remove_borrow_from_asb (span : Meta.span) (bid : SharedBorrowId.id)
    (asb : abstract_shared_borrows) : abstract_shared_borrows =
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
  [%sanity_check] span (!removed = 1);
  asb

(** We sometimes need to return a value whose type may vary depending on whether
    we find it in a "concrete" value or an abstraction (ex.: loan contents when
    we perform environment lookups by using borrow ids)

    TODO: change the name "abstract" *)
type ('a, 'b) concrete_or_abs = Concrete of 'a | Abstract of 'b
[@@deriving show]

(** Generic loan content: concrete or abstract *)
type g_loan_content = (loan_content, aloan_content) concrete_or_abs
[@@deriving show]

(** Generic borrow content: concrete or abstract *)
type g_borrow_content = (borrow_content, aborrow_content) concrete_or_abs
[@@deriving show]

type abs_or_var_id =
  | AbsId of AbsId.id
  | LocalId of LocalId.id
  | DummyVarId of DummyVarId.id

(** Utility exception *)
exception FoundBorrowContent of borrow_content

(** Utility exception *)
exception FoundLoanContent of loan_content

(** Utility exception *)
exception FoundABorrowContent of aborrow_content

(** Utility exception *)
exception FoundGBorrowContent of g_borrow_content

(** Utility exception *)
exception FoundGLoanContent of g_loan_content

(** Utility exception *)
exception FoundEBorrowContent of eborrow_content

(** Utility exception *)
exception FoundAProjBorrows of aproj_borrows

(** Utility exception *)
exception FoundAProjLoans of aproj_loans

exception FoundAbsProj of abs_id * symbolic_value_id

let symbolic_value_id_in_ctx (sv_id : SymbolicValueId.id) (ctx : eval_ctx) :
    bool =
  let obj =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_VSymbolic _ sv =
        if sv.sv_id = sv_id then raise Found else ()

      method! visit_aproj env aproj =
        (match aproj with
        | AProjLoans { proj; _ } | AProjBorrows { proj; _ } ->
            if proj.sv_id = sv_id then raise Found else ()
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty -> ());
        super#visit_aproj env aproj

      method! visit_abstract_shared_borrows _ asb =
        let visit (asb : abstract_shared_borrow) : unit =
          match asb with
          | AsbBorrow _ -> ()
          | AsbProjReborrows proj ->
              if proj.sv_id = sv_id then raise Found else ()
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

    Note that we don't check that the set of ended regions is empty: we check
    that the set of ended regions doesn't intersect the set of regions used in
    the type (this is more general). *)
let symbolic_value_has_ended_regions (ended_regions : RegionId.Set.t)
    (s : symbolic_value) : bool =
  let regions = ty_regions s.sv_ty in
  not (RegionId.Set.disjoint regions ended_regions)

let region_is_owned (abs : abs) (r : region) : bool =
  match r with
  | RVar (Free rid) -> RegionId.Set.mem rid abs.regions.owned
  | _ -> false

let bottom_in_value_visitor (ended_regions : RegionId.Set.t) =
  object
    inherit [_] iter_tvalue
    method! visit_VBottom _ = raise Found

    method! visit_symbolic_value _ s =
      if symbolic_value_has_ended_regions ended_regions s then raise Found
      else ()
  end

(** Check if a {!type:Values.value} contains [⊥].

    Note that this function is very general: it also checks wether symbolic
    values contain already ended regions. *)
let bottom_in_value (ended_regions : RegionId.Set.t) (v : tvalue) : bool =
  let obj = bottom_in_value_visitor ended_regions in
  (* We use exceptions *)
  try
    obj#visit_tvalue () v;
    false
  with Found -> true

let bottom_in_adt_value (ended_regions : RegionId.Set.t) (v : adt_value) : bool
    =
  let obj = bottom_in_value_visitor ended_regions in
  (* We use exceptions *)
  try
    obj#visit_adt_value () v;
    false
  with Found -> true

let tvalue_has_bottom (ctx : eval_ctx) (v : tvalue) : bool =
  bottom_in_value ctx.ended_regions v

let value_has_ret_symbolic_value_with_borrow_under_mut span (ctx : eval_ctx)
    (v : tvalue) : bool =
  let obj =
    object
      inherit [_] iter_tvalue

      method! visit_symbolic_value _ s =
        if ty_has_borrow_under_mut span ctx.type_ctx.type_infos s.sv_ty then
          raise Found
        else ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_tvalue () v;
    false
  with Found -> true

(** Return the place used in an rvalue, if that makes sense. This is used to
    compute span-data, to find pretty names. *)
let rvalue_get_place (rv : rvalue) : place option =
  match rv with
  | Use (Copy p | Move p) -> Some p
  | Use (Constant _) -> None
  | Len (p, _, _) | RvRef (p, _, _) | RawPtr (p, _, _) -> Some p
  | NullaryOp _
  | UnaryOp _
  | BinaryOp _
  | Discriminant _
  | Aggregate _
  | Repeat _
  | ShallowInitBox _ -> None

(** See {!ValuesUtils.symbolic_value_has_borrows} *)
let symbolic_value_has_borrows span (ctx : eval_ctx) (sv : symbolic_value) :
    bool =
  ValuesUtils.symbolic_value_has_borrows span ctx.type_ctx.type_infos sv

(** See {!ValuesUtils.value_has_borrows}. *)
let value_has_borrows span (ctx : eval_ctx) (v : value) : bool =
  ValuesUtils.value_has_borrows span ctx.type_ctx.type_infos v

(** See {!ValuesUtils.value_has_borrows}. *)
let tvalue_has_borrows span (ctx : eval_ctx) (v : tvalue) : bool =
  ValuesUtils.value_has_borrows span ctx.type_ctx.type_infos v.value

(** See {!ValuesUtils.value_has_loans_or_borrows}. *)
let value_has_loans_or_borrows span (ctx : eval_ctx) (v : value) : bool =
  ValuesUtils.value_has_loans_or_borrows span ctx.type_ctx.type_infos v

(** See {!ValuesUtils.value_has_loans_or_borrows}. *)
let tvalue_has_loans_or_borrows span (ctx : eval_ctx) (v : tvalue) : bool =
  ValuesUtils.value_has_loans_or_borrows span ctx.type_ctx.type_infos v.value

(** See {!ValuesUtils.value_has_loans}. *)
let value_has_loans (v : value) : bool = ValuesUtils.value_has_loans v

(** See {!ValuesUtils.value_has_loans}. *)
let tvalue_has_loans (v : tvalue) : bool = ValuesUtils.value_has_loans v.value

(** See {!ValuesUtils.value_has_outer_loans}. *)
let value_has_outer_loans (v : value) : bool =
  ValuesUtils.value_has_outer_loans v

(** See {!ValuesUtils.value_has_outer_loans}. *)
let tvalue_has_outer_loans (v : tvalue) : bool =
  ValuesUtils.value_has_outer_loans v.value

(** See {!ValuesUtils.value_has_mutable_loans}. *)
let value_has_mutable_loans (v : value) : bool =
  ValuesUtils.value_has_mutable_loans v

(** See {!ValuesUtils.value_has_mutable_loans}. *)
let tvalue_has_mutable_loans (v : tvalue) : bool =
  ValuesUtils.value_has_mutable_loans v.value

(** The borrow id of shared borrows doesn't uniquely identify shared borrows:
    when we need to uniquely identify a borrow, we use the borrow id for mutable
    borrows, and the shared borrow id for shared borrow (once again, the shared
    borrow id is just an implementation detail, it doesn't have any impact in
    the semantics). *)
type unique_borrow_id = UMut of borrow_id | UShared of shared_borrow_id
[@@deriving show, ord]

let unique_borrow_id_to_string (uid : unique_borrow_id) : string =
  match uid with
  | UMut id -> "m@" ^ BorrowId.to_string id
  | UShared id -> "s@" ^ SharedBorrowId.to_string id

module UniqueBorrowIdOrderedType :
  Collections.OrderedType with type t = unique_borrow_id = struct
  type t = unique_borrow_id

  let compare = compare_unique_borrow_id
  let to_string = unique_borrow_id_to_string
  let pp_t = pp_unique_borrow_id
  let show_t = show_unique_borrow_id
end

module UniqueBorrowIdMap = Collections.MakeMap (UniqueBorrowIdOrderedType)
module UniqueBorrowIdSet = Collections.MakeSet (UniqueBorrowIdOrderedType)

type unique_borrow_id_set = UniqueBorrowIdSet.t [@@deriving show, ord]

(** See {!compute_tvalue_ids}, {!compute_context_ids}, etc. *)
type ids_sets = {
  aids : AbsId.Set.t;
  blids : BorrowId.Set.t;  (** All the borrow/loan ids *)
  borrow_ids : BorrowId.Set.t;  (** Only the borrow ids *)
  unique_borrow_ids : UniqueBorrowIdSet.t;
      (** Only the borrow ids, where shared borrows are uniquely identified *)
  non_unique_shared_borrow_ids : BorrowId.Set.t;
  shared_borrow_ids : SharedBorrowId.Set.t;
  loan_ids : BorrowId.Set.t;  (** Only the loan ids *)
  shared_loans_to_values : tvalue BorrowId.Map.t;
  dids : DummyVarId.Set.t;
  rids : RegionId.Set.t;
      (** This should only contain **free** region ids (note that we have to be
          careful because we use the same index type for bound regions and free
          regions - see the implementation of [compute_ids] below) *)
  sids : SymbolicValueId.Set.t;
}
[@@deriving show]

let empty_ids_sets : ids_sets =
  let empty = BorrowId.Set.empty in
  {
    aids = AbsId.Set.empty;
    blids = empty;
    borrow_ids = empty;
    unique_borrow_ids = UniqueBorrowIdSet.empty;
    shared_borrow_ids = SharedBorrowId.Set.empty;
    non_unique_shared_borrow_ids = BorrowId.Set.empty;
    shared_loans_to_values = BorrowId.Map.empty;
    loan_ids = empty;
    dids = DummyVarId.Set.empty;
    rids = RegionId.Set.empty;
    sids = SymbolicValueId.Set.empty;
  }

let ids_sets_inter (ids0 : ids_sets) (ids1 : ids_sets) : ids_sets =
  let aids = AbsId.Set.inter ids0.aids ids1.aids in
  let blids = BorrowId.Set.inter ids0.blids ids1.blids in
  let borrow_ids = BorrowId.Set.inter ids0.borrow_ids ids1.borrow_ids in
  let unique_borrow_ids =
    UniqueBorrowIdSet.inter ids0.unique_borrow_ids ids1.unique_borrow_ids
  in
  let non_unique_shared_borrow_ids =
    BorrowId.Set.inter ids0.non_unique_shared_borrow_ids
      ids1.non_unique_shared_borrow_ids
  in
  let shared_borrow_ids =
    SharedBorrowId.Set.inter ids0.shared_borrow_ids ids1.shared_borrow_ids
  in
  let loan_ids = BorrowId.Set.inter ids0.loan_ids ids1.loan_ids in
  let shared_loans_to_values = BorrowId.Map.empty in
  let dids = DummyVarId.Set.inter ids0.dids ids1.dids in
  let rids = RegionId.Set.inter ids0.rids ids1.rids in
  let sids = SymbolicValueId.Set.inter ids0.sids ids1.sids in
  {
    aids;
    blids;
    borrow_ids;
    unique_borrow_ids;
    non_unique_shared_borrow_ids;
    shared_borrow_ids;
    loan_ids;
    shared_loans_to_values;
    dids;
    rids;
    sids;
  }

(** See {!compute_tvalue_ids}, {!compute_context_ids}, etc.

    TODO: there misses information. *)
type ids_to_values = { sids_to_values : symbolic_value SymbolicValueId.Map.t }

let compute_ids () =
  let blids = ref BorrowId.Set.empty in
  let borrow_ids = ref BorrowId.Set.empty in
  let unique_borrow_ids = ref UniqueBorrowIdSet.empty in
  let shared_borrow_ids = ref SharedBorrowId.Set.empty in
  let non_unique_shared_borrow_ids = ref BorrowId.Set.empty in
  let loan_ids = ref BorrowId.Set.empty in
  let shared_loans_to_values = ref BorrowId.Map.empty in
  let aids = ref AbsId.Set.empty in
  let dids = ref DummyVarId.Set.empty in
  let rids = ref RegionId.Set.empty in
  let sids = ref SymbolicValueId.Set.empty in
  let sids_to_values = ref SymbolicValueId.Map.empty in

  let get_ids () =
    {
      aids = !aids;
      blids = !blids;
      borrow_ids = !borrow_ids;
      unique_borrow_ids = !unique_borrow_ids;
      shared_borrow_ids = !shared_borrow_ids;
      non_unique_shared_borrow_ids = !non_unique_shared_borrow_ids;
      loan_ids = !loan_ids;
      shared_loans_to_values = !shared_loans_to_values;
      dids = !dids;
      rids = !rids;
      sids = !sids;
    }
  in
  let get_ids_to_values () = { sids_to_values = !sids_to_values } in
  let add_shared_borrow bid sid =
    blids := BorrowId.Set.add bid !blids;
    borrow_ids := BorrowId.Set.add bid !borrow_ids;
    unique_borrow_ids := UniqueBorrowIdSet.add (UShared sid) !unique_borrow_ids;
    shared_borrow_ids := SharedBorrowId.Set.add sid !shared_borrow_ids;
    non_unique_shared_borrow_ids :=
      BorrowId.Set.add bid !non_unique_shared_borrow_ids
  in
  let obj =
    object
      inherit [_] iter_eval_ctx as super
      method! visit_dummy_var_id _ did = dids := DummyVarId.Set.add did !dids

      method! visit_shared_borrow_id _ _ =
        (* Make sure we don't miss any *)
        [%internal_error_opt_span] None

      method! visit_borrow_id _ id =
        blids := BorrowId.Set.add id !blids;
        borrow_ids := BorrowId.Set.add id !borrow_ids;
        (* All the shared borrows should be caught elsewhere: if we are here, it must be a mutable borrows *)
        unique_borrow_ids := UniqueBorrowIdSet.add (UMut id) !unique_borrow_ids

      method! visit_loan_id _ id =
        blids := BorrowId.Set.add id !blids;
        loan_ids := BorrowId.Set.add id !loan_ids

      method! visit_VSharedLoan env bid sv =
        shared_loans_to_values :=
          BorrowId.Map.add bid sv !shared_loans_to_values;
        super#visit_VSharedLoan env bid sv

      method! visit_ASharedLoan env pm bid sv child =
        shared_loans_to_values :=
          BorrowId.Map.add bid sv !shared_loans_to_values;
        super#visit_ASharedLoan env pm bid sv child

      method! visit_VSharedBorrow _ bid sid = add_shared_borrow bid sid
      method! visit_VReservedMutBorrow _ bid sid = add_shared_borrow bid sid
      method! visit_ASharedBorrow _ _ bid sid = add_shared_borrow bid sid
      method! visit_AsbBorrow _ bid sid = add_shared_borrow bid sid
      method! visit_abs_id _ id = aids := AbsId.Set.add id !aids
      method! visit_region_id _ id = rids := RegionId.Set.add id !rids

      method! visit_symbolic_value env sv =
        sids := SymbolicValueId.Set.add sv.sv_id !sids;
        sids_to_values := SymbolicValueId.Map.add sv.sv_id sv !sids_to_values;
        super#visit_symbolic_value env sv

      method! visit_symbolic_value_id _ id =
        (* TODO: can we get there without going through [visit_symbolic_value] first? *)
        sids := SymbolicValueId.Set.add id !sids
    end
  in
  (obj, get_ids, get_ids_to_values)

(** Compute the sets of ids found in a list of typed values. *)
let compute_tvalues_ids (xl : tvalue list) : ids_sets * ids_to_values =
  let compute, get_ids, get_ids_to_values = compute_ids () in
  List.iter (compute#visit_tvalue ()) xl;
  (get_ids (), get_ids_to_values ())

(** Compute the sets of ids found in a typed value. *)
let compute_tvalue_ids (x : tvalue) : ids_sets * ids_to_values =
  compute_tvalues_ids [ x ]

(** Compute the sets of ids found in a list of abstractions. *)
let compute_absl_ids (xl : abs list) : ids_sets * ids_to_values =
  let compute, get_ids, get_ids_to_values = compute_ids () in
  List.iter (compute#visit_abs ()) xl;
  (get_ids (), get_ids_to_values ())

(** Compute the sets of ids found in an abstraction. *)
let compute_abs_ids (x : abs) : ids_sets * ids_to_values =
  compute_absl_ids [ x ]

(** Compute the sets of ids found in an environment. *)
let compute_env_ids (x : env) : ids_sets * ids_to_values =
  let compute, get_ids, get_ids_to_values = compute_ids () in
  compute#visit_env () x;
  (get_ids (), get_ids_to_values ())

(** Compute the sets of ids found in an environment element. *)
let compute_env_elem_ids (x : env_elem) : ids_sets * ids_to_values =
  compute_env_ids [ x ]

(** Compute the sets of ids found in a list of contexts. *)
let compute_ctxs_ids (ctxl : eval_ctx list) : ids_sets * ids_to_values =
  let compute, get_ids, get_ids_to_values = compute_ids () in
  List.iter (compute#visit_eval_ctx ()) ctxl;
  (get_ids (), get_ids_to_values ())

(** Compute the sets of ids found in a context. *)
let compute_ctx_ids (ctx : eval_ctx) : ids_sets * ids_to_values =
  compute_ctxs_ids [ ctx ]

let empty_ids_set = fst (compute_ctxs_ids [])

let initialize_eval_ctx (span : Meta.span option) (ctx : decls_ctx)
    (region_groups : RegionGroupId.id list) (type_vars : type_param list)
    (const_generic_vars : const_generic_param list) (marked_ids : marked_ids) :
    eval_ctx =
  let _, _, _, fresh_symbolic_value_id =
    SymbolicValueId.fresh_stateful_generator_with_marked
      marked_ids.symbolic_value_ids
  in
  let _, _, _, fresh_borrow_id =
    BorrowId.fresh_stateful_generator_with_marked marked_ids.borrow_ids
  in

  let _, _, _, fresh_shared_borrow_id =
    SharedBorrowId.fresh_stateful_generator_with_marked
      marked_ids.shared_borrow_ids
  in

  let _, _, _, fresh_region_id =
    RegionId.fresh_stateful_generator_with_marked marked_ids.region_ids
  in
  let _, _, _, fresh_abs_id =
    AbsId.fresh_stateful_generator_with_marked marked_ids.abs_ids
  in
  let _, _, _, fresh_abs_fvar_id =
    AbsFVarId.fresh_stateful_generator_with_marked marked_ids.abs_fvar_ids
  in
  let _, _, _, fresh_dummy_var_id =
    DummyVarId.fresh_stateful_generator_with_marked marked_ids.dummy_var_ids
  in
  let _, _, _, fresh_fun_call_id =
    FunCallId.fresh_stateful_generator_with_marked marked_ids.fun_call_ids
  in
  let _, _, _, fresh_loop_id =
    LoopId.fresh_stateful_generator_with_marked marked_ids.loop_ids
  in
  let _, _, _, fresh_meta_id =
    MetaId.fresh_stateful_generator_with_marked marked_ids.meta_ids
  in

  let const_generic_vars_map =
    ConstGenericVarId.Map.of_list
      (List.map
         (fun (cg : const_generic_param) ->
           let ty = TLiteral cg.ty in
           let cv =
             mk_fresh_symbolic_tvalue_opt_span span fresh_symbolic_value_id ty
           in
           (cg.index, cv))
         const_generic_vars)
  in
  {
    crate = ctx.crate;
    type_ctx = ctx.type_ctx;
    fun_ctx = ctx.fun_ctx;
    region_groups;
    type_vars;
    const_generic_vars;
    const_generic_vars_map;
    env = [ EFrame ];
    ended_regions = RegionId.Set.empty;
    fresh_symbolic_value_id;
    fresh_fun_call_id;
    fresh_dummy_var_id;
    fresh_borrow_id;
    fresh_shared_borrow_id;
    fresh_abs_id;
    fresh_region_id;
    fresh_abs_fvar_id;
    fresh_loop_id;
    fresh_meta_id;
  }

(** Instantiate a function signature, introducing **fresh** abstraction ids and
    region ids. This is mostly used in preparation of function calls (when
    evaluating in symbolic mode). *)
let instantiate_fun_sig (span : Meta.span) (ctx : eval_ctx)
    (generics : generic_args) (tr_self : trait_ref_kind) (sg : fun_sig)
    (regions_hierarchy : region_var_groups) : inst_fun_sig =
  [%ldebug
    "- generics: "
    ^ Print.EvalCtx.generic_args_to_string ctx generics
    ^ "\n- tr_self: "
    ^ Print.EvalCtx.trait_ref_kind_to_string ctx tr_self
    ^ "\n- sg: " ^ fun_sig_to_string ctx sg];
  (* Erase the regions in the generics we use for the instantiation *)
  let generics = Substitute.generic_args_erase_regions generics in
  let tr_self = Substitute.trait_ref_kind_erase_regions tr_self in
  (* Generate fresh abstraction ids and create a substitution from region
   * group ids to abstraction ids *)
  let asubst_map : AbsId.id RegionGroupId.Map.t =
    RegionGroupId.Map.of_list
      (List.map (fun rg -> (rg.id, ctx.fresh_abs_id ())) regions_hierarchy)
  in
  let asubst (rg_id : RegionGroupId.id) : AbsId.id =
    RegionGroupId.Map.find rg_id asubst_map
  in
  (* Generate fresh regions *)
  let rsubst =
    Substitute.fresh_regions_with_substs_from_vars sg.generics.regions
      ctx.fresh_region_id
  in
  (* Generate the type substitution. *)
  [%sanity_check] span (TypesUtils.trait_instance_id_no_regions tr_self);
  let tsubst =
    Substitute.make_type_subst_from_vars sg.generics.types generics.types
  in
  let cgsubst =
    Substitute.make_const_generic_subst_from_vars sg.generics.const_generics
      generics.const_generics
  in
  let tr_subst =
    Substitute.make_trait_subst_from_clauses sg.generics.trait_clauses
      generics.trait_refs
  in
  (* Substitute the signature *)
  let inst_sig =
    Substitute.substitute_signature asubst rsubst tsubst cgsubst tr_subst
      tr_self sg regions_hierarchy
  in
  (* Return *)
  inst_sig

(** Compute the regions hierarchy of an instantiated function call - i.e., a
    function call instantiated with type parameters which might contain borrows.
    We do so by computing a "fake" function signature and by computing the
    regions hierarchy for this signature. We return both the fake signature and
    the regions hierarchy.

    - [type_vars]: the type variables currently in the context
    - [const_generic_vars]: the const generics currently in the context
    - [generic_args]: the generic arguments given to the function
    - [sg]: the original, uninstantiated signature (we need to retrieve, for
      instance, the region outlives constraints) *)
let compute_regions_hierarchy_for_fun_call fresh_abs_id
    (span : Meta.span option) (crate : crate) (fun_name : string)
    (type_vars : type_param list)
    (const_generic_vars : const_generic_param list)
    (generic_args : generic_args) (sg : fun_sig) : inst_fun_sig =
  (* We simply put everything into a "fake" signature, then call
     [compute_regions_hierarchy_for_sig].

     The important point is that we need to introduce fresh regions for
     the erased regions. When doing so, in order to make sure there are
     no collisions, we also refresh the other regions. *)
  (* Decompose the signature *)
  let { is_unsafe; generics; inputs; output } = sg in
  (* Introduce the fresh regions *)
  let region_map = ref RegionId.Map.empty in
  let fresh_regions = ref RegionId.Set.empty in
  let _, fresh_region_id = RegionId.fresh_stateful_generator () in
  let get_region rid =
    match RegionId.Map.find_opt rid !region_map with
    | Some rid -> rid
    | None ->
        let nrid = fresh_region_id () in
        fresh_regions := RegionId.Set.add nrid !fresh_regions;
        region_map := RegionId.Map.add rid nrid !region_map;
        nrid
  in
  let visitor =
    object (_self : 'self)
      inherit [_] map_ty

      method! visit_region_id _ _ =
        [%craise_opt_span] None
          "Region ids should not be visited directly; the visitor should catch \
           cases that contain region ids earlier."

      method! visit_RVar _ var =
        match var with
        | Free rid -> RVar (Free (get_region rid))
        | Bound _ -> RVar var

      method! visit_RErased _ =
        (* Introduce a fresh region *)
        let nrid = fresh_region_id () in
        fresh_regions := RegionId.Set.add nrid !fresh_regions;
        RVar (Free nrid)
    end
  in
  (* We want to make sure that we numerotate the region parameters, even the erased
     ones, in order, before introducing fresh regions for the erased regions which
     appear in the types parameters *)
  let generic_regions =
    List.map (visitor#visit_region ()) generic_args.regions
  in
  (* Explore the types to generate the fresh regions *)
  let generic_types = List.map (visitor#visit_ty ()) generic_args.types in

  (* Reconstruct the generics *)
  let subst =
    let { regions = _; types = _; const_generics; trait_refs } = generic_args in
    let generic_args =
      {
        regions = generic_regions;
        types = generic_types;
        const_generics;
        trait_refs
        (* Keeping the same trait refs: it shouldn't have an impact *);
      }
    in
    Substitute.make_subst_from_generics sg.generics generic_args
  in

  (* Substitute the inputs and outputs *)
  let open Substitute in
  let inputs = List.map (st_substitute_visitor#visit_ty subst) inputs in
  let output = st_substitute_visitor#visit_ty subst output in

  (* Compute the regions hierarchy *)
  let trait_type_constraints, regions_hierarchy =
    let generics : generic_params =
      let {
        regions = _;
        types = _;
        const_generics = _;
        trait_clauses;
        regions_outlive;
        types_outlive;
        trait_type_constraints;
      } =
        generics
      in
      let fresh_regions = RegionId.Set.elements !fresh_regions in
      let fresh_region_vars : region_param list =
        List.map (fun index -> { Types.index; name = None }) fresh_regions
      in
      let open Substitute in
      let trait_clauses =
        List.map (st_substitute_visitor#visit_trait_param subst) trait_clauses
      in
      let regions_outlive =
        List.map
          (st_substitute_visitor#visit_region_binder
             (st_substitute_visitor#visit_outlives_pred
                st_substitute_visitor#visit_region
                st_substitute_visitor#visit_region)
             subst)
          regions_outlive
      in
      let types_outlive =
        List.map
          (st_substitute_visitor#visit_region_binder
             (st_substitute_visitor#visit_outlives_pred
                st_substitute_visitor#visit_ty
                st_substitute_visitor#visit_region)
             subst)
          types_outlive
      in
      {
        regions = fresh_region_vars;
        types = type_vars;
        const_generics = const_generic_vars;
        trait_clauses;
        regions_outlive;
        types_outlive;
        trait_type_constraints;
      }
    in

    let sg = { is_unsafe; generics; inputs; output } in
    let regions_hierarchy =
      RegionsHierarchy.compute_regions_hierarchy_for_sig span crate fun_name sg
    in
    (generics.trait_type_constraints, regions_hierarchy)
  in

  (* Compute the instantiated function signature *)
  (* Generate fresh abstraction ids and create a substitution from region
     group ids to abstraction ids.

     Remark: the region ids used here are fresh (we generated them
     just above).
  *)
  let asubst_map : AbsId.id RegionGroupId.Map.t =
    RegionGroupId.Map.of_list
      (List.map (fun rg -> (rg.id, fresh_abs_id ())) regions_hierarchy)
  in
  let asubst (rg_id : RegionGroupId.id) : AbsId.id =
    RegionGroupId.Map.find rg_id asubst_map
  in
  let subst_abs_region_group (rg : region_var_group) : abs_region_group =
    let id = asubst rg.id in
    let parents = List.map asubst rg.parents in
    ({ id; regions = rg.regions; parents } : abs_region_group)
  in
  let abs_regions_hierarchy =
    List.map subst_abs_region_group regions_hierarchy
  in
  {
    regions_hierarchy;
    abs_regions_hierarchy;
    trait_type_constraints;
    inputs;
    output;
  }

let abs_is_empty (abs : abs) : bool =
  let visitor =
    object
      inherit [_] iter_abs as super

      method! visit_ASymbolic env pm proj =
        (match proj with
        | AProjLoans _ | AProjBorrows _ -> raise Found
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty -> ());
        super#visit_ASymbolic env pm proj

      method! visit_ABorrow env bc =
        (match bc with
        | AMutBorrow _ | ASharedBorrow _ -> raise Found
        | AIgnoredMutBorrow _
        | AEndedMutBorrow _
        | AEndedSharedBorrow
        | AEndedIgnoredMutBorrow _
        | AProjSharedBorrow _ -> ());
        super#visit_ABorrow env bc

      method! visit_abstract_shared_borrow _ _ = raise Found

      method! visit_ALoan env lc =
        (match lc with
        | AMutLoan _ -> raise Found
        | ASharedLoan _
        | AEndedMutLoan _
        | AEndedSharedLoan _
        | AIgnoredMutLoan _
        | AEndedIgnoredMutLoan _
        | AIgnoredSharedLoan _ -> ());
        super#visit_ALoan env lc

      method! visit_VBorrow _ = raise Found
      method! visit_VLoan _ _ = raise Found
    end
  in
  try
    visitor#visit_abs () abs;
    true
  with Found -> false

let abs_has_markers (abs : abs) : bool =
  let visitor =
    object
      inherit [_] iter_abs
      method! visit_proj_marker _ pm = if pm = PNone then () else raise Found
    end
  in
  try
    List.iter (visitor#visit_tavalue ()) abs.avalues;
    false
  with Found -> true
