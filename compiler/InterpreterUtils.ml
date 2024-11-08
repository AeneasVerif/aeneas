open Types
open Values
open Expressions
open Contexts
open LlbcAst
open Utils
open TypesUtils
open Errors

(* TODO: we should probably rename the file to ContextsUtils *)

(** The local logger *)
let log = Logging.interpreter_log

(** Some utilities *)

let eval_ctx_to_string_no_filter = Print.Contexts.eval_ctx_to_string_no_filter
let eval_ctx_to_string = Print.Contexts.eval_ctx_to_string
let name_to_string = Print.EvalCtx.name_to_string
let symbolic_value_to_string = Print.EvalCtx.symbolic_value_to_string
let borrow_content_to_string = Print.EvalCtx.borrow_content_to_string
let loan_content_to_string = Print.EvalCtx.loan_content_to_string
let aborrow_content_to_string = Print.EvalCtx.aborrow_content_to_string
let aloan_content_to_string = Print.EvalCtx.aloan_content_to_string
let aproj_to_string = Print.EvalCtx.aproj_to_string
let typed_value_to_string = Print.EvalCtx.typed_value_to_string
let typed_avalue_to_string = Print.EvalCtx.typed_avalue_to_string
let place_to_string = Print.EvalCtx.place_to_string
let operand_to_string = Print.EvalCtx.operand_to_string
let fun_sig_to_string = Print.EvalCtx.fun_sig_to_string
let inst_fun_sig_to_string = Print.EvalCtx.inst_fun_sig_to_string
let ty_to_string = Print.EvalCtx.ty_to_string
let generic_args_to_string = Print.EvalCtx.generic_args_to_string
let trait_ref_to_string = Print.EvalCtx.trait_ref_to_string
let trait_decl_ref_to_string = Print.EvalCtx.trait_decl_ref_to_string

let trait_decl_ref_region_binder_to_string =
  Print.EvalCtx.trait_decl_ref_region_binder_to_string

let fun_id_or_trait_method_ref_to_string =
  Print.EvalCtx.fun_id_or_trait_method_ref_to_string

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

let env_to_string span ctx env =
  eval_ctx_to_string ~span:(Some span) { ctx with env }

let abs_to_string span ctx =
  Print.EvalCtx.abs_to_string ~span:(Some span) ctx "" "  "

let same_symbolic_id (sv0 : symbolic_value) (sv1 : symbolic_value) : bool =
  sv0.sv_id = sv1.sv_id

let mk_var (index : VarId.id) (name : string option) (var_ty : ty) : var =
  { index; name; var_ty }

(** Small helper - TODO: move *)
let mk_place_from_var_id (ctx : eval_ctx) (span : Meta.span) (var_id : VarId.id)
    : place =
  let _, typed_val = env_lookup_var span ctx.env var_id in
  { kind = PlaceBase var_id; ty = typed_val.ty }

(** Create a fresh symbolic value *)
let mk_fresh_symbolic_value_opt_span (span : Meta.span option) (ty : ty) :
    symbolic_value =
  (* Sanity check *)
  sanity_check_opt_span __FILE__ __LINE__ (ty_is_rty ty) span;
  let sv_id = fresh_symbolic_value_id () in
  let svalue = { sv_id; sv_ty = ty } in
  svalue

let mk_fresh_symbolic_value span = mk_fresh_symbolic_value_opt_span (Some span)

let mk_fresh_symbolic_value_from_no_regions_ty (span : Meta.span) (ty : ty) :
    symbolic_value =
  sanity_check __FILE__ __LINE__ (ty_no_regions ty) span;
  mk_fresh_symbolic_value span ty

(** Create a fresh symbolic value *)
let mk_fresh_symbolic_typed_value_opt_span (span : Meta.span option) (rty : ty)
    : typed_value =
  sanity_check_opt_span __FILE__ __LINE__ (ty_is_rty rty) span;
  let ty = Substitute.erase_regions rty in
  (* Generate the fresh a symbolic value *)
  let value = mk_fresh_symbolic_value_opt_span span rty in
  let value = VSymbolic value in
  { value; ty }

let mk_fresh_symbolic_typed_value span =
  mk_fresh_symbolic_typed_value_opt_span (Some span)

let mk_fresh_symbolic_typed_value_from_no_regions_ty (span : Meta.span)
    (ty : ty) : typed_value =
  sanity_check __FILE__ __LINE__ (ty_no_regions ty) span;
  mk_fresh_symbolic_typed_value span ty

(** Create a typed value from a symbolic value. *)
let mk_typed_value_from_symbolic_value (svalue : symbolic_value) : typed_value =
  let av = VSymbolic svalue in
  let av : typed_value =
    { value = av; ty = Substitute.erase_regions svalue.sv_ty }
  in
  av

(** Create a loans projector value from a symbolic value.
    
    Checks if the projector will actually project some regions. If not,
    returns {!Values.AIgnored} ([_]).
    
    TODO: update to handle 'static
 *)
let mk_aproj_loans_value_from_symbolic_value (regions : RegionId.Set.t)
    (svalue : symbolic_value) : typed_avalue =
  if ty_has_regions_in_set regions svalue.sv_ty then
    let av = ASymbolic (AProjLoans (svalue, [])) in
    let av : typed_avalue = { value = av; ty = svalue.sv_ty } in
    av
  else { value = AIgnored; ty = svalue.sv_ty }

(** Create a borrows projector from a symbolic value *)
let mk_aproj_borrows_from_symbolic_value (span : Meta.span)
    (proj_regions : RegionId.Set.t) (svalue : symbolic_value) (proj_ty : ty) :
    aproj =
  sanity_check __FILE__ __LINE__ (ty_is_rty proj_ty) span;
  if ty_has_regions_in_set proj_regions proj_ty then
    AProjBorrows (svalue, proj_ty)
  else AIgnoredProjBorrows

(** TODO: move *)
let borrow_is_asb (bid : BorrowId.id) (asb : abstract_shared_borrow) : bool =
  match asb with
  | AsbBorrow bid' -> bid' = bid
  | AsbProjReborrows _ -> false

(** TODO: move *)
let borrow_in_asb (bid : BorrowId.id) (asb : abstract_shared_borrows) : bool =
  List.exists (borrow_is_asb bid) asb

(** TODO: move *)
let remove_borrow_from_asb (span : Meta.span) (bid : BorrowId.id)
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
  sanity_check __FILE__ __LINE__ (!removed = 1) span;
  asb

(** We sometimes need to return a value whose type may vary depending on
    whether we find it in a "concrete" value or an abstraction (ex.: loan
    contents when we perform environment lookups by using borrow ids)

    TODO: change the name "abstract"
 *)
type ('a, 'b) concrete_or_abs = Concrete of 'a | Abstract of 'b
[@@deriving show]

(** Generic loan content: concrete or abstract *)
type g_loan_content = (loan_content, aloan_content) concrete_or_abs
[@@deriving show]

(** Generic borrow content: concrete or abstract *)
type g_borrow_content = (borrow_content, aborrow_content) concrete_or_abs
[@@deriving show]

type abs_or_var_id =
  | AbsId of AbstractionId.id
  | VarId of VarId.id
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
exception FoundAProjBorrows of symbolic_value * ty

let symbolic_value_id_in_ctx (sv_id : SymbolicValueId.id) (ctx : eval_ctx) :
    bool =
  let obj =
    object
      inherit [_] iter_eval_ctx as super

      method! visit_VSymbolic _ sv =
        if sv.sv_id = sv_id then raise Found else ()

      method! visit_aproj env aproj =
        (match aproj with
        | AProjLoans (sv, _) | AProjBorrows (sv, _) ->
            if sv.sv_id = sv_id then raise Found else ()
        | AEndedProjLoans _ | AEndedProjBorrows _ | AIgnoredProjBorrows -> ());
        super#visit_aproj env aproj

      method! visit_abstract_shared_borrows _ asb =
        let visit (asb : abstract_shared_borrow) : unit =
          match asb with
          | AsbBorrow _ -> ()
          | AsbProjReborrows (sv, _) ->
              if sv.sv_id = sv_id then raise Found else ()
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
let symbolic_value_has_ended_regions (ended_regions : RegionId.Set.t)
    (s : symbolic_value) : bool =
  let regions = ty_regions s.sv_ty in
  not (RegionId.Set.disjoint regions ended_regions)

let bottom_in_value_visitor (ended_regions : RegionId.Set.t) =
  object
    inherit [_] iter_typed_value
    method! visit_VBottom _ = raise Found

    method! visit_symbolic_value _ s =
      if symbolic_value_has_ended_regions ended_regions s then raise Found
      else ()
  end

(** Check if a {!type:Values.value} contains [⊥].

    Note that this function is very general: it also checks wether
    symbolic values contain already ended regions.
 *)
let bottom_in_value (ended_regions : RegionId.Set.t) (v : typed_value) : bool =
  let obj = bottom_in_value_visitor ended_regions in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
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

let value_has_ret_symbolic_value_with_borrow_under_mut (ctx : eval_ctx)
    (v : typed_value) : bool =
  let obj =
    object
      inherit [_] iter_typed_value

      method! visit_symbolic_value _ s =
        if ty_has_borrow_under_mut ctx.type_ctx.type_infos s.sv_ty then
          raise Found
        else ()
    end
  in
  (* We use exceptions *)
  try
    obj#visit_typed_value () v;
    false
  with Found -> true

(** Return the place used in an rvalue, if that makes sense.
    This is used to compute span-data, to find pretty names.
 *)
let rvalue_get_place (rv : rvalue) : place option =
  match rv with
  | Use (Copy p | Move p) -> Some p
  | Use (Constant _) -> None
  | Len (p, _, _) | RvRef (p, _) | RawPtr (p, _) -> Some p
  | NullaryOp _
  | UnaryOp _
  | BinaryOp _
  | Global _
  | GlobalRef _
  | Discriminant _
  | Aggregate _ -> None

(** See {!ValuesUtils.symbolic_value_has_borrows} *)
let symbolic_value_has_borrows (ctx : eval_ctx) (sv : symbolic_value) : bool =
  ValuesUtils.symbolic_value_has_borrows ctx.type_ctx.type_infos sv

(** See {!ValuesUtils.value_has_borrows}. *)
let value_has_borrows (ctx : eval_ctx) (v : value) : bool =
  ValuesUtils.value_has_borrows ctx.type_ctx.type_infos v

(** See {!ValuesUtils.value_has_loans_or_borrows}. *)
let value_has_loans_or_borrows (ctx : eval_ctx) (v : value) : bool =
  ValuesUtils.value_has_loans_or_borrows ctx.type_ctx.type_infos v

(** See {!ValuesUtils.value_has_loans}. *)
let value_has_loans (v : value) : bool = ValuesUtils.value_has_loans v

(** See {!compute_typed_value_ids}, {!compute_context_ids}, etc. *)
type ids_sets = {
  aids : AbstractionId.Set.t;
  blids : BorrowId.Set.t;  (** All the borrow/loan ids *)
  borrow_ids : BorrowId.Set.t;  (** Only the borrow ids *)
  loan_ids : BorrowId.Set.t;  (** Only the loan ids *)
  dids : DummyVarId.Set.t;
  rids : RegionId.Set.t;
  sids : SymbolicValueId.Set.t;
}
[@@deriving show]

(** See {!compute_typed_value_ids}, {!compute_context_ids}, etc.

    TODO: there misses information.
 *)
type ids_to_values = { sids_to_values : symbolic_value SymbolicValueId.Map.t }

let compute_ids () =
  let blids = ref BorrowId.Set.empty in
  let borrow_ids = ref BorrowId.Set.empty in
  let loan_ids = ref BorrowId.Set.empty in
  let aids = ref AbstractionId.Set.empty in
  let dids = ref DummyVarId.Set.empty in
  let rids = ref RegionId.Set.empty in
  let sids = ref SymbolicValueId.Set.empty in
  let sids_to_values = ref SymbolicValueId.Map.empty in

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
      inherit [_] iter_eval_ctx as super
      method! visit_dummy_var_id _ did = dids := DummyVarId.Set.add did !dids

      method! visit_borrow_id _ id =
        blids := BorrowId.Set.add id !blids;
        borrow_ids := BorrowId.Set.add id !borrow_ids

      method! visit_loan_id _ id =
        blids := BorrowId.Set.add id !blids;
        loan_ids := BorrowId.Set.add id !loan_ids

      method! visit_abstraction_id _ id = aids := AbstractionId.Set.add id !aids
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
let compute_typed_values_ids (xl : typed_value list) : ids_sets * ids_to_values
    =
  let compute, get_ids, get_ids_to_values = compute_ids () in
  List.iter (compute#visit_typed_value ()) xl;
  (get_ids (), get_ids_to_values ())

(** Compute the sets of ids found in a typed value. *)
let compute_typed_value_ids (x : typed_value) : ids_sets * ids_to_values =
  compute_typed_values_ids [ x ]

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

(** **WARNING**: this function doesn't compute the normalized types
    (for the trait type aliases). This should be computed afterwards.
 *)
let initialize_eval_ctx (span : Meta.span option) (ctx : decls_ctx)
    (region_groups : RegionGroupId.id list) (type_vars : type_var list)
    (const_generic_vars : const_generic_var list) : eval_ctx =
  reset_global_counters ();
  let const_generic_vars_map =
    ConstGenericVarId.Map.of_list
      (List.map
         (fun (cg : const_generic_var) ->
           let ty = TLiteral cg.ty in
           let cv = mk_fresh_symbolic_typed_value_opt_span span ty in
           (cg.index, cv))
         const_generic_vars)
  in
  {
    type_ctx = ctx.type_ctx;
    fun_ctx = ctx.fun_ctx;
    global_ctx = ctx.global_ctx;
    trait_decls_ctx = ctx.trait_decls_ctx;
    trait_impls_ctx = ctx.trait_impls_ctx;
    region_groups;
    type_vars;
    const_generic_vars;
    const_generic_vars_map;
    norm_trait_types = TraitTypeRefMap.empty (* Empty for now *);
    env = [ EFrame ];
    ended_regions = RegionId.Set.empty;
  }

(** Instantiate a function signature, introducing **fresh** abstraction ids and
    region ids. This is mostly used in preparation of function calls (when
    evaluating in symbolic mode).
 *)
let instantiate_fun_sig (span : Meta.span) (ctx : eval_ctx)
    (generics : generic_args) (tr_self : trait_instance_id) (sg : fun_sig)
    (regions_hierarchy : region_var_groups) : inst_fun_sig =
  log#ldebug
    (lazy
      ("instantiate_fun_sig:" ^ "\n- generics: "
      ^ Print.EvalCtx.generic_args_to_string ctx generics
      ^ "\n- tr_self: "
      ^ Print.EvalCtx.trait_instance_id_to_string ctx tr_self
      ^ "\n- sg: " ^ fun_sig_to_string ctx sg));
  (* Erase the regions in the generics we use for the instantiation *)
  let generics = Substitute.generic_args_erase_regions generics in
  let tr_self = Substitute.trait_instance_id_erase_regions tr_self in
  (* Generate fresh abstraction ids and create a substitution from region
   * group ids to abstraction ids *)
  let rg_abs_ids_bindings =
    List.map
      (fun rg ->
        let abs_id = fresh_abstraction_id () in
        (rg.id, abs_id))
      regions_hierarchy
  in
  let asubst_map : AbstractionId.id RegionGroupId.Map.t =
    List.fold_left
      (fun mp (rg_id, abs_id) -> RegionGroupId.Map.add rg_id abs_id mp)
      RegionGroupId.Map.empty rg_abs_ids_bindings
  in
  let asubst (rg_id : RegionGroupId.id) : AbstractionId.id =
    RegionGroupId.Map.find rg_id asubst_map
  in
  (* Generate fresh regions and their substitutions *)
  let _, rsubst, _ =
    Substitute.fresh_regions_with_substs_from_vars ~fail_if_not_found:true
      sg.generics.regions
  in
  let rsubst r = Option.get (rsubst r) in
  (* Generate the type substitution
     Note that for now we don't support instantiating the type parameters with
     types containing regions. *)
  sanity_check __FILE__ __LINE__
    (List.for_all TypesUtils.ty_no_regions generics.types)
    span;
  sanity_check __FILE__ __LINE__
    (TypesUtils.trait_instance_id_no_regions tr_self)
    span;
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
    AssociatedTypes.ctx_subst_norm_signature span ctx asubst rsubst tsubst
      cgsubst tr_subst tr_self sg regions_hierarchy
  in
  (* Return *)
  inst_sig
