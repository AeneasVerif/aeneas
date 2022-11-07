(* This module provides the functions which handle expansion of symbolic values.
 * For now, this file doesn't handle expansion of ⊥ values because they need
 * some path utilities for replacement. We might change that in the future (by
 * using indices to identify the values for instance). *)

module T = Types
module PV = PrimitiveValues
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module L = Logging
open TypesUtils
module Inv = Invariants
module S = SynthesizeSymbolic
module SA = SymbolicAst
open Cps
open ValuesUtils
open InterpreterUtils
open InterpreterProjectors
open InterpreterBorrows

(** The local logger *)
let log = L.expansion_log

(** Projector kind *)
type proj_kind = LoanProj | BorrowProj

(** Auxiliary function.
    Apply a symbolic expansion to avalues in a context, targetting a specific
    kind of projectors.
    
    [proj_kind] controls whether we apply the expansion to projectors
    on loans or projectors on borrows.
    
    When dealing with reference expansion, it is necessary to first apply the
    expansion on loan projectors, then on borrow projectors. The reason is
    that reducing the borrow projectors might require to perform some reborrows,
    in which case we need to lookup the corresponding loans in the context.
    
    [allow_reborrows] controls whether we allow reborrows or not. It is useful
    only if we target borrow projectors.
    
    Also, if this function is called on an expansion for *shared references*,
    the proj borrows should already have been expanded.
    
    TODO: the way this function is used is a bit complex, especially because of
    the above condition. Maybe we should have:
    1. a generic function to expand the loan projectors
    2. a function to expand the borrow projectors for non-borrows
    3. specialized functions for mut borrows and shared borrows
    Note that 2. and 3. may have a little bit of duplicated code, but hopefully
    it would make things clearer.
*)
let apply_symbolic_expansion_to_target_avalues (config : C.config)
    (allow_reborrows : bool) (proj_kind : proj_kind)
    (original_sv : V.symbolic_value) (expansion : V.symbolic_expansion)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* Symbolic values contained in the expansion might contain already ended regions *)
  let check_symbolic_no_ended = false in
  (* Prepare reborrows registration *)
  let fresh_reborrow, apply_registered_reborrows =
    prepare_reborrows config allow_reborrows
  in
  (* Visitor to apply the expansion *)
  let obj =
    object (self)
      inherit [_] C.map_eval_ctx as super

      (** When visiting an abstraction, we remember the regions it owns to be
          able to properly reduce projectors when expanding symbolic values *)
      method! visit_abs current_abs abs =
        assert (Option.is_none current_abs);
        let current_abs = Some abs in
        super#visit_abs current_abs abs

      (** We carefully updated {!visit_ASymbolic} so that {!visit_aproj} is called
          only on child projections (i.e., projections which appear in {!AEndedProjLoans}).
          The role of visit_aproj is then to check we don't have to expand symbolic
          values in child projections, because it should never happen
        *)
      method! visit_aproj current_abs aproj =
        (match aproj with
        | AProjLoans (sv, _) | AProjBorrows (sv, _) ->
            assert (not (same_symbolic_id sv original_sv))
        | AEndedProjLoans _ | AEndedProjBorrows _ | AIgnoredProjBorrows -> ());
        super#visit_aproj current_abs aproj

      method! visit_ASymbolic current_abs aproj =
        let current_abs = Option.get current_abs in
        let proj_regions = current_abs.regions in
        let ancestors_regions = current_abs.ancestors_regions in
        (* Explore in depth first - we won't update anything: we simply
         * want to check we don't have to expand inner symbolic value *)
        match (aproj, proj_kind) with
        | V.AEndedProjBorrows _, _ -> V.ASymbolic aproj
        | V.AEndedProjLoans _, _ ->
            (* Explore the given back values to make sure we don't have to expand
             * anything in there *)
            V.ASymbolic (self#visit_aproj (Some current_abs) aproj)
        | V.AProjLoans (sv, given_back), LoanProj ->
            (* Check if this is the symbolic value we are looking for *)
            if same_symbolic_id sv original_sv then (
              (* There mustn't be any given back values *)
              assert (given_back = []);
              (* Apply the projector *)
              let projected_value =
                apply_proj_loans_on_symbolic_expansion proj_regions expansion
                  original_sv.V.sv_ty
              in
              (* Replace *)
              projected_value.V.value)
            else
              (* Not the searched symbolic value: nothing to do *)
              super#visit_ASymbolic (Some current_abs) aproj
        | V.AProjBorrows (sv, proj_ty), BorrowProj ->
            (* Check if this is the symbolic value we are looking for *)
            if same_symbolic_id sv original_sv then
              (* Convert the symbolic expansion to a value on which we can
               * apply a projector (if the expansion is a reference expansion,
               * convert it to a borrow) *)
              (* WARNING: we mustn't get there if the expansion is for a shared
               * reference. *)
              let expansion =
                symbolic_expansion_non_shared_borrow_to_value original_sv
                  expansion
              in
              (* Apply the projector *)
              let projected_value =
                apply_proj_borrows check_symbolic_no_ended ctx fresh_reborrow
                  proj_regions ancestors_regions expansion proj_ty
              in
              (* Replace *)
              projected_value.V.value
            else
              (* Not the searched symbolic value: nothing to do *)
              super#visit_ASymbolic (Some current_abs) aproj
        | V.AProjLoans _, BorrowProj
        | V.AProjBorrows (_, _), LoanProj
        | V.AIgnoredProjBorrows, _ ->
            (* Nothing to do *)
            V.ASymbolic aproj
    end
  in
  (* Apply the expansion *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Apply the reborrows *)
  apply_registered_reborrows ctx

(** Auxiliary function.
    Apply a symbolic expansion to avalues in a context.
*)
let apply_symbolic_expansion_to_avalues (config : C.config)
    (allow_reborrows : bool) (original_sv : V.symbolic_value)
    (expansion : V.symbolic_expansion) (ctx : C.eval_ctx) : C.eval_ctx =
  let apply_expansion proj_kind ctx =
    apply_symbolic_expansion_to_target_avalues config allow_reborrows proj_kind
      original_sv expansion ctx
  in
  (* First target the loan projectors, then the borrow projectors *)
  let ctx = apply_expansion LoanProj ctx in
  let ctx = apply_expansion BorrowProj ctx in
  ctx

(** Auxiliary function.

    Simply replace the symbolic values (*not avalues*) in the context with
    a given value. Will break invariants if not used properly.
*)
let replace_symbolic_values (at_most_once : bool)
    (original_sv : V.symbolic_value) (nv : V.value) (ctx : C.eval_ctx) :
    C.eval_ctx =
  (* Count *)
  let replaced = ref false in
  let replace () =
    if at_most_once then assert (not !replaced);
    replaced := true;
    nv
  in
  (* Visitor to apply the substitution *)
  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_Symbolic env spc =
        if same_symbolic_id spc original_sv then replace ()
        else super#visit_Symbolic env spc
    end
  in
  (* Apply the substitution *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Return *)
  ctx

(** Apply a symbolic expansion to a context, by replacing the original
    symbolic value with its expanded value. Is valid only if the expansion
    is not a borrow (i.e., an adt...).
    
    This function does update the synthesis.
*)
let apply_symbolic_expansion_non_borrow (config : C.config)
    (original_sv : V.symbolic_value) (expansion : V.symbolic_expansion)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* Apply the expansion to non-abstraction values *)
  let nv = symbolic_expansion_non_borrow_to_value original_sv expansion in
  let at_most_once = false in
  let ctx = replace_symbolic_values at_most_once original_sv nv.V.value ctx in
  (* Apply the expansion to abstraction values *)
  let allow_reborrows = false in
  apply_symbolic_expansion_to_avalues config allow_reborrows original_sv
    expansion ctx

(** Compute the expansion of an adt value.

    The function might return a list of values if the symbolic value to expand
    is an enumeration.
    
    [expand_enumerations] controls the expansion of enumerations: if false, it
    doesn't allow the expansion of enumerations *containing several variants*.
 *)
let compute_expanded_symbolic_adt_value (expand_enumerations : bool)
    (kind : V.sv_kind) (def_id : T.TypeDeclId.id)
    (regions : T.RegionId.id T.region list) (types : T.rty list)
    (ctx : C.eval_ctx) : V.symbolic_expansion list =
  (* Lookup the definition and check if it is an enumeration with several
   * variants *)
  let def = C.ctx_lookup_type_decl ctx def_id in
  assert (List.length regions = List.length def.T.region_params);
  (* Retrieve, for every variant, the list of its instantiated field types *)
  let variants_fields_types =
    Subst.type_decl_get_instantiated_variants_fields_rtypes def regions types
  in
  (* Check if there is strictly more than one variant *)
  if List.length variants_fields_types > 1 && not expand_enumerations then
    raise (Failure "Not allowed to expand enumerations with several variants");
  (* Initialize the expanded value for a given variant *)
  let initialize
      ((variant_id, field_types) : T.VariantId.id option * T.rty list) :
      V.symbolic_expansion =
    let field_values =
      List.map (fun (ty : T.rty) -> mk_fresh_symbolic_value kind ty) field_types
    in
    let see = V.SeAdt (variant_id, field_values) in
    see
  in
  (* Initialize all the expanded values of all the variants *)
  List.map initialize variants_fields_types

(** Compute the expansion of an Option value.
 *)
let compute_expanded_symbolic_option_value (expand_enumerations : bool)
    (kind : V.sv_kind) (ty : T.rty) : V.symbolic_expansion list =
  assert expand_enumerations;
  let some_se =
    V.SeAdt (Some T.option_some_id, [ mk_fresh_symbolic_value kind ty ])
  in
  let none_se = V.SeAdt (Some T.option_none_id, []) in
  [ none_se; some_se ]

let compute_expanded_symbolic_tuple_value (kind : V.sv_kind)
    (field_types : T.rty list) : V.symbolic_expansion =
  (* Generate the field values *)
  let field_values =
    List.map (fun sv_ty -> mk_fresh_symbolic_value kind sv_ty) field_types
  in
  let variant_id = None in
  let see = V.SeAdt (variant_id, field_values) in
  see

let compute_expanded_symbolic_box_value (kind : V.sv_kind) (boxed_ty : T.rty) :
    V.symbolic_expansion =
  (* Introduce a fresh symbolic value *)
  let boxed_value = mk_fresh_symbolic_value kind boxed_ty in
  let see = V.SeAdt (None, [ boxed_value ]) in
  see

let expand_symbolic_value_shared_borrow (config : C.config)
    (original_sv : V.symbolic_value) (original_sv_place : SA.mplace option)
    (ref_ty : T.rty) : cm_fun =
 fun cf ctx ->
  (* First, replace the projectors on borrows.
   * The important point is that the symbolic value to expand may appear
   * several times, if it has been copied. In this case, we need to introduce
   * one fresh borrow id per instance.
   *)
  let borrows = ref V.BorrowId.Set.empty in
  let fresh_borrow () =
    let bid' = C.fresh_borrow_id () in
    borrows := V.BorrowId.Set.add bid' !borrows;
    bid'
  in
  (* Small utility used on shared borrows in abstractions (regular borrow
   * projector and asb).
   * Returns [Some] if the symbolic value has been expanded to an asb list,
   * [None] otherwise *)
  let reborrow_ashared proj_regions (sv : V.symbolic_value) (proj_ty : T.rty) :
      V.abstract_shared_borrows option =
    if same_symbolic_id sv original_sv then
      match proj_ty with
      | T.Ref (r, ref_ty, T.Shared) ->
          (* Projector over the shared value *)
          let shared_asb = V.AsbProjReborrows (sv, ref_ty) in
          (* Check if the region is in the set of projected regions *)
          if region_in_set r proj_regions then
            (* In the set: we need to reborrow *)
            let bid = fresh_borrow () in
            Some [ V.AsbBorrow bid; shared_asb ]
          else (* Not in the set: ignore *)
            Some [ shared_asb ]
      | _ -> raise (Failure "Unexpected")
    else None
  in
  (* The fresh symbolic value for the shared value *)
  let shared_sv = mk_fresh_symbolic_value original_sv.sv_kind ref_ty in
  (* Visitor to replace the projectors on borrows *)
  let obj =
    object (self)
      inherit [_] C.map_eval_ctx as super

      method! visit_Symbolic env sv =
        if same_symbolic_id sv original_sv then
          let bid = fresh_borrow () in
          V.Borrow
            (V.SharedBorrow (mk_typed_value_from_symbolic_value shared_sv, bid))
        else super#visit_Symbolic env sv

      method! visit_Abs proj_regions abs =
        assert (Option.is_none proj_regions);
        let proj_regions = Some abs.V.regions in
        super#visit_Abs proj_regions abs

      method! visit_AProjSharedBorrow proj_regions asb =
        let expand_asb (asb : V.abstract_shared_borrow) :
            V.abstract_shared_borrows =
          match asb with
          | V.AsbBorrow _ -> [ asb ]
          | V.AsbProjReborrows (sv, proj_ty) -> (
              match reborrow_ashared (Option.get proj_regions) sv proj_ty with
              | None -> [ asb ]
              | Some asb -> asb)
        in
        let asb = List.concat (List.map expand_asb asb) in
        V.AProjSharedBorrow asb

      (** We carefully updated {!visit_ASymbolic} so that {!visit_aproj} is called
          only on child projections (i.e., projections which appear in {!AEndedProjLoans}).
          The role of visit_aproj is then to check we don't have to expand symbolic
          values in child projections, because it should never happen
        *)
      method! visit_aproj proj_regions aproj =
        (match aproj with
        | AProjLoans (sv, _) | AProjBorrows (sv, _) ->
            assert (not (same_symbolic_id sv original_sv))
        | AEndedProjLoans _ | AEndedProjBorrows _ | AIgnoredProjBorrows -> ());
        super#visit_aproj proj_regions aproj

      method! visit_ASymbolic proj_regions aproj =
        match aproj with
        | AEndedProjBorrows _ | AIgnoredProjBorrows ->
            (* We ignore borrows *) V.ASymbolic aproj
        | AProjLoans _ ->
            (* Loans are handled later *)
            V.ASymbolic aproj
        | AProjBorrows (sv, proj_ty) -> (
            (* Check if we need to reborrow *)
            match reborrow_ashared (Option.get proj_regions) sv proj_ty with
            | None -> super#visit_ASymbolic proj_regions aproj
            | Some asb -> V.ABorrow (V.AProjSharedBorrow asb))
        | AEndedProjLoans _ ->
            (* Sanity check: make sure there is nothing to expand inside the
             * children projections *)
            V.ASymbolic (self#visit_aproj proj_regions aproj)
    end
  in
  (* Call the visitor *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Finally, replace the projectors on loans *)
  let bids = !borrows in
  assert (not (V.BorrowId.Set.is_empty bids));
  let see = V.SeSharedRef (bids, shared_sv) in
  let allow_reborrows = true in
  let ctx =
    apply_symbolic_expansion_to_avalues config allow_reborrows original_sv see
      ctx
  in
  (* Call the continuation *)
  let expr = cf ctx in
  (* Update the synthesized program *)
  S.synthesize_symbolic_expansion_no_branching original_sv original_sv_place see
    expr

(** TODO: simplify and merge with the other expansion function *)
let expand_symbolic_value_borrow (config : C.config)
    (original_sv : V.symbolic_value) (original_sv_place : SA.mplace option)
    (region : T.RegionId.id T.region) (ref_ty : T.rty) (rkind : T.ref_kind) :
    cm_fun =
 fun cf ctx ->
  (* Check that we are allowed to expand the reference *)
  assert (not (region_in_set region ctx.ended_regions));
  (* Match on the reference kind *)
  match rkind with
  | T.Mut ->
      (* Simple case: simply create a fresh symbolic value and a fresh
       * borrow id *)
      let sv = mk_fresh_symbolic_value original_sv.sv_kind ref_ty in
      let bid = C.fresh_borrow_id () in
      let see = V.SeMutRef (bid, sv) in
      (* Expand the symbolic values - we simply perform a substitution (and
       * check that we perform exactly one substitution) *)
      let nv = symbolic_expansion_non_shared_borrow_to_value original_sv see in
      let at_most_once = true in
      let ctx =
        replace_symbolic_values at_most_once original_sv nv.V.value ctx
      in
      (* Expand the symbolic avalues *)
      let allow_reborrows = true in
      let ctx =
        apply_symbolic_expansion_to_avalues config allow_reborrows original_sv
          see ctx
      in
      (* Apply the continuation *)
      let expr = cf ctx in
      (* Update the synthesized program *)
      S.synthesize_symbolic_expansion_no_branching original_sv original_sv_place
        see expr
  | T.Shared ->
      expand_symbolic_value_shared_borrow config original_sv original_sv_place
        ref_ty cf ctx

(** A small helper.

    Apply a branching symbolic expansion to a context and execute all the
    branches. Note that the expansion is optional for every branch (this is
    used for integer expansion: see {!expand_symbolic_int}).
    
    [see_cf_l]: list of pairs (optional symbolic expansion, continuation)
*)
let apply_branching_symbolic_expansions_non_borrow (config : C.config)
    (sv : V.symbolic_value) (sv_place : SA.mplace option)
    (see_cf_l : (V.symbolic_expansion option * m_fun) list) : m_fun =
 fun ctx ->
  assert (see_cf_l <> []);
  (* Apply the symbolic expansion in in the context and call the continuation *)
  let resl =
    List.map
      (fun (see_opt, cf) ->
        (* Expansion *)
        let ctx =
          match see_opt with
          | None -> ctx
          | Some see -> apply_symbolic_expansion_non_borrow config sv see ctx
        in
        (* Continuation *)
        cf ctx)
      see_cf_l
  in
  (* Collect the result: either we computed no subterm, or we computed all
   * of them *)
  let subterms =
    match resl with
    | Some _ :: _ -> Some (List.map Option.get resl)
    | None :: _ ->
        List.iter (fun res -> assert (res = None)) resl;
        None
    | _ -> raise (Failure "Unreachable")
  in
  (* Synthesize and return *)
  let seel = List.map fst see_cf_l in
  S.synthesize_symbolic_expansion sv sv_place seel subterms

let expand_symbolic_bool (config : C.config) (sv : V.symbolic_value)
    (sv_place : SA.mplace option) (cf_true : m_fun) (cf_false : m_fun) : m_fun =
 fun ctx ->
  (* Compute the expanded value *)
  let original_sv = sv in
  let original_sv_place = sv_place in
  let rty = original_sv.V.sv_ty in
  assert (rty = T.Bool);
  (* Expand the symbolic value to true or false and continue execution *)
  let see_true = V.SePrimitive (PV.Bool true) in
  let see_false = V.SePrimitive (PV.Bool false) in
  let seel = [ (Some see_true, cf_true); (Some see_false, cf_false) ] in
  (* Apply the symbolic expansion (this also outputs the updated symbolic AST) *)
  apply_branching_symbolic_expansions_non_borrow config original_sv
    original_sv_place seel ctx

let expand_symbolic_value (config : C.config) (allow_branching : bool)
    (sv : V.symbolic_value) (sv_place : SA.mplace option) : cm_fun =
 fun cf ctx ->
  (* Debug *)
  log#ldebug (lazy ("expand_symbolic_value:" ^ symbolic_value_to_string ctx sv));
  (* Remember the initial context for printing purposes *)
  let ctx0 = ctx in
  (* Compute the expanded value - note that when doing so, we may introduce
   * fresh symbolic values in the context (which thus gets updated) *)
  let original_sv = sv in
  let original_sv_place = sv_place in
  let rty = original_sv.V.sv_ty in
  let cc : cm_fun =
   fun cf ctx ->
    match rty with
    (* TODO: I think it is possible to factorize a lot the below match *)
    (* "Regular" ADTs *)
    | T.Adt (T.AdtId def_id, regions, types) ->
        (* Compute the expanded value *)
        let seel =
          compute_expanded_symbolic_adt_value allow_branching sv.sv_kind def_id
            regions types ctx
        in
        (* Check for branching *)
        assert (List.length seel <= 1 || allow_branching);
        (* Apply *)
        let seel = List.map (fun see -> (Some see, cf)) seel in
        apply_branching_symbolic_expansions_non_borrow config original_sv
          original_sv_place seel ctx
    (* Options *)
    | T.Adt (T.Assumed Option, regions, types) ->
        (* Sanity check *)
        assert (regions = []);
        let ty = Collections.List.to_cons_nil types in
        (* Compute the expanded value *)
        let seel =
          compute_expanded_symbolic_option_value allow_branching sv.sv_kind ty
        in

        (* Check for branching *)
        assert (List.length seel <= 1 || allow_branching);
        (* Apply *)
        let seel = List.map (fun see -> (Some see, cf)) seel in
        apply_branching_symbolic_expansions_non_borrow config original_sv
          original_sv_place seel ctx
    (* Tuples *)
    | T.Adt (T.Tuple, [], tys) ->
        (* Generate the field values *)
        let see = compute_expanded_symbolic_tuple_value sv.sv_kind tys in
        (* Apply in the context *)
        let ctx =
          apply_symbolic_expansion_non_borrow config original_sv see ctx
        in
        (* Call the continuation *)
        let expr = cf ctx in
        (* Update the synthesized program *)
        S.synthesize_symbolic_expansion_no_branching original_sv
          original_sv_place see expr
    (* Boxes *)
    | T.Adt (T.Assumed T.Box, [], [ boxed_ty ]) ->
        let see = compute_expanded_symbolic_box_value sv.sv_kind boxed_ty in
        (* Apply in the context *)
        let ctx =
          apply_symbolic_expansion_non_borrow config original_sv see ctx
        in
        (* Call the continuation *)
        let expr = cf ctx in
        (* Update the synthesized program *)
        S.synthesize_symbolic_expansion_no_branching original_sv
          original_sv_place see expr
    (* Borrows *)
    | T.Ref (region, ref_ty, rkind) ->
        expand_symbolic_value_borrow config original_sv original_sv_place region
          ref_ty rkind cf ctx
    (* Booleans *)
    | T.Bool ->
        assert allow_branching;
        expand_symbolic_bool config sv sv_place cf cf ctx
    | _ ->
        raise
          (Failure ("expand_symbolic_value: unexpected type: " ^ T.show_rty rty))
  in
  (* Debug *)
  let cc =
    comp_unit cc (fun ctx ->
        log#ldebug
          (lazy
            ("expand_symbolic_value: "
            ^ symbolic_value_to_string ctx0 sv
            ^ "\n\n- original context:\n" ^ eval_ctx_to_string ctx0
            ^ "\n\n- new context:\n" ^ eval_ctx_to_string ctx ^ "\n"));
        (* Sanity check: the symbolic value has disappeared *)
        assert (not (symbolic_value_id_in_ctx original_sv.V.sv_id ctx)))
  in
  (* Continue *)
  cc cf ctx

let expand_symbolic_int (config : C.config) (sv : V.symbolic_value)
    (sv_place : SA.mplace option) (int_type : T.integer_type)
    (tgts : (V.scalar_value * m_fun) list) (otherwise : m_fun) : m_fun =
  (* Sanity check *)
  assert (sv.V.sv_ty = T.Integer int_type);
  (* For all the branches of the switch, we expand the symbolic value
   * to the value given by the branch and execute the branch statement.
   * For the otherwise branch, we leave the symbolic value as it is
   * (because this branch doesn't precisely define which should be the
   * value of the scrutinee...) and simply execute the otherwise statement.
   *
   * First, generate the list of pairs:
   * (optional expansion, statement to execute)
   *)
  let tgts =
    List.map (fun (v, cf) -> (Some (V.SePrimitive (PV.Scalar v)), cf)) tgts
  in
  let tgts = List.append tgts [ (None, otherwise) ] in
  (* Then expand and evaluate - this generates the proper symbolic AST *)
  apply_branching_symbolic_expansions_non_borrow config sv sv_place tgts

let expand_symbolic_value_no_branching (config : C.config)
    (sv : V.symbolic_value) (sv_place : SA.mplace option) : cm_fun =
  let allow_branching = false in
  expand_symbolic_value config allow_branching sv sv_place

(** Expand all the symbolic values which contain borrows.
    Allows us to restrict ourselves to a simpler model for the projectors over
    symbolic values.
    
    Fails if doing this requires to do a branching (because we need to expand
    an enumeration with strictly more than one variant, a slice, etc.) or if
    we need to expand a recursive type (because this leads to looping).
 *)
let greedy_expand_symbolics_with_borrows (config : C.config) : cm_fun =
 fun cf ctx ->
  (* The visitor object, to look for symbolic values in the concrete environment *)
  let obj =
    object
      inherit [_] C.iter_eval_ctx

      method! visit_Symbolic _ sv =
        if ty_has_borrows ctx.type_context.type_infos sv.V.sv_ty then
          raise (FoundSymbolicValue sv)
        else ()

      (** Don't enter abstractions *)
      method! visit_abs _ _ = ()
    end
  in

  let rec expand : cm_fun =
   fun cf ctx ->
    try
      obj#visit_eval_ctx () ctx;
      (* Nothing to expand: continue *)
      cf ctx
    with FoundSymbolicValue sv ->
      (* Expand and recheck the environment *)
      log#ldebug
        (lazy
          ("greedy_expand_symbolics_with_borrows: about to expand: "
          ^ symbolic_value_to_string ctx sv));
      let cc : cm_fun =
        match sv.V.sv_ty with
        | T.Adt (AdtId def_id, _, _) ->
            (* {!expand_symbolic_value_no_branching} checks if there are branchings,
             * but we prefer to also check it here - this leads to cleaner messages
             * and debugging *)
            let def = C.ctx_lookup_type_decl ctx def_id in
            (match def.kind with
            | T.Struct _ | T.Enum ([] | [ _ ]) -> ()
            | T.Enum (_ :: _) ->
                raise
                  (Failure
                     ("Attempted to greedily expand a symbolic enumeration \
                       with > 1 variants (option \
                       [greedy_expand_symbolics_with_borrows] of [config]): "
                     ^ Print.name_to_string def.name))
            | T.Opaque ->
                raise (Failure "Attempted to greedily expand an opaque type"));
            (* Also, we need to check if the definition is recursive *)
            if C.ctx_type_decl_is_rec ctx def_id then
              raise
                (Failure
                   ("Attempted to greedily expand a recursive definition \
                     (option [greedy_expand_symbolics_with_borrows] of \
                     [config]): "
                   ^ Print.name_to_string def.name))
            else expand_symbolic_value_no_branching config sv None
        | T.Adt ((Tuple | Assumed Box), _, _) | T.Ref (_, _, _) ->
            (* Ok *)
            expand_symbolic_value_no_branching config sv None
        | T.Adt (Assumed (Vec | Option), _, _) ->
            (* We can't expand those *)
            raise (Failure "Attempted to greedily expand a Vec or an Option ")
        | T.Array _ -> raise Utils.Unimplemented
        | T.Slice _ -> raise (Failure "Can't expand symbolic slices")
        | T.TypeVar _ | Bool | Char | Never | Integer _ | Str ->
            raise (Failure "Unreachable")
      in
      (* Compose and continue *)
      comp cc expand cf ctx
  in
  (* Apply *)
  expand cf ctx

let greedy_expand_symbolic_values (config : C.config) : cm_fun =
 fun cf ctx ->
  if config.greedy_expand_symbolics_with_borrows then (
    log#ldebug (lazy "greedy_expand_symbolic_values");
    greedy_expand_symbolics_with_borrows config cf ctx)
  else cf ctx
