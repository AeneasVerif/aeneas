(* This module provides the functions which handle expansion of symbolic values.
 * For now, this file doesn't handle expansion of ⊥ values because they need
 * some path utilities for replacement. We might change that in the future (by
 * using indices to identify the values for instance). *)

module T = Types
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module L = Logging
open TypesUtils
module Inv = Invariants
module S = Synthesis
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
    (original_sv : V.symbolic_value) (expansion : symbolic_expansion)
    (ctx : C.eval_ctx) : C.eval_ctx =
  (* Symbolic values contained in the expansion might contain already ended regions *)
  let check_symbolic_no_ended = false in
  (* Prepare reborrows registration *)
  let fresh_reborrow, apply_registered_reborrows =
    prepare_reborrows config allow_reborrows
  in
  (* Visitor to apply the expansion *)
  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_abs current_abs abs =
        assert (Option.is_none current_abs);
        let current_abs = Some abs in
        super#visit_abs current_abs abs
      (** When visiting an abstraction, we remember the regions it owns to be
          able to properly reduce projectors when expanding symbolic values *)

      method! visit_ASymbolic current_abs aproj =
        let current_abs = Option.get current_abs in
        let proj_regions = current_abs.regions in
        let ancestors_regions = current_abs.ancestors_regions in
        match (aproj, proj_kind) with
        | V.AProjLoans (proj_filter, sv), LoanProj ->
            (* Check if this is the symbolic value we are looking for *)
            if same_symbolic_id sv original_sv then
              (* Apply the projector *)
              let projected_value =
                apply_proj_loans_on_symbolic_expansion proj_regions expansion
                  proj_filter original_sv.V.sv_ty
              in
              (* Replace *)
              projected_value.V.value
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
              (* TODO: we might want to compute this set once and for all before
               * diving into the abstraction *)
              let borrows_owned_by_abs = get_loans_in_abs current_abs in
              let projected_value =
                apply_proj_borrows check_symbolic_no_ended ctx fresh_reborrow
                  borrows_owned_by_abs proj_regions ancestors_regions expansion
                  proj_ty
              in
              (* Replace *)
              projected_value.V.value
            else
              (* Not the searched symbolic value: nothing to do *)
              super#visit_ASymbolic (Some current_abs) aproj
        | V.AProjLoans _, BorrowProj | V.AProjBorrows (_, _), LoanProj ->
            (* Nothing to do *)
            super#visit_ASymbolic (Some current_abs) aproj
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
    (expansion : symbolic_expansion) (ctx : C.eval_ctx) : C.eval_ctx =
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
  (* Check that we substituted *)
  assert !replaced;
  (* Return *)
  ctx

(** Apply a symbolic expansion to a context, by replacing the original
    symbolic value with its expanded value. Is valid only if the expansion
    is not a borrow (i.e., an adt...).
    
    This function does update the synthesis.
*)
let apply_symbolic_expansion_non_borrow (config : C.config)
    (original_sv : V.symbolic_value) (expansion : symbolic_expansion)
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
    
    `expand_enumerations` controls the expansion of enumerations: if false, it
    doesn't allow the expansion of enumerations *containing several variants*.
 *)
let compute_expanded_symbolic_adt_value (expand_enumerations : bool)
    (def_id : T.TypeDefId.id) (regions : T.RegionId.id T.region list)
    (types : T.rty list) (ctx : C.eval_ctx) : symbolic_expansion list =
  (* Lookup the definition and check if it is an enumeration with several
   * variants *)
  let def = C.ctx_lookup_type_def ctx def_id in
  assert (List.length regions = List.length def.T.region_params);
  (* Retrieve, for every variant, the list of its instantiated field types *)
  let variants_fields_types =
    Subst.type_def_get_instantiated_variants_fields_rtypes def regions types
  in
  (* Check if there is strictly more than one variant *)
  if List.length variants_fields_types > 1 && not expand_enumerations then
    failwith "Not allowed to expand enumerations with several variants";
  (* Initialize the expanded value for a given variant *)
  let initialize
      ((variant_id, field_types) : T.VariantId.id option * T.rty list) :
      symbolic_expansion =
    let field_values =
      List.map (fun (ty : T.rty) -> mk_fresh_symbolic_value ty) field_types
    in
    let see = SeAdt (variant_id, field_values) in
    see
  in
  (* Initialize all the expanded values of all the variants *)
  List.map initialize variants_fields_types

let compute_expanded_symbolic_tuple_value (field_types : T.rty list) :
    symbolic_expansion =
  (* Generate the field values *)
  let field_values =
    List.map (fun sv_ty -> mk_fresh_symbolic_value sv_ty) field_types
  in
  let variant_id = None in
  let see = SeAdt (variant_id, field_values) in
  see

let compute_expanded_symbolic_box_value (boxed_ty : T.rty) : symbolic_expansion
    =
  (* Introduce a fresh symbolic value *)
  let boxed_value = mk_fresh_symbolic_value boxed_ty in
  let see = SeAdt (None, [ boxed_value ]) in
  see

let expand_symbolic_value_shared_borrow (config : C.config)
    (original_sv : V.symbolic_value) (ref_ty : T.rty) (ctx : C.eval_ctx) :
    C.eval_ctx =
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
   * Returns `Some` if the symbolic value has been expanded to an asb list,
   * `None` otherwise *)
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
      | _ -> failwith "Unexpected"
    else None
  in
  (* Visitor to replace the projectors on borrows *)
  let obj =
    object
      inherit [_] C.map_eval_ctx as super

      method! visit_Symbolic env sv =
        if same_symbolic_id sv original_sv then
          let bid = fresh_borrow () in
          V.Borrow (V.SharedBorrow bid)
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

      method! visit_ASymbolic proj_regions aproj =
        match aproj with
        | AProjLoans _ ->
            (* Loans are handled later *)
            super#visit_ASymbolic proj_regions aproj
        | AProjBorrows (sv, proj_ty) -> (
            (* Check if we need to reborrow *)
            match reborrow_ashared (Option.get proj_regions) sv proj_ty with
            | None -> super#visit_ASymbolic proj_regions aproj
            | Some asb -> V.ABorrow (V.AProjSharedBorrow asb))
    end
  in
  (* Call the visitor *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Finally, replace the projectors on loans *)
  let bids = !borrows in
  assert (not (V.BorrowId.Set.is_empty bids));
  let shared_sv = mk_fresh_symbolic_value ref_ty in
  let see = SeSharedRef (bids, shared_sv) in
  let allow_reborrows = true in
  let ctx =
    apply_symbolic_expansion_to_avalues config allow_reborrows original_sv see
      ctx
  in
  (* Update the synthesized program *)
  S.synthesize_symbolic_expansion_no_branching original_sv see;
  (* Return *)
  ctx

let expand_symbolic_value_borrow (config : C.config)
    (original_sv : V.symbolic_value) (region : T.RegionId.id T.region)
    (ref_ty : T.rty) (rkind : T.ref_kind) (ctx : C.eval_ctx) : C.eval_ctx =
  (* Check that we are allowed to expand the reference *)
  assert (not (region_in_set region ctx.ended_regions));
  (* Match on the reference kind *)
  match rkind with
  | T.Mut ->
      (* Simple case: simply create a fresh symbolic value and a fresh
       * borrow id *)
      let sv = mk_fresh_symbolic_value ref_ty in
      let bid = C.fresh_borrow_id () in
      let see = SeMutRef (bid, sv) in
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
      (* Update the synthesized program *)
      S.synthesize_symbolic_expansion_no_branching original_sv see;
      (* Return *)
      ctx
  | T.Shared ->
      expand_symbolic_value_shared_borrow config original_sv ref_ty ctx

(** Expand a symbolic value which is not an enumeration with several variants
    (i.e., in a situation where it doesn't lead to branching).

    This function is used when exploring paths.
 *)
let expand_symbolic_value_no_branching (config : C.config)
    (pe : E.projection_elem) (sp : V.symbolic_value) (ctx : C.eval_ctx) :
    C.eval_ctx =
  (* Remember the initial context for printing purposes *)
  let ctx0 = ctx in
  (* Compute the expanded value - note that when doing so, we may introduce
   * fresh symbolic values in the context (which thus gets updated) *)
  let original_sv = sp in
  let rty = original_sv.V.sv_ty in
  let ctx =
    match (pe, rty) with
    (* "Regular" ADTs *)
    | ( Field (ProjAdt (def_id, _opt_variant_id), _),
        T.Adt (T.AdtId def_id', regions, types) ) -> (
        assert (def_id = def_id');
        (* Compute the expanded value - there should be exactly one because we
         * don't allow to expand enumerations with strictly more than one variant *)
        let expand_enumerations = false in
        match
          compute_expanded_symbolic_adt_value expand_enumerations def_id regions
            types ctx
        with
        | [ see ] ->
            (* Apply in the context *)
            let ctx =
              apply_symbolic_expansion_non_borrow config original_sv see ctx
            in
            (* Update the synthesized program *)
            S.synthesize_symbolic_expansion_no_branching original_sv see;
            (* Return *)
            ctx
        | _ -> failwith "Unexpected")
    (* Tuples *)
    | Field (ProjTuple arity, _), T.Adt (T.Tuple, [], tys) ->
        assert (arity = List.length tys);
        (* Generate the field values *)
        let see = compute_expanded_symbolic_tuple_value tys in
        (* Apply in the context *)
        let ctx =
          apply_symbolic_expansion_non_borrow config original_sv see ctx
        in
        (* Update the synthesized program *)
        S.synthesize_symbolic_expansion_no_branching original_sv see;
        (* Return *)
        ctx
    (* Boxes *)
    | DerefBox, T.Adt (T.Assumed T.Box, [], [ boxed_ty ]) ->
        let see = compute_expanded_symbolic_box_value boxed_ty in
        (* Apply in the context *)
        let ctx =
          apply_symbolic_expansion_non_borrow config original_sv see ctx
        in
        (* Update the synthesized program *)
        S.synthesize_symbolic_expansion_no_branching original_sv see;
        (* Return *)
        ctx
    (* Borrows *)
    | Deref, T.Ref (region, ref_ty, rkind) ->
        expand_symbolic_value_borrow config original_sv region ref_ty rkind ctx
    | _ ->
        failwith
          ("Unreachable: " ^ E.show_projection_elem pe ^ ", " ^ T.show_rty rty)
  in
  (* Debugging *)
  (* Debug *)
  log#ldebug
    (lazy
      ("expand_symbolic_value: "
      ^ symbolic_value_to_string ctx0 sp
      ^ "\n\n- original context:\n" ^ eval_ctx_to_string ctx0
      ^ "\n\n- new context:\n" ^ eval_ctx_to_string ctx ^ "\n"));
  (* Sanity check: the symbolic value has disappeared *)
  assert (not (symbolic_value_id_in_ctx original_sv.V.sv_id ctx));
  (* Return *)
  ctx

(** Expand a symbolic enumeration value.

    This might lead to branching.
 *)
let expand_symbolic_enum_value (config : C.config) (sp : V.symbolic_value)
    (ctx : C.eval_ctx) : C.eval_ctx list =
  (* Compute the expanded value - note that when doing so, we may introduce
   * fresh symbolic values in the context (which thus gets updated) *)
  let original_sv = sp in
  let rty = original_sv.V.sv_ty in
  match rty with
  (*  The value should be a "regular" ADTs *)
  | T.Adt (T.AdtId def_id, regions, types) ->
      (* Compute the expanded value - there should be exactly one because we
       * don't allow to expand enumerations with strictly more than one variant *)
      let expand_enumerations = true in
      let seel =
        compute_expanded_symbolic_adt_value expand_enumerations def_id regions
          types ctx
      in
      (* Update the synthesized program *)
      S.synthesize_symbolic_expansion_enum_branching original_sv seel;
      (* Apply in the context *)
      let apply see : C.eval_ctx =
        let ctx =
          apply_symbolic_expansion_non_borrow config original_sv see ctx
        in
        (* Sanity check: the symbolic value has disappeared *)
        assert (not (symbolic_value_id_in_ctx original_sv.V.sv_id ctx));
        (* Return *)
        ctx
      in
      List.map apply seel
  | _ -> failwith "Unexpected"
