(* This module provides the functions which handle expansion of symbolic values.
 * For now, this file doesn't handle expansion of ⊥ values because they need
 * some path utilities for replacement. We might change that in the future (by
 * using indices to identify the values for instance). *)

open Types
open Values
open Contexts
open TypesUtils
module SA = SymbolicAst
open Cps
open ValuesUtils
open InterpUtils
open InterpProjectors
open Print.EvalCtx
module S = SynthesizeSymbolic

(** The local logger *)
let log = Logging.expansion_log

(** Projector kind *)
type proj_kind = LoanProj | BorrowProj

(** Auxiliary function. Apply a symbolic expansion to avalues in a context,
    targetting a specific kind of projectors.

    [proj_kind] controls whether we apply the expansion to projectors on loans
    or projectors on borrows.

    When dealing with reference expansion, it is necessary to first apply the
    expansion on loan projectors, then on borrow projectors. The reason is that
    reducing the borrow projectors might require to perform some reborrows, in
    which case we need to lookup the corresponding loans in the context.

    If this function is called on an expansion for *shared references*, the proj
    borrows should already have been expanded.

    Note that this function is expands abstraction values and *expressions*.

    TODO: the way this function is used is a bit complex, especially because of
    the above condition. Maybe we should have:
    - 1. a generic function to expand the loan projectors
    - 2. a function to expand the borrow projectors for non-borrows
    - 3. specialized functions for mut borrows and shared borrows

    Note that 2. and 3. may have a little bit of duplicated code, but hopefully
    it would make things clearer. *)
let apply_symbolic_expansion_to_target_aevalues (span : Meta.span)
    (proj_kind : proj_kind) (original_sv : symbolic_value)
    (expansion : symbolic_expansion) (ctx : eval_ctx) : eval_ctx =
  (* Symbolic values contained in the expansion might contain already ended regions *)
  let check_symbolic_no_ended = false in
  (* Visitor to apply the expansion *)
  let obj =
    object (self)
      inherit [_] map_eval_ctx as super

      (** When visiting an abstraction, we remember the regions it owns to be
          able to properly reduce projectors when expanding symbolic values *)
      method! visit_abs current_abs abs =
        [%sanity_check] span (Option.is_none current_abs);
        let current_abs = Some abs in
        super#visit_abs current_abs abs

      (** We carefully updated {!visit_ASymbolic} so that {!visit_aproj} is
          called only on child projections (i.e., projections which appear in
          {!AEndedProjLoans}). The role of [visit_aproj] is then to check we
          don't have to expand symbolic values in child projections, because it
          should never happen *)
      method! visit_aproj current_abs aproj =
        (match aproj with
        | AProjLoans { proj; _ } | AProjBorrows { proj; _ } ->
            [%sanity_check] span (proj.sv_id <> original_sv.sv_id)
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty -> ());
        super#visit_aproj current_abs aproj

      (** We carefully updated {!visit_ESymbolic} so that {!visit_eproj} is
          called only on child projections (i.e., projections which appear in
          {!EEndedProjLoans}). The role of [visit_eproj] is then to check we
          don't have to expand symbolic values in child projections, because it
          should never happen *)
      method! visit_eproj current_abs aproj =
        (match aproj with
        | EProjLoans { proj; _ } | EProjBorrows { proj; _ } ->
            [%sanity_check] span (proj.sv_id <> original_sv.sv_id)
        | EEndedProjLoans _ | EEndedProjBorrows _ | EEmpty -> ());
        super#visit_eproj current_abs aproj

      method! visit_ASymbolic current_abs pm aproj =
        [%sanity_check] span (pm = PNone);
        let current_abs = Option.get current_abs in
        let proj_regions = current_abs.regions.owned in
        (* Explore in depth first - we won't update anything: we simply
         * want to check we don't have to expand inner symbolic value *)
        match (aproj, proj_kind) with
        | AEndedProjBorrows _, _ -> ASymbolic (pm, aproj)
        | AEndedProjLoans _, _ ->
            (* Explore the given back values to make sure we don't have to expand
             * anything in there *)
            ASymbolic (pm, self#visit_aproj (Some current_abs) aproj)
        | AProjLoans { proj; consumed; borrows }, LoanProj ->
            (* Check if this is the symbolic value we are looking for *)
            if proj.sv_id = original_sv.sv_id then (
              (* There mustn't be any consumed values *)
              [%sanity_check] span (consumed = []);
              (* Not sure what to do if the borrows are non empty: leaving
                 this as a TODO *)
              [%cassert] span (borrows = []) "Unimplemented";
              (* Apply the projector *)
              let projected_value =
                apply_proj_loans_on_symbolic_expansion span proj_regions
                  expansion original_sv.sv_ty proj.proj_ty ctx
              in
              (* Replace *)
              projected_value.value)
            else
              (* Not the searched symbolic value: nothing to do *)
              super#visit_ASymbolic (Some current_abs) pm aproj
        | AProjBorrows { proj; loans }, BorrowProj ->
            (* We should never expand a symbolic value which has consumed given
               back values (because then it means the symbolic value was consumed
               by region abstractions, and is thus inaccessible: such a value can't
               be expanded)
            *)
            [%cassert] span (loans = []) "Unreachable";
            (* Check if this is the symbolic value we are looking for *)
            if proj.sv_id = original_sv.sv_id then
              (* Convert the symbolic expansion to a value on which we can
               * apply a projector (if the expansion is a reference expansion,
               * convert it to a borrow) *)
              (* WARNING: we mustn't get there if the expansion is for a shared
               * reference. *)
              let expansion =
                symbolic_expansion_non_shared_borrow_to_value span original_sv
                  expansion
              in
              (* Apply the projector *)
              let projected_value =
                apply_proj_borrows span check_symbolic_no_ended ctx proj_regions
                  expansion proj.proj_ty
              in
              (* Replace *)
              projected_value.value
            else
              (* Not the searched symbolic value: nothing to do *)
              super#visit_ASymbolic (Some current_abs) pm aproj
        | AProjLoans _, BorrowProj | AProjBorrows _, LoanProj | AEmpty, _ ->
            (* Nothing to do *)
            ASymbolic (pm, aproj)

      method! visit_ESymbolic current_abs pm aproj =
        [%sanity_check] span (pm = PNone);
        let current_abs = Option.get current_abs in
        let proj_regions = current_abs.regions.owned in
        (* Explore in depth first - we won't update anything: we simply
         * want to check we don't have to expand inner symbolic value *)
        match (aproj, proj_kind) with
        | EEndedProjBorrows _, _ -> ESymbolic (pm, aproj)
        | EEndedProjLoans _, _ ->
            (* Explore the given back values to make sure we don't have to expand
             * anything in there *)
            ESymbolic (pm, self#visit_eproj (Some current_abs) aproj)
        | EProjLoans { proj; consumed; borrows }, LoanProj ->
            (* Check if this is the symbolic value we are looking for *)
            if proj.sv_id = original_sv.sv_id then (
              (* There mustn't be any consumed values *)
              [%sanity_check] span (consumed = []);
              (* Not sure what to do if the borrows are non empty: leaving
                 this as a TODO *)
              [%cassert] span (borrows = []) "Unimplemented";
              (* Epply the projector *)
              let projected_value =
                apply_eproj_loans_on_symbolic_expansion span proj_regions
                  expansion original_sv.sv_ty proj.proj_ty ctx
              in
              (* Replace *)
              projected_value.value)
            else
              (* Not the searched symbolic value: nothing to do *)
              super#visit_ESymbolic (Some current_abs) pm aproj
        | EProjBorrows { proj; loans }, BorrowProj ->
            (* We should never expand a symbolic value which has consumed given
               back values (because then it means the symbolic value was consumed
               by region abstractions, and is thus inaccessible: such a value can't
               be expanded)
            *)
            [%cassert] span (loans = []) "Unreachable";
            (* Check if this is the symbolic value we are looking for *)
            if proj.sv_id = original_sv.sv_id then
              (* Convert the symbolic expansion to a value on which we can
               * apply a projector (if the expansion is a reference expansion,
               * convert it to a borrow) *)
              (* WARNING: we mustn't get there if the expansion is for a shared
               * reference. *)
              let expansion =
                symbolic_expansion_non_shared_borrow_to_value span original_sv
                  expansion
              in
              (* Epply the projector *)
              let projected_value =
                apply_eproj_borrows span check_symbolic_no_ended ctx
                  proj_regions expansion proj.proj_ty
              in
              (* Replace *)
              projected_value.value
            else
              (* Not the searched symbolic value: nothing to do *)
              super#visit_ESymbolic (Some current_abs) pm aproj
        | EProjLoans _, BorrowProj | EProjBorrows _, LoanProj | EEmpty, _ ->
            (* Nothing to do *)
            ESymbolic (pm, aproj)
    end
  in
  (* Apply the expansion *)
  obj#visit_eval_ctx None ctx

(** Auxiliary function. Apply a symbolic expansion to avalues in a context. *)
let apply_symbolic_expansion_to_aevalues (span : Meta.span)
    (original_sv : symbolic_value) (expansion : symbolic_expansion)
    (ctx : eval_ctx) : eval_ctx =
  let apply_expansion proj_kind ctx =
    apply_symbolic_expansion_to_target_aevalues span proj_kind original_sv
      expansion ctx
  in
  (* First target the loan projectors, then the borrow projectors *)
  let ctx = apply_expansion LoanProj ctx in
  let ctx = apply_expansion BorrowProj ctx in
  ctx

(** Auxiliary function.

    Simply replace the symbolic values (*not avalues*) in the context with a
    given value. Will break invariants if not used properly. *)
let replace_symbolic_values (span : Meta.span) (at_most_once : bool)
    (original_sv : symbolic_value) (nv : value) (ctx : eval_ctx) : eval_ctx =
  (* Count *)
  let replaced = ref false in
  let replace () =
    if at_most_once then [%sanity_check] span (not !replaced);
    replaced := true;
    nv
  in
  (* Visitor to apply the substitution *)
  let obj =
    object
      inherit [_] map_eval_ctx as super

      method! visit_VSymbolic env spc =
        if same_symbolic_id spc original_sv then replace ()
        else super#visit_VSymbolic env spc
    end
  in
  (* Apply the substitution *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Return *)
  ctx

let apply_symbolic_expansion_non_borrow (span : Meta.span)
    (original_sv : symbolic_value) (ctx : eval_ctx)
    (expansion : symbolic_expansion) : eval_ctx =
  (* Apply the expansion to non-abstraction values *)
  let nv = symbolic_expansion_non_borrow_to_value span original_sv expansion in
  let at_most_once = false in
  let ctx =
    replace_symbolic_values span at_most_once original_sv nv.value ctx
  in
  (* Apply the expansion to abstraction values *)
  apply_symbolic_expansion_to_aevalues span original_sv expansion ctx

(** Compute the expansion of a non-builtin (e.g.: not [Box], etc.) adt value.

    The function might return a list of values if the symbolic value to expand
    is an enumeration.

    [generics]: mustn't contain erased regions. [expand_enumerations] controls
    the expansion of enumerations: if false, it doesn't allow the expansion of
    enumerations *containing several variants*. *)
let compute_expanded_symbolic_non_builtin_adt_value (span : Meta.span)
    (expand_enumerations : bool) (def_id : TypeDeclId.id)
    (generics : generic_args) (ctx : eval_ctx) : symbolic_expansion list =
  (* Lookup the definition and check if it is an enumeration with several
   * variants *)
  let def = ctx_lookup_type_decl span ctx def_id in
  [%sanity_check] span
    (List.length generics.regions = List.length def.generics.regions);
  (* Retrieve, for every variant, the list of its instantiated field types *)
  let variants_fields_types =
    Substitute.type_decl_get_instantiated_variants_fields_types def generics
  in
  (* Check if there is strictly more than one variant *)
  if List.length variants_fields_types > 1 && not expand_enumerations then
    [%craise] span "Not allowed to expand enumerations with several variants";
  (* Initialize the expanded value for a given variant *)
  let initialize ((variant_id, field_types) : VariantId.id option * rty list) :
      symbolic_expansion =
    let field_values =
      List.map
        (fun (ty : rty) -> mk_fresh_symbolic_value span ctx ty)
        field_types
    in
    let see = SeAdt (variant_id, field_values) in
    see
  in
  (* Initialize all the expanded values of all the variants *)
  List.map initialize variants_fields_types

let compute_expanded_symbolic_tuple_value (span : Meta.span) (ctx : eval_ctx)
    (field_types : rty list) : symbolic_expansion =
  (* Generate the field values *)
  let field_values =
    List.map (fun sv_ty -> mk_fresh_symbolic_value span ctx sv_ty) field_types
  in
  let variant_id = None in
  let see = SeAdt (variant_id, field_values) in
  see

let compute_expanded_symbolic_box_value (span : Meta.span) (ctx : eval_ctx)
    (boxed_ty : rty) : symbolic_expansion =
  (* Introduce a fresh symbolic value *)
  let boxed_value = mk_fresh_symbolic_value span ctx boxed_ty in
  let see = SeAdt (None, [ boxed_value ]) in
  see

(** Compute the expansion of an adt value.

    The function might return a list of values if the symbolic value to expand
    is an enumeration.

    [generics]: the regions shouldn't have been erased. [expand_enumerations]
    controls the expansion of enumerations: if [false], it doesn't allow the
    expansion of enumerations *containing several variants*. *)
let compute_expanded_symbolic_adt_value (span : Meta.span)
    (expand_enumerations : bool) (adt_id : type_id) (generics : generic_args)
    (ctx : eval_ctx) : symbolic_expansion list =
  match (adt_id, generics.regions, generics.types) with
  | TAdtId def_id, _, _ ->
      compute_expanded_symbolic_non_builtin_adt_value span expand_enumerations
        def_id generics ctx
  | TTuple, [], _ ->
      [ compute_expanded_symbolic_tuple_value span ctx generics.types ]
  | TBuiltin TBox, [], [ boxed_ty ] ->
      [ compute_expanded_symbolic_box_value span ctx boxed_ty ]
  | _ ->
      [%craise] span
        "compute_expanded_symbolic_adt_value: unexpected combination"

let expand_symbolic_value_shared_borrow (span : Meta.span)
    (original_sv : symbolic_value) (original_sv_place : SA.mplace option)
    (ref_ty : rty) : cm_fun =
 fun ctx ->
  (* First, replace the projectors on borrows. *)
  let bid = ctx.fresh_borrow_id () in
  (* The fresh symbolic value for the shared value *)
  let shared_sv = mk_fresh_symbolic_value span ctx ref_ty in
  (* Small utility used on shared borrows in abstractions (regular borrow
     projector and asb).
     Returns [Some] if the symbolic value has been expanded to an asb list,
     [None] otherwise *)
  let reborrow_ashared proj_regions (proj : symbolic_proj) :
      abstract_shared_borrows option =
    if proj.sv_id = original_sv.sv_id then
      match proj.proj_ty with
      | TRef (r, ref_ty, RShared) ->
          (* Projector over the shared value *)
          let shared_asb =
            AsbProjReborrows { sv_id = shared_sv.sv_id; proj_ty = ref_ty }
          in
          (* Check if the region is in the set of projected regions *)
          if region_in_set r proj_regions then
            (* In the set: we need to reborrow *)
            let sid = ctx.fresh_shared_borrow_id () in
            Some [ AsbBorrow (bid, sid); shared_asb ]
          else (* Not in the set: ignore *)
            Some [ shared_asb ]
      | _ -> [%craise] span "Unexpected"
    else None
  in
  (* Visitor to replace the projectors on borrows *)
  let obj =
    object (self)
      inherit [_] map_eval_ctx as super

      method! visit_VSymbolic env sv =
        if same_symbolic_id sv original_sv then
          let sid = ctx.fresh_shared_borrow_id () in
          VBorrow (VSharedBorrow (bid, sid))
        else super#visit_VSymbolic env sv

      method! visit_EAbs proj_regions abs =
        [%sanity_check] span (Option.is_none proj_regions);
        let proj_regions = Some abs.regions.owned in
        super#visit_EAbs proj_regions abs

      (* Note that there is no equivalent [EProjSharedBorrow] (we don't need to track shared borrows/loans
         in abstraction expressions *)
      method! visit_AProjSharedBorrow proj_regions asb =
        let expand_asb (asb : abstract_shared_borrow) : abstract_shared_borrows
            =
          match asb with
          | AsbBorrow _ -> [ asb ]
          | AsbProjReborrows proj -> (
              match reborrow_ashared (Option.get proj_regions) proj with
              | None -> [ asb ]
              | Some asb -> asb)
        in
        let asb = List.concat (List.map expand_asb asb) in
        AProjSharedBorrow asb

      (** We carefully updated {!visit_ASymbolic} so that {!visit_aproj} is
          called only on child projections (i.e., projections which appear in
          {!AEndedProjLoans}). The role of [visit_aproj] is then to check we
          don't have to expand symbolic values in child projections, because it
          should never happen *)
      method! visit_aproj proj_regions aproj =
        (match aproj with
        | AProjLoans { proj; _ } | AProjBorrows { proj; _ } ->
            [%sanity_check] span (proj.sv_id <> original_sv.sv_id)
        | AEndedProjLoans _ | AEndedProjBorrows _ | AEmpty -> ());
        super#visit_aproj proj_regions aproj

      (** We carefully updated {!visit_ESymbolic} so that {!visit_aproj} is
          called only on child projections (i.e., projections which appear in
          {!EEndedProjLoans}). The role of [visit_eproj] is then to check we
          don't have to expand symbolic values in child projections, because it
          should never happen *)
      method! visit_eproj proj_regions aproj =
        (match aproj with
        | EProjLoans { proj; _ } | EProjBorrows { proj; _ } ->
            [%sanity_check] span (proj.sv_id <> original_sv.sv_id)
        | EEndedProjLoans _ | EEndedProjBorrows _ | EEmpty -> ());
        super#visit_eproj proj_regions aproj

      method! visit_ASymbolic proj_regions pm aproj =
        [%sanity_check] span (pm = PNone);
        match aproj with
        | AEndedProjBorrows _ | AEmpty ->
            (* We ignore borrows *) ASymbolic (pm, aproj)
        | AProjLoans _ ->
            (* Loans are handled later *)
            ASymbolic (pm, aproj)
        | AProjBorrows { proj; loans } -> (
            (* We should never expand a symbolic value which has consumed given
               back values (because then it means the symbolic value was consumed
               by region abstractions, and is thus inaccessible: such a value can't
               be expanded)
            *)
            [%cassert] span (loans = []) "Unreachable";
            (* Check if we need to reborrow *)
            match reborrow_ashared (Option.get proj_regions) proj with
            | None -> super#visit_ASymbolic proj_regions pm aproj
            | Some asb -> ABorrow (AProjSharedBorrow asb))
        | AEndedProjLoans _ ->
            (* Sanity check: make sure there is nothing to expand inside the
             * children projections *)
            ASymbolic (pm, self#visit_aproj proj_regions aproj)

      method! visit_ESymbolic proj_regions pm aproj =
        [%sanity_check] span (pm = PNone);
        match aproj with
        | EEndedProjBorrows _ | EEmpty ->
            (* We ignore borrows *) ESymbolic (pm, aproj)
        | EProjLoans _ ->
            (* Loans are handled later *)
            ESymbolic (pm, aproj)
        | EProjBorrows { proj = _; loans } ->
            (* We should never expand a symbolic value which has consumed given
               back values (because then it means the symbolic value was consumed
               by region abstractions, and is thus inaccessible: such a value can't
               be expanded)
            *)
            [%cassert] span (loans = []) "Unreachable";
            (* No need to check for reborrows of shared values: we don't track
               them in abstraction expressions *)
            super#visit_ESymbolic proj_regions pm aproj
        | EEndedProjLoans _ ->
            (* Sanity check: make sure there is nothing to expand inside the
             * children projections *)
            ESymbolic (pm, self#visit_eproj proj_regions aproj)
    end
  in
  (* Call the visitor *)
  let ctx = obj#visit_eval_ctx None ctx in
  (* Finally, replace the projectors on loans *)
  let see = SeSharedRef (bid, shared_sv) in
  let ctx = apply_symbolic_expansion_to_aevalues span original_sv see ctx in
  ( ctx,
    (* Update the synthesized program *)
    S.synthesize_symbolic_expansion_no_branching span original_sv
      original_sv_place see )

(** TODO: simplify and merge with the other expansion function *)
let expand_symbolic_value_borrow (span : Meta.span)
    (original_sv : symbolic_value) (original_sv_place : SA.mplace option)
    (region : region) (ref_ty : rty) (rkind : ref_kind) : cm_fun =
 fun ctx ->
  [%sanity_check] span (region <> RErased);
  (* Check that we are allowed to expand the reference *)
  [%sanity_check] span (not (region_in_set region ctx.ended_regions));
  (* Match on the reference kind *)
  match rkind with
  | RMut ->
      (* Simple case: simply create a fresh symbolic value and a fresh
       * borrow id *)
      let sv = mk_fresh_symbolic_value span ctx ref_ty in
      let bid = ctx.fresh_borrow_id () in
      let see = SeMutRef (bid, sv) in
      (* Expand the symbolic values - we simply perform a substitution (and
       * check that we perform exactly one substitution) *)
      let nv =
        symbolic_expansion_non_shared_borrow_to_value span original_sv see
      in
      let at_most_once = true in
      let ctx =
        replace_symbolic_values span at_most_once original_sv nv.value ctx
      in
      (* Expand the symbolic avalues *)
      let ctx = apply_symbolic_expansion_to_aevalues span original_sv see ctx in
      (* Apply the continuation *)
      ( ctx,
        fun e ->
          (* Update the synthesized program *)
          S.synthesize_symbolic_expansion_no_branching span original_sv
            original_sv_place see e )
  | RShared ->
      expand_symbolic_value_shared_borrow span original_sv original_sv_place
        ref_ty ctx

let expand_symbolic_bool (span : Meta.span) (sv : symbolic_value)
    (sv_place : SA.mplace option) :
    eval_ctx -> (eval_ctx * eval_ctx) * (SA.expr * SA.expr -> SA.expr) =
 fun ctx ->
  (* Compute the expanded value *)
  let original_sv = sv in
  let rty = original_sv.sv_ty in
  [%sanity_check] span (rty = TLiteral TBool);
  (* Expand the symbolic value to true or false and continue execution *)
  let see_true = SeLiteral (VBool true) in
  let see_false = SeLiteral (VBool false) in
  let seel = [ Some see_true; Some see_false ] in
  (* Apply the symbolic expansion *)
  let apply_expansion = apply_symbolic_expansion_non_borrow span sv ctx in
  let ctx_true = apply_expansion see_true in
  let ctx_false = apply_expansion see_false in
  (* Compute the continuation to build the expression *)
  let cf (e0, e1) =
    S.synthesize_symbolic_expansion span sv sv_place seel [ e0; e1 ]
  in
  (* Return *)
  ((ctx_true, ctx_false), cf)

let expand_symbolic_value_no_branching (span : Meta.span) (sv : symbolic_value)
    (sv_place : SA.mplace option) : cm_fun =
 fun ctx ->
  (* Debug *)
  [%ltrace symbolic_value_to_string ctx sv];
  (* Remember the initial context for printing purposes *)
  let ctx0 = ctx in
  (* Compute the expanded value - note that when doing so, we may introduce
   * fresh symbolic values in the context (which thus gets updated) *)
  let original_sv = sv in
  let original_sv_place = sv_place in
  let rty = original_sv.sv_ty in
  let ctx, cc =
    match rty with
    (* ADTs *)
    | TAdt { id = adt_id; generics } ->
        (* Compute the expanded value *)
        let allow_branching = false in
        let seel =
          compute_expanded_symbolic_adt_value span allow_branching adt_id
            generics ctx
        in
        (* There should be exacly one branch *)
        let see = Collections.List.to_cons_nil seel in
        (* Apply in the context *)
        let ctx =
          apply_symbolic_expansion_non_borrow span original_sv ctx see
        in
        (* Return*)
        ( ctx,
          (* Update the synthesized program *)
          S.synthesize_symbolic_expansion_no_branching span original_sv
            original_sv_place see )
    (* Borrows *)
    | TRef (region, ref_ty, rkind) ->
        expand_symbolic_value_borrow span original_sv original_sv_place region
          ref_ty rkind ctx
    | _ ->
        [%craise] span
          ("expand_symbolic_value_no_branching: unexpected type: "
         ^ show_rty rty)
  in
  (* Debug *)
  [%ltrace
    symbolic_value_to_string ctx0 sv
    ^ "\n\n- original context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx0
    ^ "\n\n- new context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];
  (* Sanity check: the symbolic value has disappeared *)
  [%sanity_check] span (not (symbolic_value_id_in_ctx original_sv.sv_id ctx));
  (* Return *)
  (ctx, cc)

let expand_symbolic_adt (span : Meta.span) (sv : symbolic_value)
    (sv_place : SA.mplace option) :
    eval_ctx -> eval_ctx list * (SA.expr list -> SA.expr) =
 fun ctx ->
  (* Debug *)
  [%ltrace symbolic_value_to_string ctx sv];
  (* Compute the expanded value - note that when doing so, we may introduce
   * fresh symbolic values in the context (which thus gets updated) *)
  let original_sv = sv in
  let original_sv_place = sv_place in
  let rty = original_sv.sv_ty in
  (* Execute *)
  match rty with
  (* ADTs *)
  | TAdt { id = adt_id; generics } ->
      let allow_branching = true in
      (* Compute the expanded value *)
      let seel =
        compute_expanded_symbolic_adt_value span allow_branching adt_id generics
          ctx
      in
      (* Apply *)
      let ctx_branches =
        List.map (apply_symbolic_expansion_non_borrow span sv ctx) seel
      in
      ( ctx_branches,
        S.synthesize_symbolic_expansion span sv original_sv_place
          (List.map (fun el -> Some el) seel) )
  | _ -> [%craise] span ("expand_symbolic_adt: unexpected type: " ^ show_rty rty)

let expand_symbolic_int (span : Meta.span) (sv : symbolic_value)
    (sv_place : SA.mplace option) (int_type : integer_type)
    (tgts : scalar_value list) :
    eval_ctx -> (eval_ctx list * eval_ctx) * (SA.expr list * SA.expr -> SA.expr)
    =
 fun ctx ->
  (* Sanity check *)
  (match int_type with
  | Signed int_type -> [%sanity_check] span (sv.sv_ty = TLiteral (TInt int_type))
  | Unsigned int_type ->
      [%sanity_check] span (sv.sv_ty = TLiteral (TUInt int_type)));
  (* For all the branches of the switch, we expand the symbolic value
   * to the value given by the branch and execute the branch statement.
   * For the otherwise branch, we leave the symbolic value as it is
   * (because this branch doesn't precisely define which should be the
   * value of the scrutinee...) and simply execute the otherwise statement.
   *)
  (* Substitute the symbolic values to generate the contexts in the branches *)
  let seel = List.map (fun v -> SeLiteral (VScalar v)) tgts in
  let ctx_branches =
    List.map (apply_symbolic_expansion_non_borrow span sv ctx) seel
  in
  let ctx_otherwise = ctx in
  (* Update the symbolic ast *)
  let cf (el, e) =
    let seel = List.map (fun x -> Some x) seel in
    S.synthesize_symbolic_expansion span sv sv_place (seel @ [ None ])
      (el @ [ e ])
  in
  ((ctx_branches, ctx_otherwise), cf)

(** Expand all the symbolic values which contain borrows. Allows us to restrict
    ourselves to a simpler model for the projectors over symbolic values.

    Fails if doing this requires to do a branching (because we need to expand an
    enumeration with strictly more than one variant, a slice, etc.) or if we
    need to expand a recursive type (because this leads to looping). *)
let greedy_expand_symbolics_with_borrows (span : Meta.span) : cm_fun =
 fun ctx ->
  (* The visitor object, to look for symbolic values in the concrete environment *)
  let obj =
    object
      inherit [_] iter_eval_ctx

      method! visit_VSymbolic _ sv =
        if
          ValuesUtils.symbolic_value_is_greedily_expandable (Some span)
            ctx.type_ctx.type_decls ctx.type_ctx.type_infos sv
        then raise (FoundSymbolicValue sv)
        else ()

      (** Don't enter abstractions *)
      method! visit_abs _ _ = ()
    end
  in

  let rec expand : cm_fun =
   fun ctx ->
    try
      (* We reverse the environment before exploring it - this way the values
         get expanded in a more "logical" order (this is only for convenience) *)
      obj#visit_env () (List.rev ctx.env);
      [%ltrace "no value to expand"];
      (* Nothing to expand: continue *)
      (ctx, fun e -> e)
    with FoundSymbolicValue sv ->
      (* Expand and recheck the environment *)
      [%ltrace "about to expand: " ^ symbolic_value_to_string ctx sv];
      let ctx, cc =
        match sv.sv_ty with
        | TAdt { id = TAdtId def_id; _ } ->
            (* {!expand_symbolic_value_no_branching} checks if there are branchings,
             * but we prefer to also check it here - this leads to cleaner messages
             * and debugging *)
            let def = ctx_lookup_type_decl span ctx def_id in
            begin
              match def.kind with
              | Struct _ | Enum ([] | [ _ ]) -> ()
              | Enum (_ :: _) ->
                  [%craise] span
                    ("Attempted to greedily expand a symbolic enumeration with \
                      > 1 variants (option \
                      [greedy_expand_symbolics_with_borrows] of [config]): "
                    ^ name_to_string ctx def.item_meta.name)
              | Alias _ | Opaque | TDeclError _ ->
                  [%craise] span
                    "Attempted to greedily expand an alias or opaque type"
              | Union _ -> [%craise] span "Unions are not supported"
            end;
            (* Also, we need to check if the definition is recursive *)
            if ctx_type_decl_is_rec ctx def_id then
              [%craise] span
                ("Attempted to greedily expand a recursive definition (option \
                  [greedy_expand_symbolics_with_borrows] of [config]): "
                ^ name_to_string ctx def.item_meta.name)
            else expand_symbolic_value_no_branching span sv None ctx
        | TAdt { id = TTuple | TBuiltin TBox; _ } | TRef (_, _, _) ->
            (* Ok *)
            expand_symbolic_value_no_branching span sv None ctx
        | TAdt { id = TBuiltin (TArray | TSlice | TStr); _ } ->
            (* We can't expand those *)
            [%craise] span
              "Attempted to greedily expand an ADT which can't be expanded "
        | _ -> [%craise] span "Unreachable"
      in
      (* *)
      [%ltrace
        "after expansion:\n" ^ eval_ctx_to_string ~span:(Some span) ctx ^ "\n"];
      (* Compose and continue *)
      comp cc (expand ctx)
  in
  (* Apply *)
  expand ctx

let greedy_expand_symbolic_values (span : Meta.span) : cm_fun =
 fun ctx ->
  if Config.greedy_expand_symbolics_with_borrows then (
    log#ltrace (lazy "greedy_expand_symbolic_values");
    greedy_expand_symbolics_with_borrows span ctx)
  else (ctx, fun e -> e)
