open Types
open Values
open Expressions
open Contexts
open Cps
open ValuesUtils
open InterpUtils
open InterpBorrowsCore
open InterpBorrows
open InterpExpansion
module Synth = SynthesizeSymbolic

(** The local logger *)
let log = Logging.paths_log

(** Paths *)

(** When we fail reading from or writing to a path, it might be because we need
    to update the environment by ending borrows, expanding symbolic values, etc.
    The following type is used to convey this information.

    TODO: compare with borrow_lres? *)
type path_fail_kind =
  | FailSharedLoan of BorrowId.id
      (** Failure because we couldn't go inside a shared loan *)
  | FailMutLoan of BorrowId.id
      (** Failure because we couldn't go inside a mutable loan *)
  | FailReservedMutBorrow of (BorrowId.id * SharedBorrowId.id)
      (** Failure because we couldn't go inside a reserved mutable borrow (which
          should get activated) *)
  | FailSymbolic of place * symbolic_value
      (** Failure because we need to enter a symbolic value (and thus need to
          expand it).

          We store the place at which the symbolic value was found, which is
          useful for the synthesis. *)
  | FailBottom of place * projection_elem
      (** Failure because we need to enter an any value - we can expand Bottom
          values if they are left values.

          We store the place at which the bottom value appears (we need it to
          properly update the Bottom if we need to expand it, for instance if we
          want to expand a bottom pair to a pair of bottoms), together with the
          projection element that could not be evaluated. *)
  | FailBorrow of borrow_content
      (** We got stuck because we couldn't enter a borrow *)
[@@deriving show]

(** Result of evaluating a path (reading from a path/writing to a path)

    Note that when we fail, we return information used to update the
    environment, as well as the *)
type 'a path_access_result = ('a, path_fail_kind) result
(** The result of reading from/writing to a place *)

type projection_access = {
  enter_shared_loans : bool;
  enter_mut_borrows : bool;
  lookup_shared_borrows : bool;
}

(* Projects a value with a `projection_elem`. Returns the projected value and a
   continuation that propagates any changes to the projected value back
   to the original one.

   The optional loan id we output is the id of the shared loan immediately above
   the value, if there is one. We need this when creating shared references:
   we introduce a shared loan if and only if there is not already one (TODO:
   make this cleaner).
*)
let rec project_value (span : Meta.span) (access : projection_access)
    (ek : exploration_kind) (current_place : place) (ctx : eval_ctx)
    (pe : projection_elem) (v : tvalue) :
    (loan_id option * tvalue * (eval_ctx * tvalue -> eval_ctx * tvalue))
    path_access_result =
  match (pe, v.value, v.ty) with
  | ( Field (ProjAdt (def_id, opt_variant_id), field_id),
      VAdt adt,
      TAdt { id = TAdtId def_id'; _ } ) -> begin
      (* Check consistency *)
      [%sanity_check] span (def_id = def_id');
      [%sanity_check] span (opt_variant_id = adt.variant_id);
      (* Actually project *)
      let fv = FieldId.nth adt.fields field_id in
      let backward (ctx, updated) =
        (* Update the field value *)
        let nvalues = FieldId.update_nth adt.fields field_id updated in
        let value = VAdt { adt with fields = nvalues } in
        (ctx, { v with value })
      in
      Ok (None, fv, backward)
    end
  (* Tuples *)
  | Field (ProjTuple arity, field_id), VAdt adt, TAdt { id = TTuple; _ } ->
  begin
      [%sanity_check] span (arity = List.length adt.fields);
      let fv = FieldId.nth adt.fields field_id in
      let backward (ctx, updated) =
        (* Update the field value *)
        let nvalues = FieldId.update_nth adt.fields field_id updated in
        let value = VAdt { adt with fields = nvalues } in
        (ctx, { v with value })
      in
      Ok (None, fv, backward)
    end
  | Field ((ProjAdt (_, _) | ProjTuple _), _), VBottom, _ ->
      (* If we reach Bottom, it may mean we need to expand an uninitialized
       * enumeration value *)
      Error (FailBottom (current_place, pe))
  (* Symbolic value: needs to be expanded *)
  | _, VSymbolic sp, _ ->
      (* Expand the symbolic value *)
      Error (FailSymbolic (current_place, sp))
  (* Box dereferencement *)
  | ( Deref,
      VAdt { variant_id = None; fields = [ fv ] },
      TAdt { id = TBuiltin TBox; _ } ) -> begin
      (* We allow moving outside of boxes. In practice, this kind of
       * manipulations should happen only inside unsafe code, so
       * it shouldn't happen due to user code, and we leverage it
       * when implementing box dereferencement for the concrete
       * interpreter *)
      let backward (ctx, updated) =
        let value = VAdt { variant_id = None; fields = [ updated ] } in
        (ctx, { v with value })
      in
      Ok (None, fv, backward)
    end
  (* Borrows *)
  | Deref, VBorrow bc, _ ->
      (* Compute the projected value to explore and a backward function to update the result *)
      let res : _ path_access_result =
        match bc with
        | VSharedBorrow _ when not access.lookup_shared_borrows ->
            Error (FailBorrow bc)
        | VSharedBorrow (bid, _) -> begin
            (* Lookup the loan content, and explore from there *)
            match ctx_lookup_loan span ek bid ctx with
            | _, Concrete (VMutLoan _) ->
                [%craise] span "Expected a shared loan"
            | _, Concrete (VSharedLoan (bid, sv)) ->
                (* Return the shared value *)
                Ok
                  ( Some bid,
                    sv,
                    fun (ctx, updated) ->
                      let ctx =
                        update_loan span ek bid (VSharedLoan (bid, updated)) ctx
                      in
                      (ctx, v) )
            | ( _,
                Abstract
                  ( AMutLoan _
                  | AEndedMutLoan _
                  | AEndedSharedLoan _
                  | AIgnoredMutLoan _
                  | AEndedIgnoredMutLoan _
                  | AIgnoredSharedLoan _ ) ) ->
                [%craise] span "Expected a shared (abstraction) loan"
            | _, Abstract (ASharedLoan (pm, bid, sv, _av)) -> begin
                (* Sanity check: projection markers can only appear when we're doing a join *)
                [%sanity_check] span (pm = PNone);
                (* Return the shared value *)
                Ok
                  ( Some bid,
                    sv,
                    fun (ctx, updated) ->
                      let av =
                        match ctx_lookup_loan span ek bid ctx with
                        | _, Abstract (ASharedLoan (_, _, _, av)) -> av
                        | _ -> [%craise] span "Unexpected"
                      in
                      let ctx =
                        update_aloan span ek bid
                          (ASharedLoan (pm, bid, updated, av))
                          ctx
                      in
                      (ctx, v) )
              end
          end
        | VReservedMutBorrow (bid, sid) ->
            Error (FailReservedMutBorrow (bid, sid))
        | VMutBorrow _ when not access.enter_mut_borrows ->
            Error (FailBorrow bc)
        | VMutBorrow (bid, bv) ->
            Ok
              ( None,
                bv,
                fun (ctx, updated) ->
                  let value = VBorrow (VMutBorrow (bid, updated)) in
                  (ctx, { v with value }) )
      in
      res
  | _, VLoan lc, _ -> begin
      match lc with
      | VMutLoan bid -> Error (FailMutLoan bid)
      | VSharedLoan (bids, _) when not access.enter_shared_loans ->
          Error (FailSharedLoan bids)
      | VSharedLoan (bids, sv) -> begin
          (* If we can enter a shared loan, we ignore the loan. Pay attention
             to the fact that we need to reexplore the *whole* place (i.e, we
             mustn't ignore the current projection element).

             Remark about the [current_place]: if we dive into a shared loan,
             the [current_place] doesn't unambiguously designate this value.
             This is not an issue in any of the two situations in which we
             use this current place:
             - if we use it in the synthesis, it is only to drive some heuristics,
               meaning that it is not important for the soundness
             - we can also use it to expand bottom values, but bottom values
               can not appear inside of shared loans
          *)
          match project_value span access ek current_place ctx pe sv with
          | Error err -> Error err
          | Ok (lid, fv, backward) ->
              let backward (ctx, updated) =
                let ctx, updated = backward (ctx, updated) in
                let value = VLoan (VSharedLoan (bids, updated)) in
                (ctx, { v with value })
              in
              Ok (lid, fv, backward)
        end
    end
  | _, VBottom, _ -> [%craise] span "Can not apply a projection to the ⊥ value"
  | pe, ((VLiteral _ | VAdt _ | VBorrow _) as v), ty -> begin
      let pe = "- pe: " ^ show_projection_elem pe in
      let v = "- v:\n" ^ show_value v in
      let ty = "- ty:\n" ^ show_ety ty in
      [%craise] span ("Inconsistent projection:\n" ^ pe ^ "\n" ^ v ^ "\n" ^ ty)
    end

(** Generic function to access (read/write) the value inside a place, provided
    the place **does not refer to a global** (globals are handled elsewhere).

    We return the read value and a backward function that propagates any changes
    to the projected value back to the original local. *)
let rec access_place (span : Meta.span) (access : projection_access)
    (ek : exploration_kind) (ctx : eval_ctx) (p : place) :
    (loan_id option * tvalue * (eval_ctx * tvalue -> eval_ctx * tvalue))
    path_access_result =
  match p.kind with
  | PlaceLocal var_id ->
      (* Lookup the variable's value *)
      let v = ctx_lookup_var_value span ctx var_id in
      let backward (ctx, updated) =
        let ctx = ctx_update_var_value span ctx var_id updated in
        (* Type checking *)
        if updated.ty <> v.ty then (
          [%ltrace
            "Not the same type:\n- nv.ty: " ^ show_ety updated.ty ^ "\n- v.ty: "
            ^ show_ety v.ty];
          [%craise] span
            "Assertion failed: new value doesn't have the same type as its \
             destination");
        (ctx, updated)
      in
      Ok (None, v, backward)
  | PlaceProjection (p', pe) -> begin
      match access_place span access ek ctx p' with
      | Error err -> Error err
      | Ok (_, v, backward) -> begin
          match project_value span access ek p' ctx pe v with
          | Error err -> Error err
          | Ok (lid, pv, new_back) -> begin
              let backward = Core.Fn.compose backward new_back in
              Ok (lid, pv, backward)
            end
        end
    end
  | PlaceGlobal _ -> [%craise] span "Unexpected access to a global"

(** Generic function to access (read/write) the value at a given place, provided
    the place **does not refer to a global** (globals are handled elsewhere).

    We return the value we read at the place and the (eventually) updated
    environment, if we managed to access the place, or the precise reason why we
    failed. *)
let access_update_place (span : Meta.span) (access : projection_access)
    (* Function to (eventually) update the value we find *)
      (update : tvalue -> tvalue) (p : place) (ctx : eval_ctx) :
    (eval_ctx * loan_id option * tvalue) path_access_result =
  (* For looking up/updating shared loans *)
  let ek : exploration_kind =
    { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }
  in
  (* Apply the projection *)
  match access_place span access ek ctx p with
  | Error err -> Error err
  | Ok (lid, v, backward) ->
      let nv = update v in
      (* Update the ctx with the updated value *)
      let ctx, _ = backward (ctx, nv) in
      Ok (ctx, lid, v)

type access_kind =
  | Read  (** We can go inside borrows and loans *)
  | Write  (** Don't enter shared borrows or shared loans *)
  | Move  (** Don't enter borrows or loans *)

let access_kind_to_projection_access (access : access_kind) : projection_access
    =
  match access with
  | Read ->
      {
        enter_shared_loans = true;
        enter_mut_borrows = true;
        lookup_shared_borrows = true;
      }
  | Write ->
      {
        enter_shared_loans = false;
        enter_mut_borrows = true;
        lookup_shared_borrows = false;
      }
  | Move ->
      {
        enter_shared_loans = false;
        enter_mut_borrows = false;
        lookup_shared_borrows = false;
      }

(** Attempt to read the value at a given place, provided the place **does not
    refer to a global** (globals are handled elsewhere).

    Note that we only access the value at the place, and do not check that the
    value is "well-formed" (for instance that it doesn't contain bottoms). *)
let try_read_place (span : Meta.span) (access : access_kind) (p : place)
    (ctx : eval_ctx) : (loan_id option * tvalue) path_access_result =
  let access = access_kind_to_projection_access access in
  (* The update function is the identity *)
  let update v = v in
  match access_update_place span access update p ctx with
  | Error err -> Error err
  | Ok (ctx1, lid, read_value) ->
      (* Note that we ignore the new environment: it should be the same as the
         original one.
      *)
      (if !Config.sanity_checks then
         if ctx1.env <> ctx.env then
           let msg =
             "Unexpected environment update:\nNew environment:\n"
             ^ show_env ctx1.env ^ "\n\nOld environment:\n" ^ show_env ctx.env
           in
           [%craise] span msg);
      Ok (lid, read_value)

let read_place (span : Meta.span) (access : access_kind) (p : place)
    (ctx : eval_ctx) : loan_id option * tvalue =
  match try_read_place span access p ctx with
  | Error e -> [%craise] span ("Unreachable: " ^ show_path_fail_kind e)
  | Ok (lid, v) -> (lid, v)

(** Attempt to update the value at a given place, provided the place **does not
    refer to a global** (globals are handled elsewhere). *)
let try_write_place (span : Meta.span) (access : access_kind) (p : place)
    (nv : tvalue) (ctx : eval_ctx) : eval_ctx path_access_result =
  let access = access_kind_to_projection_access access in
  (* The update function substitutes the value with the new value *)
  let update _ = nv in
  match access_update_place span access update p ctx with
  | Error err -> Error err
  | Ok (ctx, _, _) ->
      (* We ignore the read value *)
      Ok ctx

let write_place (span : Meta.span) (access : access_kind) (p : place)
    (nv : tvalue) (ctx : eval_ctx) : eval_ctx =
  match try_write_place span access p nv ctx with
  | Error e -> [%craise] span ("Unreachable: " ^ show_path_fail_kind e)
  | Ok ctx -> ctx

let compute_expanded_bottom_adt_value (span : Meta.span) (ctx : eval_ctx)
    (def_id : TypeDeclId.id) (opt_variant_id : VariantId.id option)
    (generics : generic_args) : tvalue =
  [%sanity_check] span (TypesUtils.generic_args_only_erased_regions generics);
  (* Lookup the definition and check if it is an enumeration - it
     should be an enumeration if and only if the projection element
     is a field projection with *some* variant id. Retrieve the list
     of fields at the same time. *)
  let def = ctx_lookup_type_decl span ctx def_id in
  [%sanity_check] span
    (List.length generics.regions = List.length def.generics.regions);
  (* Compute the field types *)
  let field_types =
    Substitute.type_decl_get_instantiated_field_etypes def opt_variant_id
      generics
  in
  (* Initialize the expanded value *)
  let fields = List.map (mk_bottom span) field_types in
  let av = VAdt { variant_id = opt_variant_id; fields } in
  let ty = TAdt { id = TAdtId def_id; generics } in
  { value = av; ty }

let compute_expanded_bottom_tuple_value (span : Meta.span)
    (field_types : ety list) : tvalue =
  (* Generate the field values *)
  let fields = List.map (mk_bottom span) field_types in
  let v = VAdt { variant_id = None; fields } in
  let generics = TypesUtils.mk_generic_args [] field_types [] [] in
  let ty = TAdt { id = TTuple; generics } in
  { value = v; ty }

(** Auxiliary helper to expand {!Bottom} values.

    During compilation, rustc desaggregates the ADT initializations. The
    consequence is that the following rust code:
    {[
      let x = Cons a b;
    ]}

    Looks like this in MIR:
    {[
      (x as Cons).0 = a;
      (x as Cons).1 = b;
      set_discriminant(x, 0); // If [Cons] is the variant of index 0
    ]}

    The consequence is that we may sometimes need to write fields to values
    which are currently {!Bottom}. When doing this, we first expand the value
    to, say, [Cons Bottom Bottom] (note that field projection contains
    information about which variant we should project to, which is why we *can*
    set the variant index when writing one of its fields).

    Parameters:
    - [p]: the place where the {!Bottom} value appears
    - [pe]: the projection element we wish to evaluate *)
let expand_bottom_value_from_projection (span : Meta.span)
    (access : access_kind) (p : place) (pe : projection_elem) (ctx : eval_ctx) :
    eval_ctx =
  (* Debugging *)
  [%ltrace "pe: " ^ show_projection_elem pe ^ "\n" ^ "ty: " ^ show_ety p.ty];
  (* Compute the expanded value.
     The type of the {!Bottom} value should be a tuple or an ADT
     Note that the projection element we got stuck at should be a
     field projection, and gives the variant id if the {!Bottom} value
     is an enumeration value.
     Also, the expanded value should be the proper ADT variant or a tuple
     with the proper arity, with all the fields initialized to {!Bottom}
  *)
  let nv =
    match (pe, p.ty) with
    (* "Regular" ADTs *)
    | ( Field (ProjAdt (def_id, opt_variant_id), _),
        TAdt { id = TAdtId def_id'; generics } ) ->
        [%sanity_check] span (def_id = def_id');
        compute_expanded_bottom_adt_value span ctx def_id opt_variant_id
          generics
    (* Tuples *)
    | ( Field (ProjTuple arity, _),
        TAdt
          {
            id = TTuple;
            generics =
              { regions = []; types; const_generics = []; trait_refs = [] };
          } ) ->
        [%sanity_check] span (arity = List.length types);
        (* Generate the field values *)
        compute_expanded_bottom_tuple_value span types
    | _ ->
        [%craise] span
          ("Unreachable: " ^ show_projection_elem pe ^ ", " ^ show_ety p.ty)
  in
  (* Update the context by inserting the expanded value at the proper place *)
  match try_write_place span access p nv ctx with
  | Ok ctx -> ctx
  | Error _ -> [%craise] span "Unreachable"

let rec update_ctx_along_read_place (config : config) (span : Meta.span)
    (access : access_kind) (p : place) : cm_fun =
 fun ctx ->
  (* Attempt to read the place: if it fails, update the environment and retry *)
  match try_read_place span access p ctx with
  | Ok _ -> (ctx, fun e -> e)
  | Error err ->
      let ctx, cc =
        match err with
        | FailSharedLoan lid | FailMutLoan lid -> end_loan config span lid ctx
        | FailReservedMutBorrow (bid, sid) ->
            promote_reserved_mut_borrow config span bid sid ctx
        | FailSymbolic (p, sv) ->
            (* Expand the symbolic value *)
            expand_symbolic_value_no_branching span sv
              (Some (Synth.mk_mplace span p ctx))
              ctx
        | FailBottom (_, _) ->
            (* We can't expand {!Bottom} values while reading them *)
            [%craise] span "Found bottom while reading a place"
        | FailBorrow _ -> [%craise] span "Could not read a borrow"
      in
      comp cc (update_ctx_along_read_place config span access p ctx)

let rec update_ctx_along_write_place (config : config) (span : Meta.span)
    (access : access_kind) (p : place) : cm_fun =
 fun ctx ->
  (* Attempt to *read* (yes, *read*: we check the access to the place, and
     write to it later) the place: if it fails, update the environment and retry *)
  match try_read_place span access p ctx with
  | Ok _ -> (ctx, fun e -> e)
  | Error err ->
      (* Update the context *)
      let ctx, cc =
        match err with
        | FailSharedLoan lid | FailMutLoan lid -> end_loan config span lid ctx
        | FailReservedMutBorrow (bid, sid) ->
            promote_reserved_mut_borrow config span bid sid ctx
        | FailSymbolic (_pe, sp) ->
            (* Expand the symbolic value *)
            expand_symbolic_value_no_branching span sp
              (Some (Synth.mk_mplace span p ctx))
              ctx
        | FailBottom (p, pe) ->
            (* Expand the {!Bottom} value *)
            let ctx =
              expand_bottom_value_from_projection span access p pe ctx
            in
            (ctx, fun e -> e)
        | FailBorrow _ -> [%craise] span "Could not write to a borrow"
      in
      (* Retry *)
      comp cc (update_ctx_along_write_place config span access p ctx)

(** Small utility used to break control-flow *)
exception UpdateCtx of (eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr))

let rec end_loans_at_place (config : config) (span : Meta.span)
    (access : access_kind) (p : place) : cm_fun =
 fun ctx ->
  (* Iterator to explore a value and update the context whenever we find
   * loans.
   * We use exceptions to make it handy: whenever we update the
   * context, we raise an exception wrapping the updated context.
   *)
  let obj =
    object
      inherit [_] iter_tvalue as super

      method! visit_borrow_content env bc =
        match bc with
        | VSharedBorrow _ | VMutBorrow (_, _) ->
            (* Nothing special to do *) super#visit_borrow_content env bc
        | VReservedMutBorrow (bid, sid) ->
            (* We need to activate reserved borrows *)
            let res = promote_reserved_mut_borrow config span bid sid ctx in
            raise (UpdateCtx res)

      method! visit_loan_content env lc =
        match lc with
        | VSharedLoan (lid, v) -> (
            (* End the loans if we need a modification access, otherwise dive into
               the shared value *)
            match access with
            | Read -> super#visit_VSharedLoan env lid v
            | Write | Move ->
                let res = end_loan config span lid ctx in
                raise (UpdateCtx res))
        | VMutLoan lid ->
            (* We always need to end mutable borrows *)
            let res = end_loan config span lid ctx in
            raise (UpdateCtx res)
    end
  in

  (* First, retrieve the value *)
  let _, v = read_place span access p ctx in
  (* Inspect the value and update the context while doing so.
     If the context gets updated: perform a recursive call (many things
     may have been updated in the context: we need to re-read the value
     at place [p] - and this value may actually not be accessible
     anymore...)
  *)
  try
    obj#visit_tvalue () v;
    (* No context update required: apply the continuation *)
    (ctx, fun e -> e)
  with UpdateCtx (ctx, cc) ->
    (* We need to update the context: compose the caugth continuation with
     * a recursive call to reinspect the value *)
    comp cc (end_loans_at_place config span access p ctx)

let drop_outer_loans_at_lplace (config : config) (span : Meta.span) (p : place)
    : cm_fun =
 fun ctx ->
  (* Move the current value in the place outside of this place and into
   * a temporary dummy variable *)
  let access = Write in
  let _, v = read_place span access p ctx in
  let ctx = write_place span access p (mk_bottom span v.ty) ctx in
  let dummy_id = ctx.fresh_dummy_var_id () in
  let ctx = ctx_push_dummy_var ctx dummy_id v in
  (* Auxiliary function: while there are loans to end in the
     temporary value, end them *)
  let rec drop : cm_fun =
   fun ctx ->
    (* Read the value *)
    let v = ctx_lookup_dummy_var span ctx dummy_id in
    (* Check if there are loans (and only loans) to end *)
    let with_borrows = false in
    match get_first_outer_loan_or_borrow_in_value with_borrows v with
    | None ->
        (* We are done *)
        (ctx, fun e -> e)
    | Some c ->
        (* End the loans and retry *)
        let ctx, cc =
          match c with
          | LoanContent (VSharedLoan (lid, _)) | LoanContent (VMutLoan lid) ->
              end_loan config span lid ctx
          | BorrowContent _ ->
              (* Can't get there: we are only looking up the loans *)
              [%craise] span "Unreachable"
        in
        (* Retry *)
        comp cc (drop ctx)
  in
  (* Apply the drop function *)
  let ctx, cc = drop ctx in
  (* Pop the temporary value and reinsert it *)
  (* Pop *)
  let ctx, v = ctx_remove_dummy_var span ctx dummy_id in
  (* Sanity check *)
  [%sanity_check] span (not (outer_loans_in_value v));
  (* Reinsert *)
  let ctx = write_place span access p v ctx in
  (* Return *)
  (ctx, cc)

let prepare_lplace (config : config) (span : Meta.span) (p : place)
    (ctx : eval_ctx) :
    tvalue * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr) =
  [%ltrace
    "- p: " ^ place_to_string ctx p ^ "\n- Initial context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];
  (* Access the place *)
  let access = Write in
  let ctx, cc = update_ctx_along_write_place config span access p ctx in
  (* End the loans at the place we are about to overwrite *)
  let ctx, cc = comp cc (drop_outer_loans_at_lplace config span p ctx) in
  (* Read the value and check it *)
  let _, v = read_place span access p ctx in
  (* Sanity checks *)
  [%sanity_check] span (not (outer_loans_in_value v));
  (* Return *)
  (v, ctx, cc)
