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

(** A path starts either at a local or at a shared loan (the latter case is
    needed to manipulate shared loans inside abstractions). *)
type path_root = LocalRoot of LocalId.id | SharedLoanRoot of loan_id

type path_elem =
  | PathField of VariantId.id option * FieldId.id
  | PathDerefBox
  | PathDerefMut

type path = { root : path_root; projection : path_elem list }

let path_exploration : exploration_kind =
  { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }

let shared_loan_value (span : Meta.span) (lid : loan_id) (ctx : eval_ctx) :
    tvalue =
  match ctx_lookup_loan span path_exploration lid ctx with
  | _, Concrete (VSharedLoan (_, v)) -> v
  | _, Abstract (ASharedLoan (pm, _, v, _)) ->
      [%sanity_check] span (pm = PNone);
      v
  | _ -> [%craise] span "Expected a shared loan at path root"

let read_path_root (span : Meta.span) (root : path_root) (ctx : eval_ctx) :
    tvalue =
  match root with
  | LocalRoot var_id -> ctx_lookup_var_value span ctx var_id
  | SharedLoanRoot lid -> shared_loan_value span lid ctx

let project_path_elem (span : Meta.span) (pe : path_elem) (v : tvalue) : tvalue
    =
  match (pe, v.value, v.ty) with
  | PathField (variant_id, field_id), VAdt adt, TAdt _ ->
      [%sanity_check] span (variant_id = adt.variant_id);
      [%unwrap_with_span] span
        (FieldId.nth_opt adt.fields field_id)
        "Field index out of bounds"
  | ( PathDerefBox,
      VAdt { variant_id = None; fields = [ v ] },
      TAdt { builtin = Some TBox; _ } ) -> v
  | PathDerefMut, VBorrow (VMutBorrow (_, v)), _ -> v
  | _ -> [%craise] span "Invalid path projection"

(** Update the projected value and reconstruct its parent. *)
let update_path_elem (span : Meta.span) (pe : path_elem) (v : tvalue)
    (update : tvalue -> tvalue) : tvalue =
  let value =
    match (pe, v.value, v.ty) with
    | PathField (variant_id, field_id), VAdt adt, TAdt _ ->
        [%sanity_check] span (variant_id = adt.variant_id);
        let fv =
          [%unwrap_with_span] span
            (FieldId.nth_opt adt.fields field_id)
            "Field index out of bounds"
        in
        let updated = update fv in
        VAdt
          { adt with fields = FieldId.update_nth adt.fields field_id updated }
    | ( PathDerefBox,
        VAdt { variant_id = None; fields = [ bv ] },
        TAdt { builtin = Some TBox; _ } ) ->
        VAdt { variant_id = None; fields = [ update bv ] }
    | PathDerefMut, VBorrow (VMutBorrow (bid, bv)), _ ->
        VBorrow (VMutBorrow (bid, update bv))
    | _ -> [%craise] span "Invalid path projection"
  in
  { v with value }

let read_path (span : Meta.span) (path : path) (ctx : eval_ctx) : tvalue =
  List.fold_left
    (fun v pe -> project_path_elem span pe v)
    (read_path_root span path.root ctx)
    path.projection

let write_path (span : Meta.span) (path : path) (nv : tvalue) (ctx : eval_ctx) :
    eval_ctx =
  let rec write (projection : path_elem list) (v : tvalue) : tvalue =
    match projection with
    | [] ->
        [%cassert] span
          (erase_regions nv.ty = erase_regions v.ty)
          "New value doesn't have the same type as its destination";
        nv
    | pe :: projection -> update_path_elem span pe v (write projection)
  in
  let updated = write path.projection (read_path_root span path.root ctx) in
  match path.root with
  | LocalRoot var_id -> ctx_update_var_value span ctx var_id updated
  | SharedLoanRoot lid -> (
      match ctx_lookup_loan span path_exploration lid ctx with
      | _, Concrete (VSharedLoan _) ->
          update_loan span path_exploration lid (VSharedLoan (lid, updated)) ctx
      | _, Abstract (ASharedLoan (pm, _, _, av)) ->
          [%sanity_check] span (pm = PNone);
          update_aloan span path_exploration lid
            (ASharedLoan (pm, lid, updated, av))
            ctx
      | _ -> [%craise] span "Expected a shared loan at path root")

let extend_path (path : path) (pe : path_elem) : path =
  { path with projection = path.projection @ [ pe ] }

(** Resolve a projection to its value and path. The optional loan identifier
    indicates that the value is immediately beneath a shared loan. *)
let rec project_value (span : Meta.span) (access : projection_access)
    (current_place : place) (ctx : eval_ctx) (pe : projection_elem) (v : tvalue)
    (path : path) : (loan_id option * tvalue * path) path_access_result =
  match (pe, v.value, v.ty) with
  | Field (opt_variant_id, field_id), VAdt adt, TAdt { builtin = None; _ } ->
      (* Check consistency *)
      [%sanity_check] span (opt_variant_id = adt.variant_id);
      let fv =
        [%unwrap_with_span] span
          (FieldId.nth_opt adt.fields field_id)
          "Field index out of bounds"
      in
      Ok (None, fv, extend_path path (PathField (opt_variant_id, field_id)))
  (* Tuples *)
  | Field (None, field_id), VAdt adt, TAdt { builtin = Some TTuple; _ } ->
      let fv =
        [%unwrap_with_span] span
          (FieldId.nth_opt adt.fields field_id)
          "Field index out of bounds"
      in
      Ok (None, fv, extend_path path (PathField (None, field_id)))
  | Field _, VBottom, _ ->
      (* If we reach Bottom, it may mean we need to expand an uninitialized
       * enumeration value *)
      Error (FailBottom (current_place, pe))
  (* Raw pointer dereference: not supported yet.

     It is important that this appears before the symbolic value case, otherwise
     we would be tempted to expand a raw pointer symbolic value (which we can't,
     and would lead to an obscure error from the user point of view). *)
  | Deref, _, TRawPtr _ ->
      [%craise] span "Aeneas does not yet support dereferencing raw pointers."
  (* Symbolic value: needs to be expanded *)
  | _, VSymbolic sp, _ ->
      (* Expand the symbolic value *)
      Error (FailSymbolic (current_place, sp))
  (* Box dereferencement *)
  | ( Deref,
      VAdt { variant_id = None; fields = [ fv ] },
      TAdt { builtin = Some TBox; _ } ) -> begin
      (* We allow moving outside of boxes. In practice, this kind of
       * manipulations should happen only inside unsafe code, so
       * it shouldn't happen due to user code, and we leverage it
       * when implementing box dereferencement for the concrete
       * interpreter *)
      Ok (None, fv, extend_path path PathDerefBox)
    end
  (* Borrows *)
  | Deref, VBorrow bc, _ ->
      (* Resolve shared dereferences to the loan, not to the borrow's ancestors. *)
      let res : _ path_access_result =
        match bc with
        | VSharedBorrow _ when not access.lookup_shared_borrows ->
            Error (FailBorrow bc)
        | VSharedBorrow (bid, _) ->
            let sv = shared_loan_value span bid ctx in
            Ok (Some bid, sv, { root = SharedLoanRoot bid; projection = [] })
        | VReservedMutBorrow (bid, sid) ->
            Error (FailReservedMutBorrow (bid, sid))
        | VMutBorrow _ when not access.enter_mut_borrows ->
            Error (FailBorrow bc)
        | VMutBorrow (_, bv) -> Ok (None, bv, extend_path path PathDerefMut)
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
          let path = { root = SharedLoanRoot bids; projection = [] } in
          project_value span access current_place ctx pe sv path
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

    We always read the value, and return its path without updating the context.
*)
let rec access_place (span : Meta.span) (access : projection_access)
    (ctx : eval_ctx) (p : place) :
    (loan_id option * tvalue * path) path_access_result =
  match p.kind with
  | PlaceLocal var_id ->
      (* Lookup the variable's value *)
      let v = ctx_lookup_var_value span ctx var_id in
      Ok (None, v, { root = LocalRoot var_id; projection = [] })
  | PlaceProjection (p', pe) -> begin
      match access_place span access ctx p' with
      | Error err -> Error err
      | Ok (_, v, path) -> project_value span access p' ctx pe v path
    end
  | PlaceGlobal _ -> [%craise] span "Unexpected access to a global"

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
  match access_place span access ctx p with
  | Error err -> Error err
  | Ok (lid, read_value, _) -> Ok (lid, read_value)

let eval_place (span : Meta.span) (access : access_kind) (p : place)
    (ctx : eval_ctx) : loan_id option * tvalue * path =
  let access = access_kind_to_projection_access access in
  match access_place span access ctx p with
  | Error e -> [%craise] span ("Unreachable: " ^ show_path_fail_kind e)
  | Ok res -> res

let read_place (span : Meta.span) (access : access_kind) (p : place)
    (ctx : eval_ctx) : loan_id option * tvalue =
  let lid, v, _ = eval_place span access p ctx in
  (lid, v)

(** Attempt to update the value at a given place, provided the place **does not
    refer to a global** (globals are handled elsewhere). *)
let try_write_place (span : Meta.span) (access : access_kind) (p : place)
    (nv : tvalue) (ctx : eval_ctx) : eval_ctx path_access_result =
  let access = access_kind_to_projection_access access in
  match access_place span access ctx p with
  | Error err -> Error err
  | Ok (_, _, path) -> Ok (write_path span path nv ctx)

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
  let ty = TAdt { id = def_id; generics; builtin = None } in
  { value = av; ty }

let compute_expanded_bottom_tuple_value (span : Meta.span)
    (field_types : ety list) : tvalue =
  (* Generate the field values *)
  let fields = List.map (mk_bottom span) field_types in
  let v = VAdt { variant_id = None; fields } in
  let ty = TypesUtils.mk_tuple_ty field_types in
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
    | Field (opt_variant_id, _), TAdt { id = def_id; generics; builtin = None }
      ->
        compute_expanded_bottom_adt_value span ctx def_id opt_variant_id
          generics
    (* Tuples *)
    | ( Field (None, _),
        TAdt
          {
            generics =
              { regions = []; types; const_generics = []; trait_refs = [] };
            builtin = Some TTuple;
            _;
          } ) ->
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
  let _, v, path = eval_place span access p ctx in
  let ctx = write_path span path (mk_bottom span v.ty) ctx in
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
