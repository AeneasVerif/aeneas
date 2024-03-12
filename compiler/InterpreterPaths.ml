open Types
open Values
open Expressions
open Contexts
open Cps
open ValuesUtils
open InterpreterUtils
open InterpreterBorrowsCore
open InterpreterBorrows
open InterpreterExpansion
open Errors
module Synth = SynthesizeSymbolic

(** The local logger *)
let log = Logging.paths_log

(** Paths *)

(** When we fail reading from or writing to a path, it might be because we
    need to update the environment by ending borrows, expanding symbolic
    values, etc. The following type is used to convey this information.
    
    TODO: compare with borrow_lres?
*)
type path_fail_kind =
  | FailSharedLoan of BorrowId.Set.t
      (** Failure because we couldn't go inside a shared loan *)
  | FailMutLoan of BorrowId.id
      (** Failure because we couldn't go inside a mutable loan *)
  | FailReservedMutBorrow of BorrowId.id
      (** Failure because we couldn't go inside a reserved mutable borrow
          (which should get activated) *)
  | FailSymbolic of int * symbolic_value
      (** Failure because we need to enter a symbolic value (and thus need to
          expand it).
          We return the number of elements which remained in the path when we
          reached the error - this allows to retrieve the path prefix, which
          is useful for the synthesis. *)
  | FailBottom of int * projection_elem * ety
      (** Failure because we need to enter an any value - we can expand Bottom
          values if they are left values. We return the number of elements which
          remained in the path when we reached the error - this allows to
          properly update the Bottom value, if needs be.
       *)
  | FailBorrow of borrow_content
      (** We got stuck because we couldn't enter a borrow *)
[@@deriving show]

(** Result of evaluating a path (reading from a path/writing to a path)
    
    Note that when we fail, we return information used to update the
    environment, as well as the 
*)
type 'a path_access_result = ('a, path_fail_kind) result
(** The result of reading from/writing to a place *)

type updated_read_value = { read : typed_value; updated : typed_value }

type projection_access = {
  enter_shared_loans : bool;
  enter_mut_borrows : bool;
  lookup_shared_borrows : bool;
}

(** Generic function to access (read/write) the value at the end of a projection.

    We return the (eventually) updated value, the value we read at the end of
    the place and the (eventually) updated environment.
    
    TODO: use exceptions?
 *)
let rec access_projection (meta : Meta.meta) (access : projection_access) (ctx : eval_ctx)
    (* Function to (eventually) update the value we find *)
      (update : typed_value -> typed_value) (p : projection) (v : typed_value) :
    (eval_ctx * updated_read_value) path_access_result =
  (* For looking up/updating shared loans *)
  let ek : exploration_kind =
    { enter_shared_loans = true; enter_mut_borrows = true; enter_abs = true }
  in
  match p with
  | [] ->
      let nv = update v in
      (* Type checking *)
      if nv.ty <> v.ty then (
        log#lerror
          (lazy
            ("Not the same type:\n- nv.ty: " ^ show_ety nv.ty ^ "\n- v.ty: "
           ^ show_ety v.ty));
        craise
          meta
             "Assertion failed: new value doesn't have the same type as its \
              destination");
      Ok (ctx, { read = v; updated = nv })
  | pe :: p' -> (
      (* Match on the projection element and the value *)
      match (pe, v.value, v.ty) with
      | ( Field ((ProjAdt (_, _) as proj_kind), field_id),
          VAdt adt,
          TAdt (type_id, _) ) -> (
          (* Check consistency *)
          (match (proj_kind, type_id) with
          | ProjAdt (def_id, opt_variant_id), TAdtId def_id' ->
              assert (def_id = def_id');
              assert (opt_variant_id = adt.variant_id)
          | _ -> craise meta "Unreachable");
          (* Actually project *)
          let fv = FieldId.nth adt.field_values field_id in
          match access_projection meta access ctx update p' fv with
          | Error err -> Error err
          | Ok (ctx, res) ->
              (* Update the field value *)
              let nvalues =
                FieldId.update_nth adt.field_values field_id res.updated
              in
              let nadt = VAdt { adt with field_values = nvalues } in
              let updated = { v with value = nadt } in
              Ok (ctx, { res with updated }))
      (* Tuples *)
      | Field (ProjTuple arity, field_id), VAdt adt, TAdt (TTuple, _) -> (
          assert (arity = List.length adt.field_values);
          let fv = FieldId.nth adt.field_values field_id in
          (* Project *)
          match access_projection meta access ctx update p' fv with
          | Error err -> Error err
          | Ok (ctx, res) ->
              (* Update the field value *)
              let nvalues =
                FieldId.update_nth adt.field_values field_id res.updated
              in
              let ntuple = VAdt { adt with field_values = nvalues } in
              let updated = { v with value = ntuple } in
              Ok (ctx, { res with updated })
          (* If we reach Bottom, it may mean we need to expand an uninitialized
           * enumeration value *))
      | Field ((ProjAdt (_, _) | ProjTuple _), _), VBottom, _ ->
          Error (FailBottom (1 + List.length p', pe, v.ty))
      (* Symbolic value: needs to be expanded *)
      | _, VSymbolic sp, _ ->
          (* Expand the symbolic value *)
          Error (FailSymbolic (1 + List.length p', sp))
      (* Box dereferencement *)
      | ( DerefBox,
          VAdt { variant_id = None; field_values = [ bv ] },
          TAdt (TAssumed TBox, _) ) -> (
          (* We allow moving outside of boxes. In practice, this kind of
           * manipulations should happen only inside unsafe code, so
           * it shouldn't happen due to user code, and we leverage it
           * when implementing box dereferencement for the concrete
           * interpreter *)
          match access_projection meta access ctx update p' bv with
          | Error err -> Error err
          | Ok (ctx, res) ->
              let nv =
                {
                  v with
                  value =
                    VAdt { variant_id = None; field_values = [ res.updated ] };
                }
              in
              Ok (ctx, { res with updated = nv }))
      (* Borrows *)
      | Deref, VBorrow bc, _ -> (
          match bc with
          | VSharedBorrow bid ->
              (* Lookup the loan content, and explore from there *)
              if access.lookup_shared_borrows then
                match lookup_loan meta ek bid ctx with
                | _, Concrete (VMutLoan _) ->
                    craise meta "Expected a shared loan"
                | _, Concrete (VSharedLoan (bids, sv)) -> (
                    (* Explore the shared value *)
                    match access_projection meta access ctx update p' sv with
                    | Error err -> Error err
                    | Ok (ctx, res) ->
                        (* Update the shared loan with the new value returned
                           by {!access_projection} *)
                        let ctx =
                          update_loan meta ek bid
                            (VSharedLoan (bids, res.updated))
                            ctx
                        in
                        (* Return - note that we don't need to update the borrow itself *)
                        Ok (ctx, { res with updated = v }))
                | ( _,
                    Abstract
                      ( AMutLoan (_, _)
                      | AEndedMutLoan
                          { given_back = _; child = _; given_back_meta = _ }
                      | AEndedSharedLoan (_, _)
                      | AIgnoredMutLoan (_, _)
                      | AEndedIgnoredMutLoan
                          { given_back = _; child = _; given_back_meta = _ }
                      | AIgnoredSharedLoan _ ) ) ->
                    craise meta "Expected a shared (abstraction) loan"
                | _, Abstract (ASharedLoan (bids, sv, _av)) -> (
                    (* Explore the shared value *)
                    match access_projection meta access ctx update p' sv with
                    | Error err -> Error err
                    | Ok (ctx, res) ->
                        (* Relookup the child avalue *)
                        let av =
                          match lookup_loan meta ek bid ctx with
                          | _, Abstract (ASharedLoan (_, _, av)) -> av
                          | _ -> craise meta "Unexpected"
                        in
                        (* Update the shared loan with the new value returned
                             by {!access_projection} *)
                        let ctx =
                          update_aloan meta ek bid
                            (ASharedLoan (bids, res.updated, av))
                            ctx
                        in
                        (* Return - note that we don't need to update the borrow itself *)
                        Ok (ctx, { res with updated = v }))
              else Error (FailBorrow bc)
          | VReservedMutBorrow bid -> Error (FailReservedMutBorrow bid)
          | VMutBorrow (bid, bv) ->
              if access.enter_mut_borrows then
                match access_projection meta access ctx update p' bv with
                | Error err -> Error err
                | Ok (ctx, res) ->
                    let nv =
                      { v with value = VBorrow (VMutBorrow (bid, res.updated)) }
                    in
                    Ok (ctx, { res with updated = nv })
              else Error (FailBorrow bc))
      | _, VLoan lc, _ -> (
          match lc with
          | VMutLoan bid -> Error (FailMutLoan bid)
          | VSharedLoan (bids, sv) ->
              (* If we can enter shared loan, we ignore the loan. Pay attention
                 to the fact that we need to reexplore the *whole* place (i.e,
                 we mustn't ignore the current projection element *)
              if access.enter_shared_loans then
                match access_projection meta access ctx update (pe :: p') sv with
                | Error err -> Error err
                | Ok (ctx, res) ->
                    let nv =
                      { v with value = VLoan (VSharedLoan (bids, res.updated)) }
                    in
                    Ok (ctx, { res with updated = nv })
              else Error (FailSharedLoan bids))
      | (_, (VLiteral _ | VAdt _ | VBottom | VBorrow _), _) as r ->
          let pe, v, ty = r in
          let pe = "- pe: " ^ show_projection_elem pe in
          let v = "- v:\n" ^ show_value v in
          let ty = "- ty:\n" ^ show_ety ty in
          log#serror ("Inconsistent projection:\n" ^ pe ^ "\n" ^ v ^ "\n" ^ ty);
          craise meta "Inconsistent projection")

(** Generic function to access (read/write) the value at a given place.

    We return the value we read at the place and the (eventually) updated
    environment, if we managed to access the place, or the precise reason
    why we failed.
 *)
let access_place (meta : Meta.meta) (access : projection_access)
    (* Function to (eventually) update the value we find *)
      (update : typed_value -> typed_value) (p : place) (ctx : eval_ctx) :
    (eval_ctx * typed_value) path_access_result =
  (* Lookup the variable's value *)
  let value = ctx_lookup_var_value ctx p.var_id in
  (* Apply the projection *)
  match access_projection meta access ctx update p.projection value with
  | Error err -> Error err
  | Ok (ctx, res) ->
      (* Update the value *)
      let ctx = ctx_update_var_value ctx p.var_id res.updated in
      (* Return *)
      Ok (ctx, res.read)

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

(** Attempt to read the value at a given place.

    Note that we only access the value at the place, and do not check that
    the value is "well-formed" (for instance that it doesn't contain bottoms).
 *)
let try_read_place (meta : Meta.meta) (access : access_kind) (p : place) (ctx : eval_ctx) :
    typed_value path_access_result =
  let access = access_kind_to_projection_access access in
  (* The update function is the identity *)
  let update v = v in
  match access_place meta access update p ctx with
  | Error err -> Error err
  | Ok (ctx1, read_value) ->
      (* Note that we ignore the new environment: it should be the same as the
         original one.
      *)
      if !Config.sanity_checks then
        if ctx1 <> ctx then (
          let msg =
            "Unexpected environment update:\nNew environment:\n"
            ^ show_env ctx1.env ^ "\n\nOld environment:\n" ^ show_env ctx.env
          in
          log#serror msg;
          craise meta "Unexpected environment update");
      Ok read_value

let read_place (meta : Meta.meta) (access : access_kind) (p : place) (ctx : eval_ctx) : typed_value
    =
  match try_read_place meta access p ctx with
  | Error e -> craise meta ("Unreachable: " ^ show_path_fail_kind e)
  | Ok v -> v

(** Attempt to update the value at a given place *)
let try_write_place (meta : Meta.meta) (access : access_kind) (p : place) (nv : typed_value)
    (ctx : eval_ctx) : eval_ctx path_access_result =
  let access = access_kind_to_projection_access access in
  (* The update function substitutes the value with the new value *)
  let update _ = nv in
  match access_place meta access update p ctx with
  | Error err -> Error err
  | Ok (ctx, _) ->
      (* We ignore the read value *)
      Ok ctx

let write_place (meta : Meta.meta) (access : access_kind) (p : place) (nv : typed_value)
    (ctx : eval_ctx) : eval_ctx =
  match try_write_place meta access p nv ctx with
  | Error e -> craise meta ("Unreachable: " ^ show_path_fail_kind e)
  | Ok ctx -> ctx

let compute_expanded_bottom_adt_value (ctx : eval_ctx) (def_id : TypeDeclId.id)
    (opt_variant_id : VariantId.id option) (generics : generic_args) :
    typed_value =
  assert (TypesUtils.generic_args_only_erased_regions generics);
  (* Lookup the definition and check if it is an enumeration - it
     should be an enumeration if and only if the projection element
     is a field projection with *some* variant id. Retrieve the list
     of fields at the same time. *)
  let def = ctx_lookup_type_decl ctx def_id in
  assert (List.length generics.regions = List.length def.generics.regions);
  (* Compute the field types *)
  let field_types =
    AssociatedTypes.type_decl_get_inst_norm_field_etypes ctx def opt_variant_id
      generics
  in
  (* Initialize the expanded value *)
  let fields = List.map mk_bottom field_types in
  let av = VAdt { variant_id = opt_variant_id; field_values = fields } in
  let ty = TAdt (TAdtId def_id, generics) in
  { value = av; ty }

let compute_expanded_bottom_tuple_value (field_types : ety list) : typed_value =
  (* Generate the field values *)
  let fields = List.map mk_bottom field_types in
  let v = VAdt { variant_id = None; field_values = fields } in
  let generics = TypesUtils.mk_generic_args [] field_types [] [] in
  let ty = TAdt (TTuple, generics) in
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
    to, say, [Cons Bottom Bottom] (note that field projection contains information
    about which variant we should project to, which is why we *can* set the
    variant index when writing one of its fields).
*)
let expand_bottom_value_from_projection (meta : Meta.meta) (access : access_kind) (p : place)
    (remaining_pes : int) (pe : projection_elem) (ty : ety) (ctx : eval_ctx) :
    eval_ctx =
  (* Debugging *)
  log#ldebug
    (lazy
      ("expand_bottom_value_from_projection:\n" ^ "pe: "
     ^ show_projection_elem pe ^ "\n" ^ "ty: " ^ show_ety ty));
  (* Prepare the update: we need to take the proper prefix of the place
     during whose evaluation we got stuck *)
  let projection' =
    fst
      (Collections.List.split_at p.projection
         (List.length p.projection - remaining_pes))
  in
  let p' = { p with projection = projection' } in
  (* Compute the expanded value.
     The type of the {!Bottom} value should be a tuple or an AD
     Note that the projection element we got stuck at should be a
     field projection, and gives the variant id if the {!Bottom} value
     is an enumeration value.
     Also, the expanded value should be the proper ADT variant or a tuple
     with the proper arity, with all the fields initialized to {!Bottom}
  *)
  let nv =
    match (pe, ty) with
    (* "Regular" ADTs *)
    | ( Field (ProjAdt (def_id, opt_variant_id), _),
        TAdt (TAdtId def_id', generics) ) ->
        assert (def_id = def_id');
        compute_expanded_bottom_adt_value ctx def_id opt_variant_id generics
    (* Tuples *)
    | ( Field (ProjTuple arity, _),
        TAdt
          (TTuple, { regions = []; types; const_generics = []; trait_refs = [] })
      ) ->
        assert (arity = List.length types);
        (* Generate the field values *)
        compute_expanded_bottom_tuple_value types
    | _ ->
        craise
          meta
             ("Unreachable: " ^ show_projection_elem pe ^ ", " ^ show_ety ty)
  in
  (* Update the context by inserting the expanded value at the proper place *)
  match try_write_place meta access p' nv ctx with
  | Ok ctx -> ctx
  | Error _ -> craise meta "Unreachable"

let rec update_ctx_along_read_place (meta : Meta.meta) (config : config) (access : access_kind)
    (p : place) : cm_fun =
 fun cf ctx ->
  (* Attempt to read the place: if it fails, update the environment and retry *)
  match try_read_place meta access p ctx with
  | Ok _ -> cf ctx
  | Error err ->
      let cc =
        match err with
        | FailSharedLoan bids -> end_borrows config bids
        | FailMutLoan bid -> end_borrow config bid
        | FailReservedMutBorrow bid -> promote_reserved_mut_borrow config bid
        | FailSymbolic (i, sp) ->
            (* Expand the symbolic value *)
            let proj, _ =
              Collections.List.split_at p.projection
                (List.length p.projection - i)
            in
            let prefix = { p with projection = proj } in
            expand_symbolic_value_no_branching config sp
              (Some (Synth.mk_mplace prefix ctx))
        | FailBottom (_, _, _) ->
            (* We can't expand {!Bottom} values while reading them *)
            craise meta "Found [Bottom] while reading a place"
        | FailBorrow _ -> craise meta "Could not read a borrow"
      in
      comp cc (update_ctx_along_read_place meta config access p) cf ctx

let rec update_ctx_along_write_place (meta : Meta.meta) (config : config) (access : access_kind)
    (p : place) : cm_fun =
 fun cf ctx ->
  (* Attempt to *read* (yes, *read*: we check the access to the place, and
     write to it later) the place: if it fails, update the environment and retry *)
  match try_read_place meta access p ctx with
  | Ok _ -> cf ctx
  | Error err ->
      (* Update the context *)
      let cc =
        match err with
        | FailSharedLoan bids -> end_borrows config bids
        | FailMutLoan bid -> end_borrow config bid
        | FailReservedMutBorrow bid -> promote_reserved_mut_borrow config bid
        | FailSymbolic (_pe, sp) ->
            (* Expand the symbolic value *)
            expand_symbolic_value_no_branching config sp
              (Some (Synth.mk_mplace p ctx))
        | FailBottom (remaining_pes, pe, ty) ->
            (* Expand the {!Bottom} value *)
            fun cf ctx ->
             let ctx =
               expand_bottom_value_from_projection meta access p remaining_pes pe ty
                 ctx
             in
             cf ctx
        | FailBorrow _ -> craise meta "Could not write to a borrow"
      in
      (* Retry *)
      comp cc (update_ctx_along_write_place meta config access p) cf ctx

(** Small utility used to break control-flow *)
exception UpdateCtx of cm_fun

let rec end_loans_at_place (meta : Meta.meta) (config : config) (access : access_kind) (p : place)
    : cm_fun =
 fun cf ctx ->
  (* Iterator to explore a value and update the context whenever we find
   * loans.
   * We use exceptions to make it handy: whenever we update the
   * context, we raise an exception wrapping the updated context.
   * *)
  let obj =
    object
      inherit [_] iter_typed_value as super

      method! visit_borrow_content env bc =
        match bc with
        | VSharedBorrow _ | VMutBorrow (_, _) ->
            (* Nothing special to do *) super#visit_borrow_content env bc
        | VReservedMutBorrow bid ->
            (* We need to activate reserved borrows *)
            let cc = promote_reserved_mut_borrow config bid in
            raise (UpdateCtx cc)

      method! visit_loan_content env lc =
        match lc with
        | VSharedLoan (bids, v) -> (
            (* End the loans if we need a modification access, otherwise dive into
               the shared value *)
            match access with
            | Read -> super#visit_VSharedLoan env bids v
            | Write | Move ->
                let cc = end_borrows config bids in
                raise (UpdateCtx cc))
        | VMutLoan bid ->
            (* We always need to end mutable borrows *)
            let cc = end_borrow config bid in
            raise (UpdateCtx cc)
    end
  in

  (* First, retrieve the value *)
  let v = read_place meta access p ctx in
  (* Inspect the value and update the context while doing so.
     If the context gets updated: perform a recursive call (many things
     may have been updated in the context: we need to re-read the value
     at place [p] - and this value may actually not be accessible
     anymore...)
  *)
  try
    obj#visit_typed_value () v;
    (* No context update required: apply the continuation *)
    cf ctx
  with UpdateCtx cc ->
    (* We need to update the context: compose the caugth continuation with
     * a recursive call to reinspect the value *)
    comp cc (end_loans_at_place meta config access p) cf ctx

let drop_outer_loans_at_lplace (meta : Meta.meta) (config : config) (p : place) : cm_fun =
 fun cf ctx ->
  (* Move the current value in the place outside of this place and into
   * a dummy variable *)
  let access = Write in
  let v = read_place meta access p ctx in
  let ctx = write_place meta access p (mk_bottom v.ty) ctx in
  let dummy_id = fresh_dummy_var_id () in
  let ctx = ctx_push_dummy_var ctx dummy_id v in
  (* Auxiliary function *)
  let rec drop : cm_fun =
   fun cf ctx ->
    (* Read the value *)
    let v = ctx_lookup_dummy_var ctx dummy_id in
    (* Check if there are loans or borrows to end *)
    let with_borrows = false in
    match get_first_outer_loan_or_borrow_in_value with_borrows v with
    | None ->
        (* We are done: simply call the continuation *)
        cf ctx
    | Some c ->
        (* There are: end them then retry *)
        let cc =
          match c with
          | LoanContent (VSharedLoan (bids, _)) -> end_borrows config bids
          | LoanContent (VMutLoan bid) -> end_borrow config bid
          | BorrowContent _ -> craise meta "Unreachable"
        in
        (* Retry *)
        comp cc drop cf ctx
  in
  (* Apply the drop function *)
  let cc = drop in
  (* Pop the temporary value and reinsert it *)
  let cc =
    comp cc (fun cf ctx ->
        (* Pop *)
        let ctx, v = ctx_remove_dummy_var ctx dummy_id in
        (* Reinsert *)
        let ctx = write_place meta access p v ctx in
        (* Sanity check *)
        assert (not (outer_loans_in_value v));
        (* Continue *)
        cf ctx)
  in
  (* Continue *)
  cc cf ctx

let prepare_lplace (meta : Meta.meta) (config : config) (p : place) (cf : typed_value -> m_fun) :
    m_fun =
 fun ctx ->
  log#ldebug
    (lazy
      ("prepare_lplace:" ^ "\n- p: " ^ place_to_string ctx p
     ^ "\n- Initial context:\n" ^ eval_ctx_to_string ctx));
  (* Access the place *)
  let access = Write in
  let cc = update_ctx_along_write_place meta config access p in
  (* End the borrows and loans, starting with the borrows *)
  let cc = comp cc (drop_outer_loans_at_lplace meta config p) in
  (* Read the value and check it *)
  let read_check cf : m_fun =
   fun ctx ->
    let v = read_place meta access p ctx in
    (* Sanity checks *)
    assert (not (outer_loans_in_value v));
    (* Continue *)
    cf v ctx
  in
  (* Compose and apply the continuations *)
  comp cc read_check cf ctx
