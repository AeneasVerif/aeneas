open Types
open TypesUtils
open Values
open ValuesUtils
open Expressions
open Contexts
open LlbcAst
open LlbcAstUtils
open Cps
open InterpUtils
open InterpProjectors
open InterpExpansion
open InterpPaths
open InterpExpressions
module Subst = Substitute
module S = SynthesizeSymbolic

(** The local logger *)
let log = L.statements_log

(** Drop a value at a given place - TODO: factorize this with [assign_to_place]
*)
let drop_value (config : config) (span : Meta.span) (p : place) : cm_fun =
 fun ctx ->
  log#ltrace
    (lazy
      ("drop_value: place: " ^ place_to_string ctx p ^ "\n- Initial context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx));
  (* Note that we use [Write], not [Move]: we allow to drop values *below* borrows *)
  let access = Write in
  (* First make sure we can access the place, by ending loans or expanding
   * symbolic values along the path, for instance *)
  let ctx, cc = update_ctx_along_read_place config span access p ctx in
  (* Prepare the place (by ending the outer loans *at* the place). *)
  let v, ctx, cc = comp2 cc (prepare_lplace config span p ctx) in
  (* Replace the value with {!Bottom} *)
  let ctx =
    (* Move the value at destination (that we will overwrite) to a dummy variable
     * to preserve the borrows it may contain *)
    let _, mv = InterpPaths.read_place span access p ctx in
    let dummy_id = ctx.fresh_dummy_var_id () in
    let ctx = ctx_push_dummy_var ctx dummy_id mv in
    (* Update the destination to ⊥ *)
    let nv = { v with value = VBottom } in
    let ctx = write_place span access p nv ctx in
    [%ltrace
      "place: " ^ place_to_string ctx p ^ "\n- Final context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];
    ctx
  in
  (* Compose and apply *)
  (ctx, cc)

(** Push a dummy variable to the environment *)
let push_dummy_var (vid : DummyVarId.id) (v : tvalue) (ctx : eval_ctx) :
    eval_ctx =
  ctx_push_dummy_var ctx vid v

(** Remove a dummy variable from the environment *)
let remove_dummy_var (span : Meta.span) (vid : DummyVarId.id) (ctx : eval_ctx) :
    tvalue * eval_ctx =
  let ctx, v = ctx_remove_dummy_var span ctx vid in
  (v, ctx)

(** Push a list of uninitialized variables to the environment *)
let push_uninitialized_vars (span : Meta.span) (vars : local list)
    (ctx : eval_ctx) : eval_ctx =
  ctx_push_uninitialized_vars span ctx vars

(** Push a variable to the environment *)
let push_var (span : Meta.span) (var : local) (v : tvalue) (ctx : eval_ctx) :
    eval_ctx =
  ctx_push_var span ctx var v

(** Push a list of variables to the environment *)
let push_vars (span : Meta.span) (vars : (local * tvalue) list) (ctx : eval_ctx)
    : eval_ctx =
  ctx_push_vars span ctx vars

(** Assign a value to a given place.

    Note that this function first pushes the value to assign in a dummy
    variable, then prepares the destination (by ending borrows, etc.) before
    popping the dummy variable and putting in its destination (after having
    checked that preparing the destination didn't introduce ⊥). *)
let assign_to_place (config : config) (span : Meta.span) (rv : tvalue)
    (p : place) : cm_fun =
 fun ctx ->
  [%ltrace
    "- rv: "
    ^ tvalue_to_string ~span:(Some span) ctx rv
    ^ "\n- p: " ^ place_to_string ctx p ^ "\n- p.ty: " ^ ty_to_string ctx p.ty
    ^ "\n- Initial context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];
  (* Push the rvalue to a dummy variable, for bookkeeping *)
  let rvalue_vid = ctx.fresh_dummy_var_id () in
  let ctx = push_dummy_var rvalue_vid rv ctx in
  (* Prepare the destination *)
  let _, ctx, cc = prepare_lplace config span p ctx in
  (* Retrieve the rvalue from the dummy variable *)
  let rv, ctx = remove_dummy_var span rvalue_vid ctx in
  (* Move the value at destination (that we will overwrite) to a dummy variable
     to preserve the borrows *)
  let _, mv = InterpPaths.read_place span Write p ctx in
  let dest_vid = ctx.fresh_dummy_var_id () in
  let ctx = ctx_push_dummy_var ctx dest_vid mv in
  (* Write to the destination *)
  (* Checks - maybe the bookkeeping updated the rvalue and introduced bottoms *)
  [%cassert] span
    (not (bottom_in_value ctx.ended_regions rv))
    "The value to move contains bottom";
  (* Update the destination *)
  let ctx = write_place span Write p rv ctx in
  (* Debug *)
  [%ltrace
    "- rv: "
    ^ tvalue_to_string ~span:(Some span) ctx rv
    ^ "\n- p: " ^ place_to_string ctx p ^ "\n- Final context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];
  (* Return *)
  (ctx, cc)

(** Evaluate an assertion, when the scrutinee is not symbolic *)
let eval_assertion_concrete (config : config) (span : Meta.span)
    (assertion : assertion) : st_cm_fun =
 fun ctx ->
  (* There won't be any symbolic expansions: fully evaluate the operand *)
  let v, ctx, eval_op = eval_operand config span assertion.cond ctx in
  let st =
    match v.value with
    | VLiteral (VBool b) ->
        (* Branch *)
        if b = assertion.expected then Unit else Panic
    | _ ->
        [%craise] span
          ("Expected a boolean, got: "
          ^ tvalue_to_string ~span:(Some span) ctx v)
  in
  (* Compose and apply *)
  ((ctx, st), eval_op)

(** Evaluates an assertion.

    In the case the boolean under scrutinee is symbolic, we synthesize a call to
    [assert ...] then continue in the success branch (and thus expand the
    boolean to [true]). *)
let eval_assertion (config : config) (span : Meta.span) (assertion : assertion)
    : st_cm_fun =
 fun ctx ->
  (* Evaluate the operand *)
  let v, ctx, cf_eval_op = eval_operand config span assertion.cond ctx in
  (* Evaluate the assertion *)
  [%sanity_check] span (v.ty = TScalar TBool);
  let st, cf_eval_assert =
    (* We make a choice here: we could completely decouple the concrete and
     * symbolic executions here but choose not to. In the case where we
     * know the concrete value of the boolean we test, we use this value
     * even if we are in symbolic mode. Note that this case should be
     * extremely rare... *)
    match v.value with
    | VLiteral (VBool _) ->
        (* Delegate to the concrete evaluation function *)
        eval_assertion_concrete config span assertion ctx
    | VSymbolic sv ->
        [%sanity_check] span (config.mode = SymbolicMode);
        [%sanity_check] span (sv.sv_ty = TScalar TBool);
        (* We continue the execution as if the test had succeeded, and thus
         * perform the symbolic expansion: sv ~~> true.
         * We will of course synthesize an assertion in the generated code
         * (see below). *)
        let ctx =
          apply_symbolic_expansion_non_borrow span sv ctx
            (SeLiteral (VBool assertion.expected))
        in
        (* Add the synthesized assertion *)
        ((ctx, Unit), S.synthesize_assertion ctx assertion.expected v)
    | _ ->
        [%craise] span
          ("Expected a boolean, got: "
          ^ tvalue_to_string ~span:(Some span) ctx v)
  in
  (* Compose and apply *)
  (st, cc_comp cf_eval_op cf_eval_assert)

(** Updates the discriminant of a value at a given place.

    There are two situations:
    - either the discriminant is already the proper one (in which case we don't
      do anything)
    - or it is not the proper one (because the variant is not the proper one, or
      the value is actually {!Bottom} - this happens when initializing ADT
      values), in which case we replace the value with a variant with all its
      fields set to {!Bottom}. For instance, something like:
      [Cons Bottom Bottom]. *)
let set_discriminant (config : config) (span : Meta.span) (p : place)
    (variant_id : VariantId.id) : st_cm_fun =
 fun ctx ->
  [%ltrace
    "- p: " ^ place_to_string ctx p ^ "\n- variant id: "
    ^ VariantId.to_string variant_id
    ^ "\n- initial context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];
  (* Access the value *)
  let access = Write in
  let ctx, cc = update_ctx_along_read_place config span access p ctx in
  let v, ctx, cc = comp2 cc (prepare_lplace config span p ctx) in
  (* Update the value *)
  match (v.ty, v.value) with
  | TAdt { id = def_id; generics; builtin = None }, VAdt av -> (
      (* There are two situations:
         - either the discriminant is already the proper one (in which case we
           don't do anything)
         - or it is not the proper one, in which case we replace the value with
           a variant with all its fields set to {!Bottom}
      *)
      match av.variant_id with
      | None -> [%craise] span "Found a struct value while expecting an enum"
      | Some variant_id' ->
          if variant_id' = variant_id then (* Nothing to do *)
            ((ctx, Unit), cc)
          else
            (* Replace the value *)
            let bottom_v =
              compute_expanded_bottom_adt_value span ctx def_id
                (Some variant_id) generics
            in
            let ctx, cc =
              comp cc (assign_to_place config span bottom_v p ctx)
            in
            ((ctx, Unit), cc))
  | TAdt { id = def_id; generics; builtin = None }, VBottom ->
      let bottom_v =
        compute_expanded_bottom_adt_value span ctx def_id (Some variant_id)
          generics
      in
      let ctx, cc = comp cc (assign_to_place config span bottom_v p ctx) in
      ((ctx, Unit), cc)
  | _, VSymbolic _ ->
      [%sanity_check] span (config.mode = SymbolicMode);
      (* This is a bit annoying: in theory we should expand the symbolic value
       * then set the discriminant, because in the case the discriminant is
       * exactly the one we set, the fields are left untouched, and in the
       * other cases they are set to Bottom.
       * For now, we forbid setting the discriminant of a symbolic value:
       * setting a discriminant should only be used to initialize a value,
       * or reset an already initialized value, really. *)
      [%craise] span "Unexpected value"
  | _, (VAdt _ | VBottom) -> [%craise] span "Inconsistent state"
  | _, (VLiteral _ | VBorrow _ | VLoan _) -> [%craise] span "Unexpected value"

(** Push a frame delimiter in the context's environment *)
let ctx_push_frame (ctx : eval_ctx) : eval_ctx =
  { ctx with env = EFrame :: ctx.env }

(** Push a frame delimiter in the context's environment *)
let push_frame (ctx : eval_ctx) : eval_ctx = ctx_push_frame ctx

let move_return_value (config : config) (span : Meta.span)
    (pop_return_value : bool) (ctx : eval_ctx) :
    tvalue option * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr) =
  if pop_return_value then
    let ret_vid = LocalId.zero in
    let v, ctx, cc =
      eval_operand config span
        (Move (mk_place_from_var_id ctx span ret_vid))
        ctx
    in
    (Some v, ctx, cc)
  else (None, ctx, fun e -> e)

let pop_frame (config : config) (span : Meta.span) ~(pop_locals : bool)
    ~(pop_return_value : bool) (ctx : eval_ctx) :
    tvalue option * eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace eval_ctx_to_string ~span:(Some span) ctx];

  (* List the local variables, but the return variable *)
  let ret_vid = LocalId.zero in
  let rec list_locals env =
    match env with
    | [] -> [%craise] span "Inconsistent environment"
    | EAbs _ :: env -> list_locals env
    | EBinding (BDummy _, _) :: env -> list_locals env
    | EBinding (BVar var, _) :: env ->
        let locals = list_locals env in
        if var.index <> ret_vid then var.index :: locals else locals
    | EFrame :: _ -> []
  in
  let locals : LocalId.id list = list_locals ctx.env in
  (* Debug *)
  [%ltrace
    "locals in which to drop the outer loans: ["
    ^ String.concat "," (List.map LocalId.to_string locals)
    ^ "]"];

  (* Drop the outer *loans* we find in the local variables *)
  let ctx, cc =
    if pop_locals then
      (* Drop the loans *)
      let locals = List.rev locals in
      fold_left_apply_continuation
        (fun lid ctx ->
          drop_outer_loans_at_lplace config span
            (mk_place_from_var_id ctx span lid)
            ctx)
        locals ctx
    else (ctx, fun e -> e)
  in
  (* Debug *)
  [%ltrace
    "after dropping outer loans in local variables:\n"
    ^ eval_ctx_to_string ~span:(Some span) ctx];

  (* Move the return value out of the return variable *)
  let v, ctx, cc1 = move_return_value config span pop_return_value ctx in
  let cc = cc_comp cc cc1 in
  (* Check that the return value is valid (i.e., it doesn't contain the bottom value) *)
  let _ =
    match v with
    | None -> ()
    | Some ret_value ->
        [%sanity_check] span (not (bottom_in_value ctx.ended_regions ret_value))
  in

  (* Pop the frame - we remove the [Frame] delimiter, and reintroduce all
   * the local variables (which may still contain borrow permissions - but
   * no outer loans) as dummy variables in the caller frame *)
  let rec pop env =
    match env with
    | [] -> [%craise] span "Inconsistent environment"
    | EAbs abs :: env -> EAbs abs :: pop env
    | EBinding (_, v) :: env ->
        let vid = ctx.fresh_dummy_var_id () in
        EBinding (BDummy vid, v) :: pop env
    | EFrame :: env -> (* Stop here *) env
  in
  let env = pop ctx.env in
  let ctx = { ctx with env } in
  (* Return *)
  (v, ctx, cc)

(** Pop the current frame and assign the returned value to its destination. *)
let pop_frame_assign (config : config) (span : Meta.span) (dest : place) :
    cm_fun =
 fun ctx ->
  let v, ctx, cc =
    pop_frame config span ~pop_locals:true ~pop_return_value:true ctx
  in
  comp cc (assign_to_place config span (Option.get v) dest ctx)

(** Evaluate [Box::new] in concrete mode. *)
let eval_box_new_concrete (config : config) (span : Meta.span)
    (generics : generic_args) (call : call) : cm_fun =
 fun ctx ->
  (* Check and retrieve the arguments *)
  match
    (generics.regions, generics.types, generics.const_generics, call.args)
  with
  | [], [ boxed_ty ], [], [ input ] ->
      (* Move the input value *)
      let v, ctx, cc = eval_operand config span input ctx in
      [%cassert] span (v.ty = boxed_ty)
        "The input given to Box::new doesn't have the proper type";

      (* Create the new box. We use the type of the destination: this saves us
         from having to look up the id of the declaration of [Box]. *)
      let box_ty = call.dest.ty in
      [%cassert] span
        (ty_as_opt_box box_ty = Some boxed_ty)
        "The destination of Box::new doesn't have the proper type";
      let box_v = VAdt { variant_id = None; fields = [ v ] } in
      let box_v = mk_tvalue span box_ty box_v in
      comp cc (assign_to_place config span box_v call.dest ctx)
  | _ -> [%craise] span "Inconsistent state"

(** Helper

    Create abstractions (with no avalues, which have to be inserted afterwards)
    from a list of abs region groups.

    [region_can_end]: gives the region groups from which we generate functions
    which can end or not. *)
let create_empty_abstractions_from_abs_region_groups
    (kind : RegionGroupId.id -> abs_kind) (rgl : abs_region_group list)
    (region_can_end : RegionGroupId.id -> bool) : abs list =
  (* We use a reference to progressively create a map from abstraction ids
   * to set of ancestor regions. Note that {!abs_to_ancestors_regions} [abs_id]
   * returns the union of:
   * - the regions of the ancestors of abs_id
   * - the regions of abs_id
   *)
  let abs_to_ancestors_regions : region_set AbsId.Map.t ref =
    ref AbsId.Map.empty
  in
  (* Auxiliary function to create one abstraction *)
  let create_abs (rg_id : RegionGroupId.id) (rg : abs_region_group) : abs =
    let abs_id = rg.id in
    let parents =
      List.fold_left
        (fun s pid -> AbsId.Set.add pid s)
        AbsId.Set.empty rg.parents
    in
    let regions =
      let owned = RegionSet.of_list rg.regions in
      { owned }
    in
    let ancestors_regions_union_current_regions =
      RegionSet.union regions.owned regions.owned
    in
    let can_end = region_can_end rg_id in
    abs_to_ancestors_regions :=
      AbsId.Map.add abs_id ancestors_regions_union_current_regions
        !abs_to_ancestors_regions;
    (* Create the abstraction *)
    {
      abs_id;
      kind = kind rg_id;
      can_end;
      parents;
      regions;
      ended_subabs = AbsLevelSet.empty;
      avalues = [];
      (* For now the continuation is empty: we will initialize it later, when
         actually inserting the avalues. TODO: this two-phase initialization is
         not super clean. *)
      cont = None;
    }
  in
  (* Apply *)
  RegionGroupId.mapi create_abs rgl

let create_push_abstractions_from_abs_region_groups
    (kind : RegionGroupId.id -> abs_kind) (rgl : abs_region_group list)
    (region_can_end : RegionGroupId.id -> bool)
    (compute_abs_avalues :
      region_group_id -> abs -> eval_ctx -> tavalue list * abs_cont option)
    (ctx : eval_ctx) : eval_ctx =
  (* Initialize the abstractions as empty (i.e., with no avalues) abstractions *)
  let empty_absl =
    create_empty_abstractions_from_abs_region_groups kind rgl region_can_end
  in
  let rg_ids = RegionGroupId.mapi (fun rg_id _ -> rg_id) rgl in

  (* Compute and add the avalues to the abstractions, the insert the abstractions
   * in the context. *)
  let insert_abs (ctx : eval_ctx) ((rg_id, abs) : region_group_id * abs) :
      eval_ctx =
    (* Compute the values to insert in the abstraction *)
    let avalues, cont = compute_abs_avalues rg_id abs ctx in
    (* Add the avalues to the abstraction *)
    let abs = { abs with avalues; cont } in
    (* Insert the abstraction in the context *)
    let ctx = { ctx with env = EAbs abs :: ctx.env } in
    (* Return *)
    ctx
  in
  List.fold_left insert_abs ctx (List.combine rg_ids empty_absl)

type symbolic_fun_call_inst = {
  call_kind : fn_ptr_kind;
  call_generics : generic_args;
  call_span : Meta.span;
  call_sig : bound_fun_sig;
  call_inst_sig : inst_fun_sig;
}

let mk_symbolic_fun_call_inst (span : Meta.span) (ctx : eval_ctx)
    ~(call_kind : fn_ptr_kind) ~(call_generics : generic_args)
    ~(call_span : Meta.span) ~(inst_generics : generic_args)
    ~(tr_self : trait_ref_kind) (signature : bound_fun_sig) :
    symbolic_fun_call_inst =
  {
    call_kind;
    call_generics;
    call_span;
    call_sig = signature;
    call_inst_sig =
      (let merge_groups =
         match call_kind with
         | Fun fid -> FunsAnalysis.merge_region_groups ctx.fun_ctx.fun_infos fid
         | TraitMethod _ -> false
       in
       instantiate_fun_sig ~merge_groups (Some span) ctx inst_generics tr_self
         signature);
  }

(** Auxiliary helper for [eval_function_call_symbolic] Instantiate the signature
    and introduce fresh abstractions and region ids while doing so.

    We perform some manipulations when instantiating the signature.

    # Trait impl calls ================== In particular, we have a special
    treatment of trait method calls when the trait ref is a known impl.

    For instance:
    {[
      trait HasValue {
        fn has_value(&self) -> bool;
      }

      impl<T> HasValue for Option<T> {
        fn has_value(&self) {
          match self {
            None => false,
            Some(_) => true,
          }
        }
      }

      fn option_has_value<T>(x: &Option<T>) -> bool {
        x.has_value()
      }
    ]}

    The generated code looks like this:
    {[
      structure HasValue (Self : Type) = {
        has_value : Self -> result bool
      }

      let OptionHasValueImpl.has_value (Self : Type) (self : Self) : result bool =
        match self with
        | None => false
        | Some _ => true

      let OptionHasValueInstance (T : Type) : HasValue (Option T) = {
        has_value = OptionHasValueInstance.has_value
      }
    ]}

    In [option_has_value], we don't want to refer to the [has_value] method of
    the instance of [HasValue] for [Option<T>]. We want to refer directly to the
    function which implements [has_value] for [Option<T>]. That is, instead of
    generating this:
    {[
      let option_has_value (T : Type) (x : Option T) : result bool =
        (OptionHasValueInstance T).has_value x
    ]}

    We want to generate this:
    {[
      let option_has_value (T : Type) (x : Option T) : result bool =
        OptionHasValueImpl.has_value T x
    ]} *)
let eval_function_call_symbolic_inst (span : Meta.span) (func : fn_ptr)
    (ctx : eval_ctx) : symbolic_fun_call_inst =
  match func.kind with
  | Fun fid ->
      let tr_self = UnknownTrait __FUNCTION__ in
      (* Lookup the declaration *)
      let def = ctx_lookup_fun_decl span ctx fid in
      let signature = bound_fun_sig_of_decl def in
      mk_symbolic_fun_call_inst span ctx ~call_kind:func.kind
        ~call_generics:func.generics ~call_span:def.item_meta.span
        ~inst_generics:func.generics ~tr_self signature
  | TraitMethod (trait_ref, method_id) ->
      let trait_decl_ref = trait_ref.trait_decl_ref in
      (* This should be a call to a trait clause method (if it were a method
         coming from an impl, there should be no indirection through the
         trait reference itself (Charon should have simplified this). *)
      (*[%sanity_check] span
          (match trait_ref.kind with
          | TraitImpl _ -> false
          | _ -> true);*)
      let trait_decl = ctx_lookup_trait_decl span ctx trait_decl_ref.id in
      let meth =
        ([%silent_unwrap] span (lookup_trait_decl_method trait_decl method_id))
          .item_binder_value
          .binder_value
      in
      let signature =
        [%silent_unwrap] span
          (Substitute.lookup_flat_method_sig ctx.crate trait_decl_ref.id
             method_id)
      in
      let tr_self = trait_ref.kind in
      let inst_generics =
        concat_generic_args trait_decl_ref.generics func.generics
      in
      mk_symbolic_fun_call_inst span ctx ~call_kind:func.kind
        ~call_generics:func.generics ~call_span:meth.item_meta.span
        ~inst_generics ~tr_self signature

(** Helper: introduce a fresh symbolic value for a global.

    We return the value as well as its type with regions. Note that we currently
    only support globals whose (instantiated) type doesn't contain regions,
    except for a top-level static shared reference. *)
let eval_global_as_fresh_symbolic_value (span : Meta.span)
    (gref : global_decl_ref) (ctx : eval_ctx) :
    eval_ctx * tvalue * rty * (SA.expr -> SA.expr) =
  let generics = gref.generics in
  let global = ctx_lookup_global_decl span ctx gref.id in
  (* The global might itself be a (static) reference - TODO: generalize *)
  match global.ty with
  | TRef (RStatic, _, RShared) ->
      (* Instantiate the type  *)
      let generics = Subst.generic_args_erase_regions generics in
      let subst =
        [%add_loc] Subst.make_subst_from_generics (Some span) global.generics
          generics Self
      in
      let ty = Subst.erase_regions_substitute_types subst global.ty in
      (* Decompose *)
      let inner_ty =
        match ty with
        | TRef (_, ty, RShared) -> ty
        | _ -> [%internal_error] span
      in
      [%cassert] span (ty_no_regions inner_ty) "Unimplemented";
      (* We introduce a borrow whose corresponding loan is in a region
         abstraction owning the static region, allowing the borrow to live as
         long as needed. *)
      let sval = mk_fresh_symbolic_value span ctx inner_ty in
      let v = mk_tvalue_from_symbolic_value sval in
      let ctx, borrow = push_value_to_static_shared_loan span ctx v inner_ty in
      let cc = S.synthesize_global_eval gref sval in
      (ctx, borrow, TRef (RStatic, inner_ty, RShared), cc)
  | _ ->
      [%cassert] span (ty_no_regions global.ty) "Unimplemented";
      (* Instantiate the type  *)
      let generics = Subst.generic_args_erase_regions generics in
      let subst =
        [%add_loc] Subst.make_subst_from_generics (Some span) global.generics
          generics Self
      in
      let ty = Subst.erase_regions_substitute_types subst global.ty in
      [%cassert] span (ty_no_regions ty) "Unimplemented";
      let sval = mk_fresh_symbolic_value span ctx ty in
      let cc = S.synthesize_global_eval gref sval in
      (ctx, mk_tvalue_from_symbolic_value sval, ty, cc)

(** Repeatedly end a region abstraction without parents such that
    [candidate ctx abs] holds and whose end is unobservable:
    [unchanged ctx ctx'] holds and the abstractions which were not introduced by
    function calls (nor by joins, if [ignore_joins]) are unchanged. We end the
    abstractions of the most recent function calls first: the raw pointers
    manipulated by a function call may come from a previous call (for instance,
    a slice created by [from_raw_parts] from a pointer given by [as_mut_ptr]).
*)
let rec end_unobservable_abs (config : config) (span : Meta.span)
    ~(ignore_joins : bool) (candidate : eval_ctx -> abs -> bool)
    (unchanged : eval_ctx -> eval_ctx -> bool) : cm_fun =
 fun ctx ->
  let other_abs (ctx : eval_ctx) : abs list =
    env_filter_map_abs
      (fun abs ->
        match abs.kind with
        | FunCall _ -> None
        | Join when ignore_joins -> None
        | _ -> Some abs)
      ctx.env
  in
  let is_candidate = candidate ctx in
  let try_end (abs : abs) :
      (eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr)) option =
    if is_candidate abs && abs.can_end && AbsId.Set.is_empty abs.parents then
      let ctx', cc = InterpBorrows.end_abs config span abs.abs_id 0 ctx in
      if unchanged ctx ctx' && other_abs ctx' = other_abs ctx then
        Some (ctx', cc)
      else None
    else None
  in
  let call_id (abs : abs) =
    match abs.kind with
    | FunCall (call_id, _) -> FunCallId.to_int call_id
    | _ -> -1
  in
  let abs_list =
    List.sort
      (fun a0 a1 -> Int.compare (call_id a1) (call_id a0))
      (env_filter_map_abs (fun abs -> Some abs) ctx.env)
  in
  match List.find_map try_end abs_list with
  | None -> (ctx, fun e -> e)
  | Some (ctx, cc) ->
      comp cc
        (end_unobservable_abs config span ~ignore_joins candidate unchanged ctx)

(** Register the region abstractions of a function call which borrow values from
    the heap, that is, the abstractions of the region groups whose backward
    functions are stateful and which appear in the output as the regions of
    references (for instance [NonNull::as_mut], or a function which returns a
    borrow obtained from a raw pointer). See [end_dead_heap_borrows].

    We ignore the regions which only appear as parameters of ADTs (for instance
    [S<'a>] with a field of type [PhantomData<&'a mut T>]): we can not detect
    when the values of those ADTs are dead (the expanded values do not carry the
    regions), so the backward functions are called later (lazily, or when the
    function returns). *)
let register_heap_borrow_abs (ctx : eval_ctx) (fid : fn_ptr_kind)
    (inst_sg : inst_fun_sig) : unit =
  let stateful_groups =
    match fid with
    | Fun fid -> (
        match FunsAnalysis.lookup_fun_decl_info ctx.fun_ctx.fun_infos fid with
        | Some { stateful_region_groups = Some gids; _ } -> gids
        | Some { stateful = true; _ } ->
            List.map
              (fun (rg : region_group) -> rg.id)
              inst_sg.regions_hierarchy
        | _ -> [])
    | TraitMethod _ -> []
  in
  let output_regions = RegionsHierarchy.top_level_regions [ inst_sg.output ] in
  let ref_regions = ref RegionId.Set.empty in
  let visitor =
    object
      inherit [_] iter_ty as super

      method! visit_TRef env r ty kind =
        (match r with
        | RVar (Free r) -> ref_regions := RegionId.Set.add r !ref_regions
        | _ -> ());
        super#visit_TRef env r ty kind
    end
  in
  visitor#visit_ty () inst_sg.output;
  List.iter
    (fun gid ->
      let rg = RegionGroupId.nth inst_sg.regions_hierarchy gid in
      if
        List.exists
          (fun r ->
            match r with
            | RVar (Free r) ->
                RegionId.Set.mem r output_regions
                && RegionId.Set.mem r !ref_regions
            | _ -> false)
          rg.regions
      then
        Hashtbl.replace ctx.heap_borrow_abs
          (RegionGroupId.nth inst_sg.abs_regions_hierarchy gid).id ())
    stateful_groups

(** In the functions which access the heap, end the region abstractions of the
    function calls which borrow values from the heap (see
    [register_heap_borrow_abs]) as soon as their borrows are dead: their
    backward functions give the values back to the heap, which must happen
    before the values are accessed again through other pointers (the heap model
    fails if we access a value which is borrowed).

    The borrows are dead if ending the abstraction modifies neither the live
    local variables ([live]) nor the abstractions which were not introduced by
    function calls or joins (the joins may have merged the borrows of the dead
    abstraction with other borrows, for instance shared borrows of the value in
    the heap), and if no live value has a type which mentions the regions which
    ended (for instance, a structure with a [PhantomData<&'a mut T>] field). We
    end the abstractions of the most recent calls first.

    The liveness analysis does not need to be exact: if we end a borrow which is
    used later, the symbolic execution fails when it is used (the borrow was
    replaced with ⊥). *)
let end_dead_heap_borrows (config : config) (span : Meta.span)
    (live : LocalId.Set.t) : cm_fun =
  let live_values (ctx : eval_ctx) : tvalue list =
    List.filter_map
      (fun (e : env_elem) ->
        match e with
        | EBinding (BVar { index; _ }, v) when LocalId.Set.mem index live ->
            Some v
        | _ -> None)
      ctx.env
  in
  let unchanged (ctx : eval_ctx) (ctx' : eval_ctx) : bool =
    (* The values whose types mention the regions which ended are dead *)
    let ended = RegionId.Set.diff ctx'.ended_regions ctx.ended_regions in
    let visitor =
      object
        inherit [_] iter_tvalue as super

        method! visit_tvalue env v =
          if
            ty_has_regions_in_pred ctx.type_ctx.type_infos
              (function
                | RVar (Free r) -> RegionId.Set.mem r ended
                | _ -> false)
              v.ty
          then raise Utils.Found
          else super#visit_tvalue env v

        method! visit_symbolic_value _ sv =
          if symbolic_value_has_ended_regions ended sv then raise Utils.Found
      end
    in
    let live_values' = live_values ctx' in
    live_values' = live_values ctx
    &&
    try
      List.iter (visitor#visit_tvalue ()) live_values';
      true
    with Utils.Found -> false
  in
  end_unobservable_abs config span ~ignore_joins:true
    (fun ctx abs -> Hashtbl.mem ctx.heap_borrow_abs abs.abs_id)
    unchanged

(** The configuration to evaluate the body of a function in symbolic mode. If
    the function accesses the heap, we end the borrows of values in the heap as
    soon as they are dead (see [end_dead_heap_borrows]): we need the liveness of
    the locals. *)
let mk_symbolic_fun_config (ctx : eval_ctx) (fdef : fun_decl) : config =
  let live_locals =
    match body_as_body fdef.body with
    | Some body when FunsAnalysis.is_stateful ctx.fun_ctx.fun_infos fdef.def_id
      -> Some (compute_live_locals body.body)
    | _ -> None
  in
  mk_config ~live_locals SymbolicMode

(** Evaluate a statement. *)
let rec eval_statement (config : config) (st : statement) : stl_cm_fun =
 fun ctx ->
  (* Debugging *)
  [%ltrace
    "\n**About to evaluate statement** ("
    ^ Errors.raw_span_to_string st.span
    ^ "): [\n"
    ^ statement_to_string_with_tab ctx st
    ^ "\n]\n\n**Context**:\n"
    ^ eval_ctx_to_string ~span:(Some st.span) ctx
    ^ "\n"];

  (* Take a snapshot of the current context for the purpose of generating pretty names *)
  let cc = S.save_snapshot ctx in
  (* Expand the symbolic values if necessary - we need to do that before
     checking the invariants *)
  let ctx, cc = comp cc (greedy_expand_symbolic_values st.span ctx) in
  (* Sanity check *)
  Invariants.check_invariants st.span ctx;

  (* End the dead borrows of values in the heap, before and after the
     statement (see [end_dead_heap_borrows]) *)
  let live_before, live_after =
    match config.live_locals with
    | Some live -> (
        match StatementId.Map.find_opt st.statement_id live with
        | Some (before, after) -> (Some before, Some after)
        | None -> (None, None))
    | None -> (None, None)
  in
  let end_dead_borrows (live : LocalId.Set.t option) : cm_fun =
   fun ctx ->
    match live with
    | Some live -> end_dead_heap_borrows config st.span live ctx
    | None -> (ctx, fun e -> e)
  in
  let ctx, cc = comp cc (end_dead_borrows live_before ctx) in

  (* Evaluate the statement *)
  let config =
    match st.kind with
    | Switch _ -> { config with live_after_switch = live_after }
    | _ -> config
  in
  let ctx_resl, cc = comp cc (eval_statement_raw config st ctx) in
  let ctx_res_cfl =
    List.map
      (fun (ctx, res) ->
        match res with
        | Unit ->
            let ctx, cf = end_dead_borrows live_after ctx in
            ((ctx, res), cf)
        | _ -> ((ctx, res), fun e -> e))
      ctx_resl
  in
  let ctx_resl, cfl = List.split ctx_res_cfl in
  (ctx_resl, cc_comp cc (fun el -> List.map2 (fun cf e -> cf e) cfl el))

and eval_statement_list (config : config) span (stmts : statement list) :
    stl_cm_fun =
 fun ctx ->
  match stmts with
  | [] -> ([ (ctx, Unit) ], cf_singleton __FILE__ __LINE__ span)
  | hd :: tl ->
      (* Evaluate the first statement *)
      let ctx_resl, cf_st1 = eval_statement config hd ctx in
      (* Evaluate the sequence (evaluate the following statements if the first
         statement successfully evaluated, otherwise transmit the control-flow
         break) *)
      let ctx_res_cfl =
        List.map
          (fun (ctx, res) ->
            match res with
            (* Evaluation successful: evaluate the second statement *)
            | Unit -> eval_statement_list config span tl ctx
            (* Control-flow break: transmit. We enumerate the cases on purpose *)
            | Panic | Break _ | Continue _ | Return ->
                ([ (ctx, res) ], cf_singleton __FILE__ __LINE__ span))
          ctx_resl
      in
      (* Put everything together:
         - we return the flattened list of contexts and results
         - we need to build the continuation which will build the whole
           expression from the continuations for the individual branches
      *)
      let ctx_resl, cf_st2 = comp_seqs __FILE__ __LINE__ span ctx_res_cfl in
      (ctx_resl, cc_comp cf_st1 cf_st2)

and eval_block (config : config) (b : block) : stl_cm_fun =
 fun ctx ->
  [%ltrace
    "About to evaluate block ("
    ^ Errors.raw_span_to_string b.span
    ^ "):\n"
    ^ block_to_string_with_tab ctx b
    ^ "\n"];
  eval_statement_list config b.span b.statements ctx

and eval_statement_raw (config : config) (st : statement) : stl_cm_fun =
 fun ctx ->
  [%ltrace "statement:\n" ^ statement_to_string_with_tab ctx st ^ "\n"];
  match st.kind with
  | Assign (p, rvalue) when Option.is_some (raw_ptr_deref_place p) ->
      (* Write through a raw pointer: the value goes to the heap *)
      [%cassert] st.span
        (not (ExpressionsUtils.rvalue_accesses_global rvalue))
        "Unsupported: writing a global through a raw pointer";
      [%cassert] st.span
        (not (ty_has_borrows (Some st.span) ctx.type_ctx.type_infos p.ty))
        "Unsupported: writing a value containing borrows through a raw pointer";
      let q = Option.get (raw_ptr_deref_place p) in
      let res, ctx, cc = eval_rvalue_not_global config st.span rvalue ctx in
      begin
        match res with
        | Error EPanic ->
            ([ (ctx, Panic) ], cc_singleton __FILE__ __LINE__ st.span cc)
        | Ok v ->
            let ptr, ctx, cc =
              comp2 cc (eval_operand config st.span (Copy q) ctx)
            in
            let unit_sv = mk_fresh_symbolic_value st.span ctx mk_unit_ty in
            let cc =
              cc_comp cc
                (S.synthesize_function_call st.span SymbolicAst.RawPtrWrite ctx
                   None []
                   (mk_generic_args_from_types [ p.ty ])
                   [ ptr; v ]
                   [ S.mk_opt_place_from_op st.span (Copy q) ctx; None ]
                   unit_sv None)
            in
            ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ st.span cc)
      end
  | Assign (p, rvalue) ->
      if
        (* We handle global assignments separately as a specific case. *)
        ExpressionsUtils.rvalue_accesses_global rvalue
      then (
        [%ltrace "The rvalue is a global access"];
        eval_rvalue_global config st.span p rvalue ctx)
      else (
        [%ltrace "The rvalue is not a global access"];
        (* Evaluate the rvalue *)
        let res, ctx, cc = eval_rvalue_not_global config st.span rvalue ctx in
        (* Assign *)
        [%ltrace
          "about to assign to place: " ^ place_to_string ctx p
          ^ "\n- Context:\n"
          ^ eval_ctx_to_string ~span:(Some st.span) ctx];
        let (ctx, res), cf_assign =
          match res with
          | Error EPanic -> ((ctx, Panic), fun e -> e)
          | Ok rv ->
              (* Update the synthesized AST - here we store additional span-information.
                 We do it only in specific cases (it is not always useful, and
                 also it can lead to issues - for instance, if we borrow a
                 reserved borrow, we later can't translate it to pure values...) *)
              let cc =
                match rvalue with
                | Len _ -> [%craise] st.span "Len is not handled yet"
                | Repeat _ ->
                    [%craise] st.span
                      "Repeat should have been removed in a micropass"
                | Use _
                | RvRef
                    ( _,
                      ( BShared
                      | BMut
                      | BTwoPhaseMut
                      | BShallow
                      | BUniqueImmutable ),
                      _ )
                | NullaryOp _
                | UnaryOp _
                | BinaryOp _
                | Discriminant _
                | Aggregate _
                | RawPtr _ ->
                    let p = S.mk_mplace st.span p ctx in
                    let rp = rvalue_get_place rvalue in
                    let rp =
                      Option.map (fun rp -> S.mk_mplace st.span rp ctx) rp
                    in
                    S.synthesize_assignment ctx p rv rp
              in
              let ctx, cc = comp cc (assign_to_place config st.span rv p ctx) in
              ((ctx, Unit), cc)
        in
        let cc = cc_comp cc cf_assign in
        (* Compose and apply *)
        ([ (ctx, res) ], cc_singleton __FILE__ __LINE__ st.span cc))
  | SetDiscriminant (p, variant_id) ->
      let (ctx, res), cc = set_discriminant config st.span p variant_id ctx in
      ([ (ctx, res) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | PlaceMention _ ->
      (* A place mention just needs to check the place projections are valid; for
         now we treat this as a no-op *)
      ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ st.span (fun e -> e))
  | Drop (p, _, _, _) when Option.is_some (raw_ptr_deref_place p) ->
      (* Dropping a value through a raw pointer (for instance, [*q = v] first
         drops the old value of [*q]). We do not model the drop glue, but the
         value must be valid: we read it (and ignore it), so that dropping
         uninitialized memory fails. *)
      let _, ctx, cc = eval_operand config st.span (Copy p) ctx in
      ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | Drop (p, _, _, _) ->
      if !Config.drop_as_no_op then
        ([ (ctx, Unit) ], cf_singleton __FILE__ __LINE__ st.span)
      else
        let ctx, cc = drop_value config st.span p ctx in
        ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | StorageDead local ->
      let p = mk_place_from_var_id ctx st.span local in
      let ctx, cc = drop_value config st.span p ctx in
      ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | Assert (assertion, _on_failure, _) ->
      let (ctx, res), cc = eval_assertion config st.span assertion ctx in
      ([ (ctx, res) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | Call (call, _) -> eval_function_call config st.span call ctx
  | Panic _ | UnwindTerminate | UndefinedBehavior ->
      (* Evaluate to a panic only if the execution is concrete, otherwise we stop
         evaluating there and synthesize a [panic] node in the symbolic AST. *)
      if config.mode = ConcreteMode then
        ([ (ctx, Panic) ], cf_singleton __FILE__ __LINE__ st.span)
      else ([], cf_empty __FILE__ __LINE__ st.span SA.Panic)
  | Return -> ([ (ctx, Return) ], cf_singleton __FILE__ __LINE__ st.span)
  | UnwindResume -> [%craise] st.span "unwinding is not supported by Aeneas"
  | Break i -> ([ (ctx, Break i) ], cf_singleton __FILE__ __LINE__ st.span)
  | Continue i -> ([ (ctx, Continue i) ], cf_singleton __FILE__ __LINE__ st.span)
  | StorageLive _ | Nop ->
      ([ (ctx, Unit) ], cf_singleton __FILE__ __LINE__ st.span)
  | Loop loop_body ->
      let eval_loop_body = eval_block config loop_body in
      InterpLoops.eval_loop config st.span eval_loop_body ctx
  | Switch (data, branches) -> eval_switch config st.span data branches ctx
  | _ ->
      [%craise] st.span ("unsupported statement: " ^ show_statement_kind st.kind)

and eval_rvalue_global (config : config) (span : Meta.span) (dest : place)
    (rv : rvalue) : stl_cm_fun =
 fun ctx ->
  (* One of the micro-passes makes sures there is only one case to handle *)
  match rv with
  | RvRef ({ kind = PlaceGlobal gref; ty = _ }, BShared, _) ->
      eval_global_ref config span dest gref RShared ctx
  | _ ->
      [%craise] span
        ("Unsupported case of rvalue accessing a global:\n"
        ^ Print.EvalCtx.rvalue_to_string ctx rv)

and eval_global_ref (config : config) (span : Meta.span) (dest : place)
    (gref : global_decl_ref) (rk : ref_kind) : stl_cm_fun =
 fun ctx ->
  (* We only support shared references to globals *)
  [%cassert] span (rk = RShared)
    "Can only create shared references to global values";
  match config.mode with
  | ConcreteMode ->
      (* We should treat the evaluation of the global as a call to the global body,
         then create a reference *)
      [%craise] span "Unimplemented"
  | SymbolicMode ->
      (* Generate a fresh symbolic value. In the translation, this fresh symbolic value will be
       * defined as equal to the value of the global (see {!S.synthesize_global_eval}).
       * We then create a reference to the global. *)
      let ctx, sval, rty, cf =
        eval_global_as_fresh_symbolic_value span gref ctx
      in
      (* Create a shared loan containing the global (in a region abstraction
         owning the static region), as well as a shared borrow *)
      let ctx, borrow = push_value_to_static_shared_loan span ctx sval rty in
      (* Assign the borrow to its destination *)
      let ctx, cc = assign_to_place config span borrow dest ctx in
      ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ span (cc_comp cf cc))

(** Evaluate a switch *)
and eval_switch (config : config) (span : Meta.span) (data : switch_data)
    (branches : block list) : stl_cm_fun =
 fun ctx ->
  let ctx, cc = eval_switch_prepare span ctx in
  comp cc (eval_switch_raw config span data branches ctx)

(** Prepare the context before evaluating a switch.

    TODO: generalize the join so that we don't have to do so. The problem is
    that we may symbolically expand some shared values which are in frozen
    region abstractions (and which we thus want to remain the same in the left
    and right branches). *)
and eval_switch_prepare (span : Meta.span) : cm_fun =
 fun ctx ->
  InterpJoin.reborrow_ashared_loans_symbolic_borrows span None
    ~with_abs_conts:true ctx

and eval_switch_raw (config : config) (span : Meta.span) (data : switch_data)
    (branches : block list) : stl_cm_fun =
 fun ctx ->
  (* We evaluate the scrutinee in two steps:
     first we prepare it, then we check if its value is concrete or
     symbolic. If it is concrete, we can then evaluate the operand
     directly, otherwise we must first expand the value.
     Note that we can't fully evaluate the operand *then* expand the
     value if it is symbolic, because the value may have been moved
     (and would thus floating in thin air...)! *)
  let branch (id : branch_id) : block =
    [%unwrap_with_span] span
      (List.nth_opt branches (BranchId.to_int id))
      "Switch branch index out of bounds"
  in
  let branch_for_case (matches : constant_expr -> bool) : block =
    match List.find_opt (fun (case, _) -> matches case) data.branches with
    | Some (_, id) -> branch id
    | None ->
        branch ([%unwrap_with_span] span data.fallback "No fallback branch")
  in
  match data.scrutinee with
  | SwitchValue op ->
      (* Evaluate the operand *)
      let op_v, ctx, cf_eval_op = eval_operand config span op ctx in
      let ctx0 = ctx in
      let ctx_resl, cf_switch =
        match (op_v.value, op_v.ty) with
        | VLiteral (VBool b), TScalar TBool ->
            let target = branch_for_case (fun case -> case.kind = CBool b) in
            eval_block config target ctx
        | VSymbolic sv, TScalar TBool ->
            (* Expand the symbolic boolean, and continue by evaluating
               the branches *)
            let true_block =
              branch_for_case (fun case -> case.kind = CBool true)
            in
            let false_block =
              branch_for_case (fun case -> case.kind = CBool false)
            in
            let (true_ctx, false_ctx), cf_bool =
              expand_symbolic_bool span sv
                (S.mk_opt_place_from_op span op ctx)
                ctx
            in
            (* Check if we should join the states after the if then else *)
            let join =
              (not (block_has_break_continue_return true_block))
              && not (block_has_break_continue_return false_block)
            in
            let resl_true = eval_block config true_block true_ctx in
            let resl_false = eval_block config false_block false_ctx in
            let ctx_resl, cf_branches =
              comp_seqs __FILE__ __LINE__ span [ resl_true; resl_false ]
            in
            let cc el =
              match cf_branches el with
              | [ e_true; e_false ] -> cf_bool (e_true, e_false)
              | _ -> [%internal_error] span
            in
            if join then
              try eval_switch_with_join config span cc ctx0 ctx_resl
              with Errors.RFailure ->
                (* If the join threw a recoverable error we do not join
                   and simply duplicate the code *)
                (ctx_resl, cc)
            else (ctx_resl, cc)
        | VLiteral (VScalar sv), TScalar (TInteger _ as int_ty) ->
            (* Sanity check *)
            [%sanity_check] span (Scalars.get_ty sv = scalar_as_integer int_ty);
            (* Find the branch *)
            let target =
              branch_for_case (fun case -> case.kind = CInteger sv)
            in
            eval_block config target ctx
        | VSymbolic sv, TScalar (TInteger _ as int_ty) ->
            let values, target_blocks =
              List.split
                (List.map
                   (fun (case, branch_id) ->
                     (TypesUtils.constant_expr_as_integer case, branch branch_id))
                   data.branches)
            in
            let otherwise =
              branch
                ([%unwrap_with_span] span data.fallback
                   "Integer switch has no fallback branch")
            in
            (* Expand the symbolic value *)
            let (ctx_branches, ctx_otherwise), cf_int =
              expand_symbolic_int span sv
                (S.mk_opt_place_from_op span op ctx)
                (scalar_as_integer int_ty) values ctx
            in
            (* Evaluate the branches: first the "regular" branches *)
            let resl_branches =
              List.map
                (fun (ctx, branch) -> eval_block config branch ctx)
                (List.combine ctx_branches target_blocks)
            in
            (* Then evaluate the "otherwise" branch *)
            let resl_otherwise = eval_block config otherwise ctx_otherwise in

            (* Should we join the contexts after the switch? *)
            let join =
              (not (List.exists block_has_break_continue_return target_blocks))
              && not (block_has_break_continue_return otherwise)
            in
            let resl, cf =
              comp_seqs __FILE__ __LINE__ span
                (resl_branches @ [ resl_otherwise ])
            in
            let cc el =
              let el, e_otherwise = Collections.List.pop_last el in
              cf_int (el, e_otherwise)
            in
            let cf = cc_comp cc cf in
            if join then
              (* Join the contexts *)
              try eval_switch_with_join config span cf ctx0 resl
              with Errors.RFailure ->
                (* If the join threw a recoverable error we do not join
                   and simply duplicate the code *)
                (resl, cf)
            else
              (* Do not join the contexts: compose the continuations and continue *)
              (resl, cf)
        | _ -> [%craise] span "Unsupported switch scrutinee"
      in
      (* Compose *)
      (ctx_resl, cc_comp cf_eval_op cf_switch)
  | SwitchDiscriminant p ->
      (* Access the place *)
      let access = Read in
      let expand_prim_copy = false in
      let _, p_v, ctx, cf_read_p =
        access_rplace_reorganize_and_read config span expand_prim_copy access p
          ctx
      in
      let ctx0 = ctx in
      (* Match on the value *)
      let ctx_resl, cf_match =
        (* The value may be shared: we need to ignore the shared loans
           to read the value itself *)
        let p_v = value_strip_shared_loans p_v in
        (* Match *)
        match p_v.value with
        | VAdt adt ->
            (* Evaluate the discriminant *)
            let dv = Option.get adt.variant_id in
            (* Find the branch, evaluate and continue *)
            let target =
              branch_for_case (fun case ->
                  match case.kind with
                  | CDiscriminant (_, variant_id) -> variant_id = dv
                  | _ -> false)
            in
            eval_block config target ctx
        | VSymbolic sv ->
            (* Expand the symbolic value - may lead to branching *)
            let ctxl, cf_expand =
              expand_symbolic_adt span sv (Some (S.mk_mplace span p ctx)) ctx
            in
            (* Re-evaluate the switch - the value is not symbolic anymore,
               which means we will go to the other branch *)
            let resl =
              List.map
                (fun ctx -> (eval_switch config span data branches) ctx)
                ctxl
            in
            (* Should we join the contexts after the match? *)
            let join =
              not (List.exists block_has_break_continue_return branches)
            in
            let ctx_resl, cf = comp_seqs __FILE__ __LINE__ span resl in
            let cc = cc_comp cf_expand cf in
            if join then (* Join the contexts *)
              try eval_switch_with_join config span cc ctx0 ctx_resl
              with Errors.RFailure ->
                (* If the join threw a recoverable error we do not join
                   and simply duplicate the code *)
                (ctx_resl, cc)
            else
              (* Compose the continuations *)
              (ctx_resl, cc)
        | _ -> [%craise] span "Inconsistent state"
      in
      (* Compose *)
      (ctx_resl, cc_comp cf_read_p cf_match)

(** Evaluate a switch in case we need to branch and want to join the contexts
    afterwards.

    - [cf_switch_scrut]: the continuation introduced after branching on the
      symbolic scrutinee. Expects the symbolic expressions for the branches, and
      builds the branching expressions (e.g., for an [if then else]: given
      expressions for the [then] and [else] branches, reconstructs the full
      [if then else] expression).
    - [resl_branches]: each element of the list corresponds to the result of
      evaluating a branch. The list of eval contexts and evaluation results
      should be either empty (if we reached a panic statement: we abort the
      symbolic execution there) or a list with one element (if we did not abort
      execution because of a panic statement). The continuation expects the
      symbolic expression for what happens at the end of the branch, and
      reconstructs the expression for the full branch. *)
and eval_switch_with_join (config : config) (span : Meta.span)
    (cf : SA.expr list -> SA.expr) (ctx0 : eval_ctx)
    (ctx_resl : (eval_ctx * statement_eval_res) list) :
    (eval_ctx * statement_eval_res) list * (SA.expr list -> SA.expr) =
  (* Count the number of contexts to join.

     Note that all evaluation results should be [Unit]: break, continue and
     return should not happen as we attempt to join only if the code in the
     branches doesn't contain break, etc. instructions. It can also not be
     panic as once we reach a panic we stop the symbolic execution (we simply
     synthesize a panic node in the symbolic AST). *)
  [%sanity_check] span (List.for_all (fun (_, res) -> res = Unit) ctx_resl);
  (* End the dead borrows of values in the heap at the end of every branch (see
     [config.live_after_switch]) *)
  let ctx_resl, cf =
    match config.live_after_switch with
    | None -> (ctx_resl, cf)
    | Some live ->
        let ctx_ccl =
          List.map
            (fun (ctx, res) ->
              let ctx, cc = end_dead_heap_borrows config span live ctx in
              ((ctx, res), cc))
            ctx_resl
        in
        let ctx_resl, ccl = List.split ctx_ccl in
        (ctx_resl, fun el -> cf (List.map2 (fun cc e -> cc e) ccl el))
  in
  let ctxl = List.map fst ctx_resl in
  let num_units = List.length ctxl in
  if num_units = 0 then (
    ( (* We only have panics: nothing to do *)
      [],
      fun el ->
        [%sanity_check] span (el = []);
        cf [] ))
  else if num_units = 1 then
    (* No need to join the contexts: continue with the current context, and inline
       what happens inside the loop inside the branching expression. *)
    let ctx = List.hd ctxl in
    ([ (ctx, Unit) ], cf)
  else (
    (* We need to join the contexts *)
    [%ldebug
      "About to join contexts after an [if then else]." ^ "\n- initial ctx:\n"
      ^ eval_ctx_to_string ctx0 ^ "\n\n"
      ^ String.concat "\n\n"
          (List.map
             (fun (ctx, res) ->
               "- eval_ctx (res: "
               ^ show_statement_eval_res res
               ^ "):\n" ^ eval_ctx_to_string ctx)
             ctx_resl)];
    let ctx_to_join =
      List.filter_map
        (fun (ctx, res) -> if res = Unit then Some ctx else None)
        ctx_resl
    in
    (* Note that we make the join *recoverable*: if the join fails (because
       it requires supporting some unsupported case) it is possible to recover
       from it, in which case we simply duplicate the code after the switch *)
    let _, joined_ctx =
      InterpJoin.join_ctxs_list config span ~recoverable:!Config.recover_joins
        ~with_abs_conts:true Join ctx_to_join
    in
    [%ldebug "Joined ctx:\n" ^ eval_ctx_to_string joined_ctx];
    let ctx0_aids = env_get_abs_ids ctx0.env in
    [%ldebug "ctx0_aids:\n" ^ AbsId.Set.to_string None ctx0_aids];
    (* The join drops the abstractions which were ended in some branches only:
       this would lose the effects of the backward functions which give values
       back to the heap (see [end_dead_heap_borrows]). It also merges the
       abstractions introduced in the branches into join abstractions, whose
       continuations can not call (stateful, failing) backward functions. If
       one of those happens, we do not join. *)
    let joined_aids = env_get_abs_ids joined_ctx.env in
    [%cassert_recover] !Config.recover_joins span
      (List.for_all
         (fun ctx ->
           AbsId.Set.for_all
             (fun id ->
               (not (Hashtbl.mem ctx.heap_borrow_abs id))
               || AbsId.Set.mem id joined_aids)
             (env_get_abs_ids ctx.env))
         ctx_to_join)
      "Joining the branches would drop the borrow of a value in the heap";

    (* We need to update the fresh abstraction continuations in the joined context,
       to reflect the fact that in the symbolic AST they should be introduced by
       the branching expression (they are bound by the let-binding we introduce) *)
    let joined_ctx =
      Contexts.ctx_map_abs
        (fun abs ->
          if AbsId.Set.mem abs.abs_id ctx0_aids then abs
          else
            (* The abstraction is fresh and is thus introduced by the join:
                we need to update its continuation *)
            InterpAbs.add_abs_cont_to_abs span joined_ctx abs (EJoin abs.abs_id))
        joined_ctx
    in
    [%ldebug
      "Joined ctx (after updating the abs conts):\n"
      ^ eval_ctx_to_string joined_ctx];

    (* Compute the output values *)
    let output_svalues =
      InterpJoin.compute_ctx_fresh_ordered_symbolic_values span
        ~only_modified_svalues:true ctx0 joined_ctx
    in
    let output_svalue_ids =
      List.map (fun (sv : symbolic_value) -> sv.sv_id) output_svalues
    in

    let output_abs =
      List.filter_map
        (fun (e : env_elem) ->
          match e with
          | EAbs abs when not (AbsId.Set.mem abs.abs_id ctx0_aids) -> Some abs
          | _ -> None)
        joined_ctx.env
    in
    let output_abs_ids = List.map (fun (abs : abs) -> abs.abs_id) output_abs in

    let fixed_aids = InterpJoinCore.compute_fixed_abs_ids ctx0 joined_ctx in
    let fixed_dids = Contexts.ctx_get_dummy_var_ids ctx0 in

    (* Match every context resulting from evaluating a branch (there should be
       one if no explicit panic was encountered, or 0 it we encountered a panic)
       with the joined context.

       Note that we make the match (and the whole join) recoverable.
    *)
    let match_ctx (ctx : eval_ctx) : SA.expr =
      (* Match the contexts with the joined context to determine the output of the branch *)
      let (_, ctx, output_values, output_abs), cf =
        InterpJoin.match_ctx_with_target config span WithCont fixed_aids
          fixed_dids output_abs_ids output_svalue_ids
          ~recoverable:!Config.recover_joins joined_ctx ctx
      in

      let reorder_output_abs (map : abs AbsId.Map.t) (absl : abs_id list) :
          abs list =
        List.map (fun id -> AbsId.Map.find id map) absl
      in
      let reorder_output_values (map : tvalue SymbolicValueId.Map.t)
          (values : symbolic_value_id list) : tvalue list =
        List.map (fun id -> SymbolicValueId.Map.find id map) values
      in
      let output_values =
        reorder_output_values output_values output_svalue_ids
      in
      let output_abs = reorder_output_abs output_abs output_abs_ids in

      (* Generate the let expression *)
      cf (SA.Join (ctx, output_values, output_abs))
    in
    let resl = List.map match_ctx ctxl in

    (* We can now call the continuation introduced when branching to group the
       expressions of the branches into a single branching expression (i.e.,
       we group the expressions for the [then] and [else] branches into a single
       [if then else] expression. *)
    let bound_expr = cf resl in

    (* Generate the let expression *)
    let cf (el : SA.expr list) : SA.expr =
      match el with
      | [ next_expr ] ->
          Let
            {
              bound_expr;
              out_svalues = output_svalues;
              out_abs = output_abs;
              next_expr;
              span;
            }
      | _ -> [%internal_error] span
    in

    (* Output the joined context *)
    ([ (joined_ctx, Unit) ], cf))

(** Evaluate a function call (auxiliary helper for [eval_statement]) *)
and eval_function_call (config : config) (span : Meta.span) (call : call) :
    stl_cm_fun =
  (* There are several cases:
     - this is a local function, in which case we execute its body
     - this is an builtin function, in which case there is a special treatment
     - this is a trait method
  *)
  match config.mode with
  | ConcreteMode -> eval_function_call_concrete config span call
  | SymbolicMode -> eval_function_call_symbolic config span call

and eval_function_call_concrete (config : config) (span : Meta.span)
    (call : call) : stl_cm_fun =
 fun ctx ->
  match call.func with
  | FnOpDynamic _ -> [%craise] span "Function pointers are not supported yet"
  | FnOpRegular func -> (
      match func.kind with
      | Fun fid ->
          let def = ctx_lookup_fun_decl span ctx fid in
          if def.item_meta.diagnostic_item = Some "box_new" then
            let ctx, cc =
              eval_box_new_concrete config span func.generics call ctx
            in
            ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ span cc)
          else eval_non_builtin_function_call_concrete config span fid call ctx
      | TraitMethod _ -> [%craise] span "Unimplemented")

and eval_function_call_symbolic (config : config) (span : Meta.span)
    (call : call) : stl_cm_fun =
 fun ctx ->
  match call.func with
  | FnOpDynamic _ -> [%craise] span "Function pointers are not supported yet"
  | FnOpRegular func ->
      [%ltrace
        "function call:\n- call: " ^ call_to_string ctx call ^ "\n- fn_ptr : "
        ^ fn_ptr_to_string ctx func];
      let call_info = eval_function_call_symbolic_inst span func ctx in
      [%ltrace
        "- call: " ^ call_to_string ctx call ^ "\n- call.generics:\n"
        ^ generic_args_to_string ctx call_info.call_generics
        ^ "\n- def.signature:\n"
        ^ fun_sig_to_string ctx call_info.call_sig];
      (* Evaluate the function call *)
      eval_function_call_symbolic_from_inst_sig config call_info call.args
        call.dest ctx

(** Evaluate a local (i.e., non-builtin) function call in concrete mode *)
and eval_non_builtin_function_call_concrete (config : config) (span : Meta.span)
    (fid : FunDeclId.id) (call : call) : stl_cm_fun =
 fun ctx ->
  let args = call.args in
  let dest = call.dest in
  match call.func with
  | FnOpDynamic _ -> [%craise] span "Function pointers are not supported yet"
  | FnOpRegular func ->
      let generics = func.generics in
      (* Sanity check: we don't fully handle the const generic vars environment
         in concrete mode yet *)
      [%sanity_check] span (generics.const_generics = []);
      (* Retrieve the (correctly instantiated) body *)
      let def = ctx_lookup_fun_decl span ctx fid in
      (* We can evaluate the function call only if it is not opaque *)
      let body =
        match def.body with
        | StructuredBody body -> body
        | other ->
            [%craise] span
              ("Can't evaluate a call to function: "
              ^ name_to_string ctx def.item_meta.name
              ^ ", it is "
              ^ Charon.GAst.show_body other)
      in
      (* TODO: we need to normalize the types if we want to correctly support traits *)
      [%cassert] body.span (generics.trait_refs = [])
        "Traits are not supported yet in concrete mode";
      let subst =
        [%add_loc] Subst.make_subst_from_generics (Some span) def.generics
          generics Self
      in
      let locals, body_st = Subst.expr_body_substitute subst body in

      (* Evaluate the input operands *)
      [%sanity_check] body.span (List.length args = body.locals.arg_count);
      let vl, ctx, cc = eval_operands config body.span args ctx in

      (* Push a frame delimiter - we use {!comp_transmit} to transmit the result
       * of the operands evaluation from above to the functions afterwards, while
       * ignoring it in this function *)
      let ctx = push_frame ctx in

      (* Compute the initial values for the local variables *)
      (* 1. Push the return value *)
      let ret_var, locals =
        match locals with
        | ret_ty :: locals -> (ret_ty, locals)
        | _ -> [%craise] span "Unreachable"
      in
      let input_locals, locals =
        Collections.List.split_at locals body.locals.arg_count
      in

      let ctx = push_var span ret_var (mk_bottom span ret_var.local_ty) ctx in

      (* 2. Push the input values *)
      let ctx =
        let inputs = List.combine input_locals vl in
        (* Note that this function checks that the variables and their values
         * have the same type (this is important) *)
        push_vars span inputs ctx
      in

      (* 3. Push the remaining local variables (initialized as {!Bottom}) *)
      let ctx = push_uninitialized_vars span locals ctx in

      (* Execute the function body *)
      let ctx_resl, cc = comp cc (eval_function_body config body_st ctx) in

      (* Pop the stack frame and move the return value to its destination *)
      let ctx_resl_cfl =
        List.map
          (fun (ctx, res) ->
            match res with
            | Panic -> ((ctx, Panic), fun e -> e)
            | Return ->
                (* Pop the stack frame, retrieve the return value, move it to
                   its destination and continue *)
                let ctx, cf = pop_frame_assign config span dest ctx in
                ((ctx, Unit), cf)
            | Break _ | Continue _ | Unit -> [%craise] span "Unreachable")
          ctx_resl
      in
      let ctx_resl, cfl = List.split ctx_resl_cfl in
      let cf_pop el = List.map2 (fun cf e -> cf e) cfl el in
      (* Continue *)
      (ctx_resl, cc_comp cc cf_pop)

(** Evaluate a function call in symbolic mode by using the function signature.

    This allows us to factorize the evaluation of local and non-local function
    calls in symbolic mode: only their signatures matter.

    The [call_info] contains the signature after instantiation together with the
    original call information used by the symbolic AST. *)
and eval_function_call_symbolic_from_inst_sig (config : config)
    (call_info : symbolic_fun_call_inst) (args : operand list) (dest : place) :
    stl_cm_fun =
 fun ctx ->
  let span = call_info.call_span in
  let fid = call_info.call_kind in
  let sg = call_info.call_sig.item_binder_value in
  let inst_sg = call_info.call_inst_sig in
  let generics = call_info.call_generics in
  (* Sanity check: same number of inputs *)
  [%sanity_check] span
    (List.length args = List.length call_info.call_sig.item_binder_value.inputs);
  (* Sanity check: the class of borrows present in the type is supported *)
  List.iter
    ([%add_loc] check_ty_is_supported span ctx)
    (call_info.call_inst_sig.output :: call_info.call_inst_sig.inputs);
  [%ltrace
    "- fid: "
    ^ fn_ptr_kind_to_string ctx fid
    ^ "\n- inst_sg:\n"
    ^ inst_fun_sig_to_string ctx inst_sg
    ^ "\n- call.generics:\n"
    ^ generic_args_to_string ctx generics
    ^ "\n- args:\n"
    ^ String.concat ", " (List.map (operand_to_string ctx) args)
    ^ "\n- dest:\n" ^ place_to_string ctx dest];

  (* Unique identifier for the call *)
  let call_id = ctx.fresh_fun_call_id () in

  (* Generate a fresh symbolic value for the return value *)
  let ret_sv_ty = inst_sg.output in
  let ret_spc = mk_fresh_symbolic_value span ctx ret_sv_ty in
  let ret_value = mk_tvalue_from_symbolic_value ret_spc in
  let args_places =
    List.map (fun p -> S.mk_opt_place_from_op span p ctx) args
  in
  let dest_place = Some (S.mk_mplace span dest ctx) in

  (* Evaluate the input operands *)
  let args, ctx, cc = eval_operands config span args ctx in

  [%ldebug
    "- args:\n"
    ^ Print.list_to_string ~sep:"\n"
        (fun (v : tvalue) ->
          "- " ^ tvalue_to_string ctx v ^ " : " ^ ty_to_string ctx v.ty)
        args];

  (* Generate the abstractions and insert them in the context *)
  let abs_ids = List.map (fun rg -> rg.id) inst_sg.abs_regions_hierarchy in
  let args_with_rtypes = List.combine args inst_sg.inputs in

  (* Check the type of the input arguments *)
  List.iteri
    (fun i ((arg, rty) : tvalue * rty) ->
      if not (Subst.erase_regions arg.ty = Subst.erase_regions rty) then (
        [%ltrace
          "Argument " ^ string_of_int i
          ^ " doesn't have the proper type:\n- arg: " ^ tvalue_to_string ctx arg
          ^ "\n- arg.ty: " ^ ty_to_string ctx arg.ty ^ "\n- target type: "
          ^ ty_to_string ctx rty];
        [%craise] span "The input arguments don't have the proper type"))
    args_with_rtypes;
  (* Check that the input arguments don't contain symbolic values that can't
   * be fed to functions (i.e., symbolic values output from function return
   * values and which contain borrows of borrows can't be used as function
   * inputs *)
  [%sanity_check] span
    (List.for_all
       (fun arg ->
         not
           (value_has_ret_symbolic_value_with_borrow_under_mut (Some span) ctx
              arg))
       args);

  (* Initialize the abstractions and push them in the context.
   * First, we define the function which, given an initialized, empty
   * abstraction, computes the avalues which should be inserted inside.
   *)
  let compute_abs_avalues (_rg_id : RegionGroupId.id) (abs : abs)
      (ctx : eval_ctx) : tavalue list * abs_cont option =
    (* Project over the input values *)
    let args_projs =
      List.map
        (fun (arg, arg_rty) ->
          apply_proj_borrows_on_input_value span ctx abs.regions.owned arg
            arg_rty)
        args_with_rtypes
    in
    (* Introduce the output value *)
    let ret_v =
      mk_aproj_loans_value_from_symbolic_value ctx.type_ctx.type_infos
        abs.regions.owned ret_spc ret_sv_ty
    in
    (* Compute the continuation used in the translation *)
    let cont : abs_cont =
      let outputs =
        List.map
          (fun (arg, arg_rty) ->
            apply_eproj_borrows_on_input_value span ctx abs.regions.owned arg
              arg_rty)
          args_with_rtypes
      in
      let output = mk_simpl_etuple ~borrow_proj:true outputs in
      let input =
        mk_eproj_loans_value_from_symbolic_value ctx.env ctx.type_ctx.type_infos
          abs.regions.owned ret_spc ret_sv_ty
      in
      let input = EApp (EFunCall abs.abs_id, [ [ input ] ]) in
      let input : tevalue = { value = input; ty = ret_sv_ty } in
      { output = Some output; input = Some input }
    in
    (* Group the input and output values *)
    (List.append args_projs [ ret_v ], Some cont)
  in
  (* Actually initialize and insert the abstractions *)
  let region_can_end _ = true in
  let ctx =
    create_push_abstractions_from_abs_region_groups
      (fun rg_id -> FunCall (call_id, rg_id))
      inst_sg.abs_regions_hierarchy region_can_end compute_abs_avalues ctx
  in
  register_heap_borrow_abs ctx fid inst_sg;
  (* Synthesize the symbolic AST *)
  let cc =
    cc_comp cc
      (S.synthesize_regular_function_call span fid call_id ctx sg inst_sg
         abs_ids generics args args_places ret_spc dest_place)
  in

  (* Move the return value to its destination *)
  let ctx, cc = comp cc (assign_to_place config span ret_value dest ctx) in

  (* End the abstractions which don't contain loans and don't have parent
   * abstractions.
   * We do the general, nested borrows case here: we end abstractions, then
   * retry (because then we might end their children abstractions)
   *)
  let abs_ids = ref abs_ids in
  let rec end_abs_with_no_loans ctx =
    (* Find the abstractions which don't contain loans *)
    let no_loans_abs, with_loans_abs =
      List.partition
        (fun abs_id ->
          (* Lookup the abstraction *)
          let abs = ctx_lookup_abs ctx abs_id in
          (* Check if it has parents *)
          AbsId.Set.is_empty abs.parents
          (* Check if it contains non-ignored loans *)
          && Option.is_none
               (InterpBorrowsCore.get_first_non_ignored_aloan_in_abs span abs 0
                  (-1))
          (* Check that we are allowed to end it (this is not the case for
             instance if it owns the static region and still contains
             borrows: see [abs_is_endable]) *)
          && abs_is_endable ctx abs)
        !abs_ids
    in
    (* Check if there are abstractions to end *)
    if no_loans_abs <> [] then (
      (* Update the reference to the list of asbtraction ids, for the recursive calls *)
      abs_ids := with_loans_abs;
      (* End the abstractions which can be ended *)
      let no_loans_abs =
        AbsIdWithLevelSet.of_list
          (List.map (fun abs_id -> { abs_id; level = 0 }) no_loans_abs)
      in
      let ctx, cc = InterpBorrows.end_abs_set config span no_loans_abs ctx in
      (* Recursive call *)
      comp cc (end_abs_with_no_loans ctx))
    else (* No abstractions to end: continue *)
      (ctx, fun e -> e)
  in
  (* Try to end the abstractions with no loans if:
   * - the option is enabled
   * - the function returns unit
   * (see the documentation of {!config} for more information)
   *)
  let ctx, cc =
    comp cc
      (if Config.return_unit_end_abs_with_no_loans && ty_is_unit inst_sg.output
       then end_abs_with_no_loans ctx
       else (ctx, fun e -> e))
  in

  (* Continue - note that we do as if the function call has been successful,
   * by giving {!Unit} to the continuation, because we place us in the case
   * where we haven't panicked. Of course, the translation needs to take the
   * panic case into account... *)
  ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ span cc)

(** Evaluate a statement seen as a function body *)
and eval_function_body (config : config) (body : block) : stl_cm_fun =
 fun ctx ->
  [%ltrace ""];
  let ctx_resl, cf_body = eval_block config body ctx in
  let ctx_res_cfl =
    List.map
      (fun (ctx, res) ->
        (* Note that we *don't* check the result ({!Panic}, {!Return}, etc.): we
           delegate the check to the caller. *)
        [%ltrace "cf_finish:\n" ^ eval_ctx_to_string ctx];
        (* Expand the symbolic values if necessary - we need to do that before
           checking the invariants *)
        let ctx, cf = greedy_expand_symbolic_values body.span ctx in
        [%ltrace "after expansion:\n" ^ eval_ctx_to_string ctx];
        (* Sanity check *)
        Invariants.check_invariants body.span ctx;
        (* Continue *)
        ((ctx, res), cf))
      ctx_resl
  in
  let ctx_resl, cfl = List.split ctx_res_cfl in
  let cf_end el = List.map2 (fun cf e -> cf e) cfl el in
  (* Compose and continue *)
  (ctx_resl, cc_comp cf_body cf_end)
