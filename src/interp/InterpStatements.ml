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

(** Push an uninitialized variable to the environment *)
let push_uninitialized_var (span : Meta.span) (var : local) (ctx : eval_ctx) :
    eval_ctx =
  ctx_push_uninitialized_var span ctx var

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
    ^ "\n- p: " ^ place_to_string ctx p ^ "\n- Initial context:\n"
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
  [%sanity_check] span (v.ty = TLiteral TBool);
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
        [%sanity_check] span (sv.sv_ty = TLiteral TBool);
        (* We continue the execution as if the test had succeeded, and thus
         * perform the symbolic expansion: sv ~~> true.
         * We will of course synthesize an assertion in the generated code
         * (see below). *)
        let ctx =
          apply_symbolic_expansion_non_borrow span sv ctx
            (SeLiteral (VBool true))
        in
        (* Add the synthesized assertion *)
        ((ctx, Unit), S.synthesize_assertion ctx v)
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
  | TAdt { id = TAdtId _ as type_id; generics }, VAdt av -> (
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
              match type_id with
              | TAdtId def_id ->
                  compute_expanded_bottom_adt_value span ctx def_id
                    (Some variant_id) generics
              | _ -> [%craise] span "Unreachable"
            in
            let ctx, cc =
              comp cc (assign_to_place config span bottom_v p ctx)
            in
            ((ctx, Unit), cc))
  | TAdt { id = TAdtId _ as type_id; generics }, VBottom ->
      let bottom_v =
        match type_id with
        | TAdtId def_id ->
            compute_expanded_bottom_adt_value span ctx def_id (Some variant_id)
              generics
        | _ -> [%craise] span "Unreachable"
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

(** Small helper: compute the type of the return value for a specific
    instantiation of an builtin function. *)
let get_builtin_function_return_type (span : Meta.span) (fid : builtin_fun_id)
    (generics : generic_args) : ety =
  [%sanity_check] span (generics.trait_refs = []);
  (* Retrieve the function's signature *)
  let sg = Builtin.get_builtin_fun_sig fid in
  (* Instantiate the return type  *)
  let generics = Subst.generic_args_erase_regions generics in
  let subst = Subst.make_subst_from_generics sg.generics generics in
  Subst.erase_regions_substitute_types subst sg.output

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

let pop_frame (config : config) (span : Meta.span) (pop_return_value : bool)
    (ctx : eval_ctx) :
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
    (* Drop the loans *)
    let locals = List.rev locals in
    fold_left_apply_continuation
      (fun lid ctx ->
        drop_outer_loans_at_lplace config span
          (mk_place_from_var_id ctx span lid)
          ctx)
      locals ctx
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
  let v, ctx, cc = pop_frame config span true ctx in
  comp cc (assign_to_place config span (Option.get v) dest ctx)

(** Auxiliary function - see {!eval_builtin_function_call} *)
let eval_box_new_concrete (config : config) (span : Meta.span)
    (generics : generic_args) : cm_fun =
 fun ctx ->
  (* Check and retrieve the arguments *)
  match
    (generics.regions, generics.types, generics.const_generics, ctx.env)
  with
  | ( [],
      [ boxed_ty ],
      [],
      EBinding (BVar input_var, input_value)
      :: EBinding (_ret_var, _)
      :: EFrame :: _ ) ->
      (* Required type checking *)
      [%cassert] span
        (input_value.ty = boxed_ty)
        "The input given to Box::new doesn't have the proper type";

      (* Move the input value *)
      let v, ctx, cc =
        eval_operand config span
          (Move (mk_place_from_var_id ctx span input_var.index))
          ctx
      in

      (* Create the new box *)
      (* Create the box value *)
      let generics = TypesUtils.mk_generic_args_from_types [ boxed_ty ] in
      let box_ty = TAdt { id = TBuiltin TBox; generics } in
      let box_v = VAdt { variant_id = None; fields = [ v ] } in
      let box_v = mk_tvalue span box_ty box_v in

      (* Move this value to the return variable *)
      let dest = mk_place_from_var_id ctx span LocalId.zero in
      comp cc (assign_to_place config span box_v dest ctx)
  | _ -> [%craise] span "Inconsistent state"

(** Evaluate a non-local function call in concrete mode *)
let eval_builtin_function_call_concrete (config : config) (span : Meta.span)
    (fid : builtin_fun_id) (call : call) : cm_fun =
 fun ctx ->
  let args = call.args in
  let dest = call.dest in
  match call.func with
  | FnOpMove _ ->
      (* Closure case: TODO *)
      [%craise] span "Closures are not supported yet"
  | FnOpRegular func ->
      let generics = func.generics in
      (* Sanity check: we don't fully handle the const generic vars environment
         in concrete mode yet *)
      [%sanity_check] span (generics.const_generics = []);

      (* Evaluate the operands *)
      (*      let ctx, args_vl = eval_operands config ctx args in *)
      let args_vl, ctx, cc = eval_operands config span args ctx in

      (* Evaluate the call
       *
       * Style note: at some point we used {!comp_transmit} to
       * transmit the result of {!eval_operands} above down to {!push_vars}
       * below, without having to introduce an intermediary function call,
       * but it made it less clear where the computed values came from,
       * so we reversed the modifications. *)
      (* Push the stack frame: we initialize the frame with the return variable,
         and one variable per input argument *)
      let ctx = push_frame ctx in

      (* Create and push the return variable *)
      let ret_vid = LocalId.zero in
      let ret_ty = get_builtin_function_return_type span fid generics in
      let ret_var = mk_var ret_vid (Some "@return") ret_ty in
      let ctx = push_uninitialized_var span ret_var ctx in

      (* Create and push the input variables *)
      let input_vars =
        LocalId.mapi_from1
          (fun id (v : tvalue) -> (mk_var id None v.ty, v))
          args_vl
      in
      let ctx = push_vars span input_vars ctx in

      (* "Execute" the function body. As the functions are builtin, here we call
       * custom functions to perform the proper manipulations: we don't have
       * access to a body. *)
      let ctx, cf_eval_body =
        match fid with
        | BoxNew -> eval_box_new_concrete config span generics ctx
        | Index _
        | ArrayToSliceShared
        | ArrayToSliceMut
        | ArrayRepeat
        | PtrFromParts _ -> [%craise] span "Unimplemented"
      in
      let cc = cc_comp cc cf_eval_body in

      (* Pop the frame *)
      comp cc (pop_frame_assign config span dest ctx)

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
  let abs_to_ancestors_regions : RegionId.Set.t AbsId.Map.t ref =
    ref AbsId.Map.empty
  in
  (* Auxiliary function to create one abstraction *)
  let create_abs (rg_id : RegionGroupId.id) (rg : abs_region_group) : abs =
    let abs_id = rg.id in
    let original_parents = rg.parents in
    let parents =
      List.fold_left
        (fun s pid -> AbsId.Set.add pid s)
        AbsId.Set.empty rg.parents
    in
    let regions =
      let owned = RegionId.Set.of_list rg.regions in
      { owned }
    in
    let ancestors_regions_union_current_regions =
      RegionId.Set.union regions.owned regions.owned
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
      original_parents;
      regions;
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

(** Auxiliary helper for [eval_non_builtin_function_call_symbolic] Instantiate
    the signature and introduce fresh abstractions and region ids while doing
    so.

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
let eval_non_builtin_function_call_symbolic_inst (span : Meta.span)
    (call : call) (ctx : eval_ctx) :
    fn_ptr_kind * generic_args * fun_decl * inst_fun_sig =
  match call.func with
  | FnOpMove _ ->
      (* Closure case: TODO *)
      [%craise] span "Closures are not supported yet"
  | FnOpRegular func ->
      let fid, generics, tr_self =
        match func.kind with
        | FunId (FRegular fid) ->
            [%ltrace "Regular function"];
            let tr_self = UnknownTrait __FUNCTION__ in
            (fid, func.generics, tr_self)
        | FunId (FBuiltin _) ->
            (* Unreachable: must be a transparent function *)
            [%craise] span "Unreachable"
        | TraitMethod (trait_ref, method_name, _) ->
            [%ltrace
              "trait method call:\n- call: " ^ call_to_string ctx call
              ^ "\n- method name: " ^ method_name ^ "\n- call.generics:\n"
              ^ generic_args_to_string ctx func.generics
              ^ "\n- trait_ref.trait_decl_ref: "
              ^ trait_decl_ref_region_binder_to_string ctx
                  trait_ref.trait_decl_ref];
            (* Check that there are no bound regions *)
            [%cassert] span
              (trait_ref.trait_decl_ref.binder_regions = [])
              "Unexpected bound regions";
            let trait_decl_ref = trait_ref.trait_decl_ref.binder_value in
            (* This should be a call to a trait clause method (if it were a method
               coming from an impl, there should be no indirection through the trait
               reference itself (Charon should have simplified this). *)
            [%sanity_check] span
              (match trait_ref.kind with
              | TraitImpl _ -> false
              | _ -> true);
            (* Lookup the trait decl and substitution *)
            let trait_decl = ctx_lookup_trait_decl span ctx trait_decl_ref.id in
            let fn_ref =
              Option.get
                (Substitute.lookup_and_subst_trait_decl_method trait_decl
                   method_name trait_ref func.generics)
            in
            (* *)
            let tr_self = trait_ref.kind in
            (fn_ref.id, fn_ref.generics, tr_self)
      in
      (* Lookup the declaration *)
      let def = ctx_lookup_fun_decl span ctx fid in
      [%ltrace
        "- call: " ^ call_to_string ctx call ^ "\n- call.generics:\n"
        ^ generic_args_to_string ctx func.generics
        ^ "\n- def.signature:\n"
        ^ fun_sig_to_string ctx def.signature];
      (* Instantiate *)
      let regions_hierarchy =
        [%silent_unwrap] span
          (LlbcAstUtils.FunIdMap.find_opt (FRegular fid)
             ctx.fun_ctx.regions_hierarchies)
      in
      let inst_sg =
        instantiate_fun_sig span ctx generics tr_self def.signature
          regions_hierarchy
      in
      (func.kind, func.generics, def, inst_sg)

(** Helper: introduce a fresh symbolic value for a global *)
let eval_global_as_fresh_symbolic_value (span : Meta.span)
    (gref : global_decl_ref) (ctx : eval_ctx) : symbolic_value =
  let generics = gref.generics in
  let global = ctx_lookup_global_decl span ctx gref.id in
  [%cassert] span (ty_no_regions global.ty)
    "Const globals should not contain regions";
  (* Instantiate the type  *)
  let generics = Subst.generic_args_erase_regions generics in
  let subst = Subst.make_subst_from_generics global.generics generics in
  let ty = Subst.erase_regions_substitute_types subst global.ty in
  mk_fresh_symbolic_value span ctx ty

(** Evaluate a statement. *)
let rec eval_statement (config : config) (st : statement) : stl_cm_fun =
 fun ctx ->
  (* Debugging *)
  [%ltrace
    "\n**About to evaluate statement**: [\n"
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

  (* Evaluate the statement *)
  comp cc (eval_statement_raw config st ctx)

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
  eval_statement_list config b.span b.statements

and eval_statement_raw (config : config) (st : statement) : stl_cm_fun =
 fun ctx ->
  [%ltrace "statement:\n" ^ statement_to_string_with_tab ctx st ^ "\n"];
  match st.kind with
  | Assign (p, rvalue) ->
      if
        (* We handle global assignments separately as a specific case. *)
        ExpressionsUtils.rvalue_accesses_global rvalue
      then eval_rvalue_global config st.span p rvalue ctx
      else
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
                | ShallowInitBox _ ->
                    [%craise] st.span
                      "ShallowInitBox should have been removed in a micropass"
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
        ([ (ctx, res) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | SetDiscriminant (p, variant_id) ->
      let (ctx, res), cc = set_discriminant config st.span p variant_id ctx in
      ([ (ctx, res) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | Deinit p ->
      let ctx, cc = drop_value config st.span p ctx in
      ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | Assert assertion ->
      let (ctx, res), cc = eval_assertion config st.span assertion ctx in
      ([ (ctx, res) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | Call call -> eval_function_call config st.span call ctx
  | Abort _ ->
      (* Evaluate to a panic only if the execution is concrete, otherwise we stop
         evaluating there and synthesize a [panic] node in the symbolic AST. *)
      if config.mode = ConcreteMode then
        ([ (ctx, Panic) ], cf_singleton __FILE__ __LINE__ st.span)
      else ([], cf_empty __FILE__ __LINE__ st.span SA.Panic)
  | Return -> ([ (ctx, Return) ], cf_singleton __FILE__ __LINE__ st.span)
  | Break i -> ([ (ctx, Break i) ], cf_singleton __FILE__ __LINE__ st.span)
  | Continue i -> ([ (ctx, Continue i) ], cf_singleton __FILE__ __LINE__ st.span)
  | StorageLive _ | Nop ->
      ([ (ctx, Unit) ], cf_singleton __FILE__ __LINE__ st.span)
  | CopyNonOverlapping _ ->
      [%craise] st.span "CopyNonOverlapping is not supported yet"
  | Loop loop_body ->
      let eval_loop_body = eval_block config loop_body in
      InterpLoops.eval_loop config st.span eval_loop_body ctx
  | Switch switch -> eval_switch config st.span switch ctx
  | Drop _ | StorageDead _ ->
      [%craise] st.span "StorageDead/Drop should have been removed in a prepass"
  | Error s -> [%craise] st.span s

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
       * We then create a reference to the global.
       *)
      let sval = eval_global_as_fresh_symbolic_value span gref ctx in
      let typed_sval = mk_tvalue_from_symbolic_value sval in
      (* Create a shared loan containing the global, as well as a shared borrow *)
      let bid = ctx.fresh_borrow_id () in
      let sid = ctx.fresh_shared_borrow_id () in
      let loan : tvalue =
        { value = VLoan (VSharedLoan (bid, typed_sval)); ty = sval.sv_ty }
      in
      let borrow : tvalue =
        {
          value = VBorrow (VSharedBorrow (bid, sid));
          ty = TRef (RErased, sval.sv_ty, RShared);
        }
      in
      (* We need to push the shared loan in a dummy variable *)
      let dummy_id = ctx.fresh_dummy_var_id () in
      let ctx = ctx_push_dummy_var ctx dummy_id loan in
      (* Assign the borrow to its destination *)
      let ctx, cc = assign_to_place config span borrow dest ctx in
      ( [ (ctx, Unit) ],
        cc_singleton __FILE__ __LINE__ span
          (cc_comp (S.synthesize_global_eval gref sval) cc) )

(** Evaluate a switch *)
and eval_switch (config : config) (span : Meta.span) (switch : switch) :
    stl_cm_fun =
 fun ctx ->
  let ctx, cc = eval_switch_prepare config span switch ctx in
  comp cc (eval_switch_raw config span switch ctx)

(** Prepare the context before evaluating a switch.

    TODO: generalize the join so that we don't have to do so. The problem is
    that we may symbolically expand some shared values which are in frozen
    region abstractions (and which we thus want to remain the same in the left
    and right branches). *)
and eval_switch_prepare (_config : config) (span : Meta.span) (_switch : switch)
    : cm_fun =
 fun ctx -> InterpJoin.prepare_ashared_loans span None ~with_abs_conts:true ctx

and eval_switch_raw (config : config) (span : Meta.span) (switch : switch) :
    stl_cm_fun =
 fun ctx ->
  (* We evaluate the scrutinee in two steps:
     first we prepare it, then we check if its value is concrete or
     symbolic. If it is concrete, we can then evaluate the operand
     directly, otherwise we must first expand the value.
     Note that we can't fully evaluate the operand *then* expand the
     value if it is symbolic, because the value may have been moved
     (and would thus floating in thin air...)! *)
  (* Match on the targets *)
  match (switch : LlbcAst.switch) with
  | If (op, true_block, false_block) ->
      (* Evaluate the operand *)
      let op_v, ctx, cf_eval_op = eval_operand config span op ctx in
      let ctx0 = ctx in
      (* Switch on the value *)
      let ctx_resl, cf_if =
        match op_v.value with
        | VLiteral (VBool b) ->
            (* Branch *)
            if b then eval_block config true_block ctx
            else eval_block config false_block ctx
        | VSymbolic sv ->
            (* Expand the symbolic boolean, and continue by evaluating
               the branches *)
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
            if join then eval_switch_with_join config span cc ctx0 ctx_resl
            else (ctx_resl, cc)
        | _ -> [%craise] span "Inconsistent state"
      in
      (* Compose *)
      (ctx_resl, cc_comp cf_eval_op cf_if)
  | SwitchInt (op, (int_ty : literal_type), stgts, otherwise) ->
      (* Evaluate the operand *)
      let op_v, ctx, cf_eval_op = eval_operand config span op ctx in
      let ctx0 = ctx in
      (* Switch on the value *)
      let ctx_resl, cf_switch =
        match (op_v.value, int_ty) with
        | VLiteral (VScalar sv), (TInt _ | TUInt _) -> (
            (* Sanity check *)
            [%sanity_check] span (Scalars.get_ty sv = literal_as_integer int_ty);
            (* Find the branch *)
            match
              List.find_opt (fun (svl, _) -> List.mem (VScalar sv) svl) stgts
            with
            | None -> eval_block config otherwise ctx
            | Some (_, tgt) -> eval_block config tgt ctx)
        | VSymbolic sv, _ ->
            (* Several branches may be grouped together: every branch is described
               by a pair (list of values, branch expression).
               In order to do a symbolic evaluation, we make this "flat" by
               de-grouping the branches. *)
            let values, branches =
              List.split
                (List.concat
                   (List.map
                      (fun (vl, st) -> List.map (fun v -> (v, st)) vl)
                      stgts))
            in
            (* Expand the symbolic value *)
            let (ctx_branches, ctx_otherwise), cf_int =
              expand_symbolic_int span sv
                (S.mk_opt_place_from_op span op ctx)
                (literal_as_integer int_ty)
                (List.map literal_as_scalar values)
                ctx
            in
            (* Evaluate the branches: first the "regular" branches *)
            let resl_branches =
              List.map
                (fun (ctx, branch) -> eval_block config branch ctx)
                (List.combine ctx_branches branches)
            in
            (* Then evaluate the "otherwise" branch *)
            let resl_otherwise = eval_block config otherwise ctx_otherwise in

            (* Should we join the contexts after the switch? *)
            let join =
              (not (List.exists block_has_break_continue_return branches))
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
              eval_switch_with_join config span cf ctx0 resl
            else
              (* Do not join the contexts: compose the continuations and continue *)
              (resl, cf)
        | _ -> [%craise] span "Inconsistent state"
      in
      (* Compose *)
      (ctx_resl, cc_comp cf_eval_op cf_switch)
  | Match (p, stgts, otherwise) ->
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
        | VAdt adt -> (
            (* Evaluate the discriminant *)
            let dv = Option.get adt.variant_id in
            (* Find the branch, evaluate and continue *)
            match List.find_opt (fun (svl, _) -> List.mem dv svl) stgts with
            | None -> (
                match otherwise with
                | None -> [%craise] span "No otherwise branch"
                | Some otherwise -> eval_block config otherwise ctx)
            | Some (_, tgt) -> eval_block config tgt ctx)
        | VSymbolic sv ->
            (* Expand the symbolic value - may lead to branching *)
            let ctxl, cf_expand =
              expand_symbolic_adt span sv (Some (S.mk_mplace span p ctx)) ctx
            in
            (* Re-evaluate the switch - the value is not symbolic anymore,
               which means we will go to the other branch *)
            let resl =
              List.map (fun ctx -> (eval_switch config span switch) ctx) ctxl
            in
            (* Should we join the contexts after the match? *)
            let join =
              (not
                 (List.exists
                    (fun (_, b) -> block_has_break_continue_return b)
                    stgts))
              &&
              match otherwise with
              | None -> true
              | Some block -> not (block_has_break_continue_return block)
            in
            let ctx_resl, cf = comp_seqs __FILE__ __LINE__ span resl in
            let cc = cc_comp cf_expand cf in
            if join then (* Join the contexts *)
              eval_switch_with_join config span cc ctx0 ctx_resl
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
    let _, joined_ctx =
      InterpJoin.join_ctxs_list config span ~with_abs_conts:true Join
        ctx_to_join
    in
    [%ldebug "Joined ctx:\n" ^ eval_ctx_to_string joined_ctx];
    let ctx0_aids = env_get_abs_ids ctx0.env in
    [%ldebug "ctx0_aids:\n" ^ AbsId.Set.to_string None ctx0_aids];

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
       with the joined context. *)
    let match_ctx (ctx : eval_ctx) : SA.expr =
      (* Match the contexts with the joined context to determine the output of the branch *)
      let (_, ctx, output_values, output_abs), cf =
        InterpJoin.match_ctx_with_target config span WithCont fixed_aids
          fixed_dids output_abs_ids output_svalue_ids joined_ctx ctx
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
  | FnOpMove _ -> [%craise] span "Closures are not supported yet"
  | FnOpRegular func -> (
      match func.kind with
      | FunId (FRegular fid) ->
          eval_non_builtin_function_call_concrete config span fid call ctx
      | FunId (FBuiltin fid) ->
          (* Continue - note that we do as if the function call has been successful,
           * by giving {!Unit} to the continuation, because we place us in the case
           * where we haven't panicked. Of course, the translation needs to take the
           * panic case into account... *)
          let ctx, cc =
            eval_builtin_function_call_concrete config span fid call ctx
          in
          ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ span cc)
      | TraitMethod _ -> [%craise] span "Unimplemented")

and eval_function_call_symbolic (config : config) (span : Meta.span)
    (call : call) : stl_cm_fun =
  match call.func with
  | FnOpMove _ -> [%craise] span "Closures are not supported yet"
  | FnOpRegular func -> (
      match func.kind with
      | FunId (FRegular _) | TraitMethod _ ->
          eval_non_builtin_function_call_symbolic config span call
      | FunId (FBuiltin fid) ->
          eval_builtin_function_call_symbolic config span fid func call.args
            call.dest)

(** Evaluate a local (i.e., non-builtin) function call in concrete mode *)
and eval_non_builtin_function_call_concrete (config : config) (span : Meta.span)
    (fid : FunDeclId.id) (call : call) : stl_cm_fun =
 fun ctx ->
  let args = call.args in
  let dest = call.dest in
  match call.func with
  | FnOpMove _ -> [%craise] span "Closures are not supported yet"
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
        | None ->
            [%craise] span
              ("Can't evaluate a call to an opaque function: "
              ^ name_to_string ctx def.item_meta.name)
        | Some body -> body
      in
      (* TODO: we need to normalize the types if we want to correctly support traits *)
      [%cassert] body.span (generics.trait_refs = [])
        "Traits are not supported yet in concrete mode";
      let subst =
        Subst.make_subst_from_generics def.signature.generics generics
      in
      let locals, body_st = Subst.fun_body_substitute_in_body subst body in

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

(** Evaluate a local (i.e., non-builtin) function call in symbolic mode *)
and eval_non_builtin_function_call_symbolic (config : config) (span : Meta.span)
    (call : call) : stl_cm_fun =
 fun ctx ->
  let func, generics, def, inst_sg =
    eval_non_builtin_function_call_symbolic_inst span call ctx
  in
  (* Sanity check: same number of inputs *)
  [%sanity_check] span (List.length call.args = List.length def.signature.inputs);
  (* Sanity check: no nested borrows, borrows in ADTs, etc. *)
  [%cassert] span
    (List.for_all
       (fun ty ->
         not (ty_has_nested_borrows (Some span) ctx.type_ctx.type_infos ty))
       (inst_sg.output :: inst_sg.inputs))
    "Nested borrows are not supported yet";
  (* Evaluate the function call *)
  eval_function_call_symbolic_from_inst_sig config def.item_meta.span func
    def.signature inst_sg generics call.args call.dest ctx

(** Evaluate a function call in symbolic mode by using the function signature.

    This allows us to factorize the evaluation of local and non-local function
    calls in symbolic mode: only their signatures matter.

    The [self_trait_ref] trait ref refers to [Self]. We use it when calling a
    provided trait method, because those methods have a special treatment: we
    dot not group them with the required trait methods, and forbid (for now)
    overriding them. We treat them as regular method, which take an additional
    trait ref as input. *)
and eval_function_call_symbolic_from_inst_sig (config : config)
    (span : Meta.span) (fid : fn_ptr_kind) (sg : fun_sig)
    (inst_sg : inst_fun_sig) (generics : generic_args) (args : operand list)
    (dest : place) : stl_cm_fun =
 fun ctx ->
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

  (* Generate the abstractions and insert them in the context *)
  let abs_ids = List.map (fun rg -> rg.id) inst_sg.abs_regions_hierarchy in
  let args_with_rtypes = List.combine args inst_sg.inputs in

  (* Check the type of the input arguments *)
  [%cassert] span
    (List.for_all
       (fun ((arg, rty) : tvalue * rty) -> arg.ty = Subst.erase_regions rty)
       args_with_rtypes)
    "The input arguments don't have the proper type";
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
      mk_aproj_loans_value_from_symbolic_value abs.regions.owned ret_spc
        ret_sv_ty
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
      let output = mk_simpl_etuple outputs in
      let input =
        mk_eproj_loans_value_from_symbolic_value ctx.type_ctx.type_infos
          abs.regions.owned ret_spc ret_sv_ty
      in
      let input = EApp (EFunCall abs.abs_id, [ input ]) in
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
               (InterpBorrowsCore.get_first_non_ignored_aloan_in_abstraction
                  span abs))
        !abs_ids
    in
    (* Check if there are abstractions to end *)
    if no_loans_abs <> [] then (
      (* Update the reference to the list of asbtraction ids, for the recursive calls *)
      abs_ids := with_loans_abs;
      (* End the abstractions which can be ended *)
      let no_loans_abs = AbsId.Set.of_list no_loans_abs in
      let ctx, cc =
        InterpBorrows.end_abstractions config span no_loans_abs ctx
      in
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

(** Evaluate a non-local function call in symbolic mode *)
and eval_builtin_function_call_symbolic (config : config) (span : Meta.span)
    (fid : builtin_fun_id) (func : fn_ptr) (args : operand list) (dest : place)
    : stl_cm_fun =
 fun ctx ->
  (* In symbolic mode, the behavior of a function call is completely defined
     by the signature of the function: we thus simply generate correctly
     instantiated signatures, and delegate the work to an auxiliary function *)
  let sg = Builtin.get_builtin_fun_sig fid in
  if fid = BoxNew then begin
    (* Special case: Box::new: we allow instantiating the type parameters with
       types containing borrows.

       TODO: this is a hack.
    *)
    (* Sanity check: check that we are not using nested borrows *)
    [%classert] span
      (List.for_all
         (fun ty ->
           not (ty_has_nested_borrows (Some span) ctx.type_ctx.type_infos ty))
         func.generics.types)
      (lazy
        ("Instantiating [Box::new] with nested borrows is not allowed for now ("
       ^ fn_ptr_to_string ctx func ^ ")"));

    (* As we allow instantiating type parameters with types containing regions,
       we have to recompute the regions hierarchy. *)
    let fun_name = Print.Types.builtin_fun_id_to_string fid in
    let inst_sig =
      compute_regions_hierarchy_for_fun_call ctx.fresh_abs_id (Some span)
        ctx.crate fun_name ctx.type_vars ctx.const_generic_vars func.generics sg
    in
    [%ltrace
      "special case:" ^ "\n- inst_sig:" ^ inst_fun_sig_to_string ctx inst_sig];

    (* Evaluate the function call *)
    eval_function_call_symbolic_from_inst_sig config span (FunId (FBuiltin fid))
      sg inst_sig func.generics args dest ctx
  end
  else begin
    (* Sanity check: make sure the type parameters don't contain regions -
       this is a current limitation of our synthesis.
    *)
    [%classert] span
      (List.for_all
         (fun ty -> not (ty_has_borrows (Some span) ctx.type_ctx.type_infos ty))
         func.generics.types)
      (lazy
        ("Instantiating the type parameters of a function with types \
          containing borrows is not allowed for now ("
       ^ fn_ptr_to_string ctx func ^ ")"));
    let regions_hierarchy =
      LlbcAstUtils.FunIdMap.find (FBuiltin fid) ctx.fun_ctx.regions_hierarchies
    in

    (* There shouldn't be any reference to Self *)
    let tr_self = UnknownTrait __FUNCTION__ in
    let inst_sig =
      instantiate_fun_sig span ctx func.generics tr_self sg regions_hierarchy
    in

    (* Evaluate the function call *)
    eval_function_call_symbolic_from_inst_sig config span (FunId (FBuiltin fid))
      sg inst_sig func.generics args dest ctx
  end

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
