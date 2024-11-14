open Types
open TypesUtils
open Values
open ValuesUtils
open Expressions
open Contexts
open LlbcAst
open Cps
open InterpreterUtils
open InterpreterProjectors
open InterpreterExpansion
open InterpreterPaths
open InterpreterExpressions
open Errors
module Subst = Substitute
module S = SynthesizeSymbolic

(** The local logger *)
let log = L.statements_log

(** Drop a value at a given place - TODO: factorize this with [assign_to_place] *)
let drop_value (config : config) (span : Meta.span) (p : place) : cm_fun =
 fun ctx ->
  log#ldebug
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
    let mv = InterpreterPaths.read_place span access p ctx in
    let dummy_id = fresh_dummy_var_id () in
    let ctx = ctx_push_dummy_var ctx dummy_id mv in
    (* Update the destination to ⊥ *)
    let nv = { v with value = VBottom } in
    let ctx = write_place span access p nv ctx in
    log#ldebug
      (lazy
        ("drop_value: place: " ^ place_to_string ctx p ^ "\n- Final context:\n"
        ^ eval_ctx_to_string ~span:(Some span) ctx));
    ctx
  in
  (* Compose and apply *)
  (ctx, cc)

(** Push a dummy variable to the environment *)
let push_dummy_var (vid : DummyVarId.id) (v : typed_value) (ctx : eval_ctx) :
    eval_ctx =
  ctx_push_dummy_var ctx vid v

(** Remove a dummy variable from the environment *)
let remove_dummy_var (span : Meta.span) (vid : DummyVarId.id) (ctx : eval_ctx) :
    typed_value * eval_ctx =
  let ctx, v = ctx_remove_dummy_var span ctx vid in
  (v, ctx)

(** Push an uninitialized variable to the environment *)
let push_uninitialized_var (span : Meta.span) (var : var) (ctx : eval_ctx) :
    eval_ctx =
  ctx_push_uninitialized_var span ctx var

(** Push a list of uninitialized variables to the environment *)
let push_uninitialized_vars (span : Meta.span) (vars : var list)
    (ctx : eval_ctx) : eval_ctx =
  ctx_push_uninitialized_vars span ctx vars

(** Push a variable to the environment *)
let push_var (span : Meta.span) (var : var) (v : typed_value) (ctx : eval_ctx) :
    eval_ctx =
  ctx_push_var span ctx var v

(** Push a list of variables to the environment *)
let push_vars (span : Meta.span) (vars : (var * typed_value) list)
    (ctx : eval_ctx) : eval_ctx =
  ctx_push_vars span ctx vars

(** Assign a value to a given place.

    Note that this function first pushes the value to assign in a dummy variable,
    then prepares the destination (by ending borrows, etc.) before popping the
    dummy variable and putting in its destination (after having checked that
    preparing the destination didn't introduce ⊥).
 *)
let assign_to_place (config : config) (span : Meta.span) (rv : typed_value)
    (p : place) : cm_fun =
 fun ctx ->
  log#ldebug
    (lazy
      ("assign_to_place:" ^ "\n- rv: "
      ^ typed_value_to_string ~span:(Some span) ctx rv
      ^ "\n- p: " ^ place_to_string ctx p ^ "\n- Initial context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx));
  (* Push the rvalue to a dummy variable, for bookkeeping *)
  let rvalue_vid = fresh_dummy_var_id () in
  let ctx = push_dummy_var rvalue_vid rv ctx in
  (* Prepare the destination *)
  let _, ctx, cc = prepare_lplace config span p ctx in
  (* Retrieve the rvalue from the dummy variable *)
  let rv, ctx = remove_dummy_var span rvalue_vid ctx in
  (* Move the value at destination (that we will overwrite) to a dummy variable
     to preserve the borrows *)
  let mv = InterpreterPaths.read_place span Write p ctx in
  let dest_vid = fresh_dummy_var_id () in
  let ctx = ctx_push_dummy_var ctx dest_vid mv in
  (* Write to the destination *)
  (* Checks - maybe the bookkeeping updated the rvalue and introduced bottoms *)
  exec_assert __FILE__ __LINE__
    (not (bottom_in_value ctx.ended_regions rv))
    span "The value to move contains bottom";
  (* Update the destination *)
  let ctx = write_place span Write p rv ctx in
  (* Debug *)
  log#ldebug
    (lazy
      ("assign_to_place:" ^ "\n- rv: "
      ^ typed_value_to_string ~span:(Some span) ctx rv
      ^ "\n- p: " ^ place_to_string ctx p ^ "\n- Final context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx));
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
        craise __FILE__ __LINE__ span
          ("Expected a boolean, got: "
          ^ typed_value_to_string ~span:(Some span) ctx v)
  in
  (* Compose and apply *)
  ((ctx, st), eval_op)

(** Evaluates an assertion.
    
    In the case the boolean under scrutinee is symbolic, we synthesize
    a call to [assert ...] then continue in the success branch (and thus
    expand the boolean to [true]).
 *)
let eval_assertion (config : config) (span : Meta.span) (assertion : assertion)
    : st_cm_fun =
 fun ctx ->
  (* Evaluate the operand *)
  let v, ctx, cf_eval_op = eval_operand config span assertion.cond ctx in
  (* Evaluate the assertion *)
  sanity_check __FILE__ __LINE__ (v.ty = TLiteral TBool) span;
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
        sanity_check __FILE__ __LINE__ (config.mode = SymbolicMode) span;
        sanity_check __FILE__ __LINE__ (sv.sv_ty = TLiteral TBool) span;
        (* We continue the execution as if the test had succeeded, and thus
         * perform the symbolic expansion: sv ~~> true.
         * We will of course synthesize an assertion in the generated code
         * (see below). *)
        let ctx =
          apply_symbolic_expansion_non_borrow config span sv ctx
            (SeLiteral (VBool true))
        in
        (* Add the synthesized assertion *)
        ((ctx, Unit), S.synthesize_assertion ctx v)
    | _ ->
        craise __FILE__ __LINE__ span
          ("Expected a boolean, got: "
          ^ typed_value_to_string ~span:(Some span) ctx v)
  in
  (* Compose and apply *)
  (st, cc_comp cf_eval_op cf_eval_assert)

(** Updates the discriminant of a value at a given place.

    There are two situations:
    - either the discriminant is already the proper one (in which case we
      don't do anything)
    - or it is not the proper one (because the variant is not the proper
      one, or the value is actually {!Bottom} - this happens when
      initializing ADT values), in which case we replace the value with
      a variant with all its fields set to {!Bottom}.
      For instance, something like: [Cons Bottom Bottom].
 *)
let set_discriminant (config : config) (span : Meta.span) (p : place)
    (variant_id : VariantId.id) : st_cm_fun =
 fun ctx ->
  log#ldebug
    (lazy
      ("set_discriminant:" ^ "\n- p: " ^ place_to_string ctx p
     ^ "\n- variant id: "
      ^ VariantId.to_string variant_id
      ^ "\n- initial context:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx));
  (* Access the value *)
  let access = Write in
  let ctx, cc = update_ctx_along_read_place config span access p ctx in
  let v, ctx, cc = comp2 cc (prepare_lplace config span p ctx) in
  (* Update the value *)
  match (v.ty, v.value) with
  | TAdt ((TAdtId _ as type_id), generics), VAdt av -> (
      (* There are two situations:
         - either the discriminant is already the proper one (in which case we
           don't do anything)
         - or it is not the proper one, in which case we replace the value with
           a variant with all its fields set to {!Bottom}
      *)
      match av.variant_id with
      | None ->
          craise __FILE__ __LINE__ span
            "Found a struct value while expecting an enum"
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
              | _ -> craise __FILE__ __LINE__ span "Unreachable"
            in
            let ctx, cc =
              comp cc (assign_to_place config span bottom_v p ctx)
            in
            ((ctx, Unit), cc))
  | TAdt ((TAdtId _ as type_id), generics), VBottom ->
      let bottom_v =
        match type_id with
        | TAdtId def_id ->
            compute_expanded_bottom_adt_value span ctx def_id (Some variant_id)
              generics
        | _ -> craise __FILE__ __LINE__ span "Unreachable"
      in
      let ctx, cc = comp cc (assign_to_place config span bottom_v p ctx) in
      ((ctx, Unit), cc)
  | _, VSymbolic _ ->
      sanity_check __FILE__ __LINE__ (config.mode = SymbolicMode) span;
      (* This is a bit annoying: in theory we should expand the symbolic value
       * then set the discriminant, because in the case the discriminant is
       * exactly the one we set, the fields are left untouched, and in the
       * other cases they are set to Bottom.
       * For now, we forbid setting the discriminant of a symbolic value:
       * setting a discriminant should only be used to initialize a value,
       * or reset an already initialized value, really. *)
      craise __FILE__ __LINE__ span "Unexpected value"
  | _, (VAdt _ | VBottom) -> craise __FILE__ __LINE__ span "Inconsistent state"
  | _, (VLiteral _ | VBorrow _ | VLoan _) ->
      craise __FILE__ __LINE__ span "Unexpected value"

(** Push a frame delimiter in the context's environment *)
let ctx_push_frame (ctx : eval_ctx) : eval_ctx =
  { ctx with env = EFrame :: ctx.env }

(** Push a frame delimiter in the context's environment *)
let push_frame (ctx : eval_ctx) : eval_ctx = ctx_push_frame ctx

(** Small helper: compute the type of the return value for a specific
    instantiation of an assumed function.
 *)
let get_assumed_function_return_type (span : Meta.span) (ctx : eval_ctx)
    (fid : assumed_fun_id) (generics : generic_args) : ety =
  sanity_check __FILE__ __LINE__ (generics.trait_refs = []) span;
  (* Retrieve the function's signature *)
  let sg = Assumed.get_assumed_fun_sig fid in
  (* Instantiate the return type  *)
  (* There shouldn't be any reference to Self *)
  let tr_self : trait_instance_id = UnknownTrait __FUNCTION__ in
  let generics = Subst.generic_args_erase_regions generics in
  let { Subst.r_subst = _; ty_subst; cg_subst; tr_subst; tr_self } =
    Subst.make_subst_from_generics sg.generics generics tr_self
  in
  let ty =
    Subst.erase_regions_substitute_types ty_subst cg_subst tr_subst tr_self
      sg.output
  in
  AssociatedTypes.ctx_normalize_erase_ty span ctx ty

let move_return_value (config : config) (span : Meta.span)
    (pop_return_value : bool) (ctx : eval_ctx) :
    typed_value option
    * eval_ctx
    * (SymbolicAst.expression -> SymbolicAst.expression) =
  if pop_return_value then
    let ret_vid = VarId.zero in
    let v, ctx, cc =
      eval_operand config span
        (Move (mk_place_from_var_id ctx span ret_vid))
        ctx
    in
    (Some v, ctx, cc)
  else (None, ctx, fun e -> e)

let pop_frame (config : config) (span : Meta.span) (pop_return_value : bool)
    (ctx : eval_ctx) :
    typed_value option
    * eval_ctx
    * (SymbolicAst.expression -> SymbolicAst.expression) =
  (* Debug *)
  log#ldebug (lazy ("pop_frame:\n" ^ eval_ctx_to_string ~span:(Some span) ctx));

  (* List the local variables, but the return variable *)
  let ret_vid = VarId.zero in
  let rec list_locals env =
    match env with
    | [] -> craise __FILE__ __LINE__ span "Inconsistent environment"
    | EAbs _ :: env -> list_locals env
    | EBinding (BDummy _, _) :: env -> list_locals env
    | EBinding (BVar var, _) :: env ->
        let locals = list_locals env in
        if var.index <> ret_vid then var.index :: locals else locals
    | EFrame :: _ -> []
  in
  let locals : VarId.id list = list_locals ctx.env in
  (* Debug *)
  log#ldebug
    (lazy
      ("pop_frame: locals in which to drop the outer loans: ["
      ^ String.concat "," (List.map VarId.to_string locals)
      ^ "]"));

  (* Move the return value out of the return variable *)
  let v, ctx, cc = move_return_value config span pop_return_value ctx in
  let _ =
    match v with
    | None -> ()
    | Some ret_value ->
        sanity_check __FILE__ __LINE__
          (not (bottom_in_value ctx.ended_regions ret_value))
          span
  in

  (* Drop the outer *loans* we find in the local variables *)
  let ctx, cc =
    comp cc
      ((* Drop the loans *)
       let locals = List.rev locals in
       fold_left_apply_continuation
         (fun lid ctx ->
           drop_outer_loans_at_lplace config span
             (mk_place_from_var_id ctx span lid)
             ctx)
         locals ctx)
  in
  (* Debug *)
  log#ldebug
    (lazy
      ("pop_frame: after dropping outer loans in local variables:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx));

  (* Pop the frame - we remove the [Frame] delimiter, and reintroduce all
   * the local variables (which may still contain borrow permissions - but
   * no outer loans) as dummy variables in the caller frame *)
  let rec pop env =
    match env with
    | [] -> craise __FILE__ __LINE__ span "Inconsistent environment"
    | EAbs abs :: env -> EAbs abs :: pop env
    | EBinding (_, v) :: env ->
        let vid = fresh_dummy_var_id () in
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

(** Auxiliary function - see {!eval_assumed_function_call} *)
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
      cassert __FILE__ __LINE__
        (input_value.ty = boxed_ty)
        span "The input given to Box::new doesn't have the proper type";

      (* Move the input value *)
      let v, ctx, cc =
        eval_operand config span
          (Move (mk_place_from_var_id ctx span input_var.index))
          ctx
      in

      (* Create the new box *)
      (* Create the box value *)
      let generics = TypesUtils.mk_generic_args_from_types [ boxed_ty ] in
      let box_ty = TAdt (TAssumed TBox, generics) in
      let box_v = VAdt { variant_id = None; field_values = [ v ] } in
      let box_v = mk_typed_value span box_ty box_v in

      (* Move this value to the return variable *)
      let dest = mk_place_from_var_id ctx span VarId.zero in
      comp cc (assign_to_place config span box_v dest ctx)
  | _ -> craise __FILE__ __LINE__ span "Inconsistent state"

(** Evaluate a non-local function call in concrete mode *)
let eval_assumed_function_call_concrete (config : config) (span : Meta.span)
    (fid : assumed_fun_id) (call : call) : cm_fun =
 fun ctx ->
  let args = call.args in
  let dest = call.dest in
  match call.func with
  | FnOpMove _ ->
      (* Closure case: TODO *)
      craise __FILE__ __LINE__ span "Closures are not supported yet"
  | FnOpRegular func ->
      let generics = func.generics in
      (* Sanity check: we don't fully handle the const generic vars environment
         in concrete mode yet *)
      sanity_check __FILE__ __LINE__ (generics.const_generics = []) span;

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
      let ret_vid = VarId.zero in
      let ret_ty = get_assumed_function_return_type span ctx fid generics in
      let ret_var = mk_var ret_vid (Some "@return") ret_ty in
      let ctx = push_uninitialized_var span ret_var ctx in

      (* Create and push the input variables *)
      let input_vars =
        VarId.mapi_from1
          (fun id (v : typed_value) -> (mk_var id None v.ty, v))
          args_vl
      in
      let ctx = push_vars span input_vars ctx in

      (* "Execute" the function body. As the functions are assumed, here we call
       * custom functions to perform the proper manipulations: we don't have
       * access to a body. *)
      let ctx, cf_eval_body =
        match fid with
        | BoxNew -> eval_box_new_concrete config span generics ctx
        | Index _ | ArrayToSliceShared | ArrayToSliceMut | ArrayRepeat ->
            craise __FILE__ __LINE__ span "Unimplemented"
      in
      let cc = cc_comp cc cf_eval_body in

      (* Pop the frame *)
      comp cc (pop_frame_assign config span dest ctx)

(** Helper
 
    Create abstractions (with no avalues, which have to be inserted afterwards)
    from a list of abs region groups.
    
    [region_can_end]: gives the region groups from which we generate functions
    which can end or not.
 *)
let create_empty_abstractions_from_abs_region_groups
    (kind : RegionGroupId.id -> abs_kind) (rgl : abs_region_group list)
    (region_can_end : RegionGroupId.id -> bool) : abs list =
  (* We use a reference to progressively create a map from abstraction ids
   * to set of ancestor regions. Note that {!abs_to_ancestors_regions} [abs_id]
   * returns the union of:
   * - the regions of the ancestors of abs_id
   * - the regions of abs_id
   *)
  let abs_to_ancestors_regions : RegionId.Set.t AbstractionId.Map.t ref =
    ref AbstractionId.Map.empty
  in
  (* Auxiliary function to create one abstraction *)
  let create_abs (rg_id : RegionGroupId.id) (rg : abs_region_group) : abs =
    let abs_id = rg.id in
    let original_parents = rg.parents in
    let parents =
      List.fold_left
        (fun s pid -> AbstractionId.Set.add pid s)
        AbstractionId.Set.empty rg.parents
    in
    let regions =
      List.fold_left
        (fun s rid -> RegionId.Set.add rid s)
        RegionId.Set.empty rg.regions
    in
    let ancestors_regions =
      List.fold_left
        (fun acc parent_id ->
          RegionId.Set.union acc
            (AbstractionId.Map.find parent_id !abs_to_ancestors_regions))
        RegionId.Set.empty rg.parents
    in
    let ancestors_regions_union_current_regions =
      RegionId.Set.union ancestors_regions regions
    in
    let can_end = region_can_end rg_id in
    abs_to_ancestors_regions :=
      AbstractionId.Map.add abs_id ancestors_regions_union_current_regions
        !abs_to_ancestors_regions;
    (* Create the abstraction *)
    {
      abs_id;
      kind = kind rg_id;
      can_end;
      parents;
      original_parents;
      regions;
      ancestors_regions;
      avalues = [];
    }
  in
  (* Apply *)
  RegionGroupId.mapi create_abs rgl

let create_push_abstractions_from_abs_region_groups
    (kind : RegionGroupId.id -> abs_kind) (rgl : abs_region_group list)
    (region_can_end : RegionGroupId.id -> bool)
    (compute_abs_avalues : abs -> eval_ctx -> eval_ctx * typed_avalue list)
    (ctx : eval_ctx) : eval_ctx =
  (* Initialize the abstractions as empty (i.e., with no avalues) abstractions *)
  let empty_absl =
    create_empty_abstractions_from_abs_region_groups kind rgl region_can_end
  in

  (* Compute and add the avalues to the abstractions, the insert the abstractions
   * in the context. *)
  let insert_abs (ctx : eval_ctx) (abs : abs) : eval_ctx =
    (* Compute the values to insert in the abstraction *)
    let ctx, avalues = compute_abs_avalues abs ctx in
    (* Add the avalues to the abstraction *)
    let abs = { abs with avalues } in
    (* Insert the abstraction in the context *)
    let ctx = { ctx with env = EAbs abs :: ctx.env } in
    (* Return *)
    ctx
  in
  List.fold_left insert_abs ctx empty_absl

(** Auxiliary helper for [eval_transparent_function_call_symbolic]
    Instantiate the signature and introduce fresh abstractions and region ids while doing so.

    We perform some manipulations when instantiating the signature.

    # Trait impl calls
    ==================
    In particular, we have a special treatment of trait method calls when
    the trait ref is a known impl.

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

    In [option_has_value], we don't want to refer to the [has_value] method
    of the instance of [HasValue] for [Option<T>]. We want to refer directly
    to the function which implements [has_value] for [Option<T>].
    That is, instead of generating this:
    {[
      let option_has_value (T : Type) (x : Option T) : result bool =
        (OptionHasValueInstance T).has_value x
    ]}

    We want to generate this:
    {[
      let option_has_value (T : Type) (x : Option T) : result bool =
        OptionHasValueImpl.has_value T x
    ]}

    # Provided trait methods
    ========================
    Calls to provided trait methods also have a special treatment because
    for now we forbid overriding provided trait methods in the trait implementations,
    which means that whenever we call a provided trait method, we do not refer
    to a trait clause but directly to the method provided in the trait declaration.
 *)
let eval_transparent_function_call_symbolic_inst (span : Meta.span)
    (call : call) (ctx : eval_ctx) :
    fun_id_or_trait_method_ref
    * generic_args
    * (generic_args * trait_instance_id) option
    * fun_decl
    * region_var_groups
    * inst_fun_sig =
  match call.func with
  | FnOpMove _ ->
      (* Closure case: TODO *)
      craise __FILE__ __LINE__ span "Closures are not supported yet"
  | FnOpRegular func -> (
      match func.func with
      | FunId (FRegular fid) ->
          let def = ctx_lookup_fun_decl ctx fid in
          log#ldebug
            (lazy
              ("fun call:\n- call: " ^ call_to_string ctx call
             ^ "\n- call.generics:\n"
              ^ generic_args_to_string ctx func.generics
              ^ "\n- def.signature:\n"
              ^ fun_sig_to_string ctx def.signature));
          let tr_self = UnknownTrait __FUNCTION__ in
          let regions_hierarchy =
            LlbcAstUtils.FunIdMap.find (FRegular fid)
              ctx.fun_ctx.regions_hierarchies
          in
          let inst_sg =
            instantiate_fun_sig span ctx func.generics tr_self def.signature
              regions_hierarchy
          in
          (func.func, func.generics, None, def, regions_hierarchy, inst_sg)
      | FunId (FAssumed _) ->
          (* Unreachable: must be a transparent function *)
          craise __FILE__ __LINE__ span "Unreachable"
      | TraitMethod (trait_ref, method_name, _) -> (
          log#ldebug
            (lazy
              ("trait method call:\n- call: " ^ call_to_string ctx call
             ^ "\n- method name: " ^ method_name ^ "\n- call.generics:\n"
              ^ generic_args_to_string ctx func.generics
              ^ "\n- trait_ref.trait_decl_ref: "
              ^ trait_decl_ref_region_binder_to_string ctx
                  trait_ref.trait_decl_ref));
          (* Check that there are no bound regions *)
          cassert __FILE__ __LINE__
            (trait_ref.trait_decl_ref.binder_regions = [])
            span "Unexpected bound regions";
          let trait_decl_ref = trait_ref.trait_decl_ref.binder_value in
          (* Lookup the trait method signature - there are several possibilities
             depending on whethere we call a top-level trait method impl or the
             method from a local clause *)
          match trait_ref.trait_id with
          | TraitImpl (impl_id, generics) -> (
              (* Lookup the trait impl *)
              let trait_impl = ctx_lookup_trait_impl ctx impl_id in
              log#ldebug
                (lazy ("trait impl: " ^ trait_impl_to_string ctx trait_impl));
              (* First look in the required methods *)
              let method_id =
                List.find_opt
                  (fun (s, _) -> s = method_name)
                  trait_impl.required_methods
              in
              match method_id with
              | Some (_, id) ->
                  (* This is a required method *)
                  let method_def = ctx_lookup_fun_decl ctx id in
                  (* We have to concatenate the generics for the impl
                     and the generics for the method *)
                  let generics = merge_generic_args generics func.generics in
                  (* Instantiate *)
                  let tr_self = trait_ref.trait_id in
                  let fid : fun_id = FRegular id in
                  let regions_hierarchy =
                    LlbcAstUtils.FunIdMap.find fid
                      ctx.fun_ctx.regions_hierarchies
                  in
                  let inst_sg =
                    instantiate_fun_sig span ctx generics tr_self
                      method_def.signature regions_hierarchy
                  in
                  (* Also update the function identifier: we want to forget
                     the fact that we called a trait method, and treat it as
                     a regular function call to the top-level function
                     which implements the method. In order to do this properly,
                     we also need to update the generics.
                  *)
                  let func = FunId fid in
                  ( func,
                    generics,
                    Some (generics, tr_self),
                    method_def,
                    regions_hierarchy,
                    inst_sg )
              | None ->
                  (* If not found, lookup the methods provided by the trait *declaration*
                     (remember: for now, we forbid overriding provided methods) *)
                  cassert __FILE__ __LINE__
                    (trait_impl.provided_methods = [])
                    span "Overriding provided methods is currently forbidden";
                  let trait_decl =
                    ctx_lookup_trait_decl ctx trait_decl_ref.trait_decl_id
                  in
                  let _, method_id =
                    List.find
                      (fun (s, _) -> s = method_name)
                      trait_decl.provided_methods
                  in
                  let method_def = ctx_lookup_fun_decl ctx method_id in
                  (* For the instantiation we have to do something peculiar
                     because the method was defined for the trait declaration.
                     We have to group:
                     - the parameters given to the trait decl reference
                     - the parameters given to the method itself
                     For instance:
                     {[
                       trait Foo<T> {
                         fn f<U>(...) { ... }
                       }

                       fn g<G>(x : G) where Clause0: Foo<G, bool>
                       {
                         x.f::<u32>(...) // The arguments to f are: <G, bool, u32>
                       }
                     ]}
                  *)
                  let all_generics =
                    TypesUtils.merge_generic_args trait_decl_ref.decl_generics
                      func.generics
                  in
                  log#ldebug
                    (lazy
                      ("provided method call:" ^ "\n- method name: "
                     ^ method_name ^ "\n- all_generics:\n"
                      ^ generic_args_to_string ctx all_generics
                      ^ "\n- parent params info: "
                      ^ Print.option_to_string show_params_info
                          method_def.signature.parent_params_info));
                  let regions_hierarchy =
                    LlbcAstUtils.FunIdMap.find (FRegular method_id)
                      ctx.fun_ctx.regions_hierarchies
                  in
                  let tr_self = trait_ref.trait_id in
                  let inst_sg =
                    instantiate_fun_sig span ctx all_generics tr_self
                      method_def.signature regions_hierarchy
                  in
                  ( func.func,
                    func.generics,
                    Some (all_generics, tr_self),
                    method_def,
                    regions_hierarchy,
                    inst_sg ))
          | _ ->
              (* We are using a local clause - we lookup the trait decl *)
              let trait_decl =
                ctx_lookup_trait_decl ctx trait_decl_ref.trait_decl_id
              in
              (* Lookup the method decl in the required *and* the provided methods *)
              let _, method_id =
                List.find
                  (fun (s, _) -> s = method_name)
                  (List.append trait_decl.required_methods
                     trait_decl.provided_methods)
              in
              let method_def = ctx_lookup_fun_decl ctx method_id in
              log#ldebug
                (lazy ("method:\n" ^ fun_decl_to_string ctx method_def));
              (* Instantiate *)
              (* When instantiating, we need to group the generics for the
                 trait ref and the generics for the method *)
              let generics =
                TypesUtils.merge_generic_args trait_decl_ref.decl_generics
                  func.generics
              in
              let regions_hierarchy =
                LlbcAstUtils.FunIdMap.find (FRegular method_id)
                  ctx.fun_ctx.regions_hierarchies
              in
              let tr_self = trait_ref.trait_id in
              let inst_sg =
                instantiate_fun_sig span ctx generics tr_self
                  method_def.signature regions_hierarchy
              in
              ( func.func,
                func.generics,
                Some (generics, tr_self),
                method_def,
                regions_hierarchy,
                inst_sg )))

(** Helper: introduce a fresh symbolic value for a global *)
let eval_global_as_fresh_symbolic_value (span : Meta.span)
    (gref : global_decl_ref) (ctx : eval_ctx) : symbolic_value =
  let generics = gref.global_generics in
  let global = ctx_lookup_global_decl ctx gref.global_id in
  cassert __FILE__ __LINE__ (ty_no_regions global.ty) span
    "Const globals should not contain regions";
  (* Instantiate the type  *)
  (* There shouldn't be any reference to Self *)
  let tr_self : trait_instance_id = UnknownTrait __FUNCTION__ in
  let generics = Subst.generic_args_erase_regions generics in
  let { Subst.r_subst = _; ty_subst; cg_subst; tr_subst; tr_self } =
    Subst.make_subst_from_generics global.generics generics tr_self
  in
  let ty =
    Subst.erase_regions_substitute_types ty_subst cg_subst tr_subst tr_self
      global.ty
  in
  mk_fresh_symbolic_value span ty

(** Evaluate a statement *)
let rec eval_statement (config : config) (st : statement) : stl_cm_fun =
 fun ctx ->
  (* Debugging *)
  log#ldebug
    (lazy
      ("\n**About to evaluate statement**: [\n"
      ^ statement_to_string_with_tab ctx st
      ^ "\n]\n\n**Context**:\n"
      ^ eval_ctx_to_string ~span:(Some st.span) ctx
      ^ "\n\n"));

  (* Take a snapshot of the current context for the purpose of generating pretty names *)
  let cc = S.save_snapshot ctx in
  (* Expand the symbolic values if necessary - we need to do that before
     checking the invariants *)
  let ctx, cc = comp cc (greedy_expand_symbolic_values config st.span ctx) in
  (* Sanity check *)
  Invariants.check_invariants st.span ctx;

  (* Evaluate the statement *)
  comp cc (eval_statement_raw config st ctx)

and eval_statement_raw (config : config) (st : statement) : stl_cm_fun =
 fun ctx ->
  log#ldebug
    (lazy
      ("\neval_statement_raw: statement:\n"
      ^ statement_to_string_with_tab ctx st
      ^ "\n\n"));
  match st.content with
  | Assign (p, rvalue) -> (
      (* We handle global assignments separately *)
      match rvalue with
      | Global gref ->
          (* Evaluate the global *)
          eval_global config st.span p gref ctx
      | GlobalRef (gref, rkind) ->
          (* Evaluate the reference to the global *)
          eval_global_ref config st.span p gref rkind ctx
      | _ ->
          (* Evaluate the rvalue *)
          let res, ctx, cc = eval_rvalue_not_global config st.span rvalue ctx in
          (* Assign *)
          log#ldebug
            (lazy
              ("about to assign to place: " ^ place_to_string ctx p
             ^ "\n- Context:\n"
              ^ eval_ctx_to_string ~span:(Some st.span) ctx));
          let (ctx, res), cf_assign =
            match res with
            | Error EPanic -> ((ctx, Panic), fun e -> e)
            | Ok rv ->
                (* Update the synthesized AST - here we store additional span-information.
                 * We do it only in specific cases (it is not always useful, and
                 * also it can lead to issues - for instance, if we borrow a
                 * reserved borrow, we later can't translate it to pure values...) *)
                let cc =
                  match rvalue with
                  | Global _ | GlobalRef _ ->
                      craise __FILE__ __LINE__ st.span "Unreachable"
                  | Len _ ->
                      craise __FILE__ __LINE__ st.span "Len is not handled yet"
                  | Use _
                  | RvRef
                      ( _,
                        ( BShared
                        | BMut
                        | BTwoPhaseMut
                        | BShallow
                        | BUniqueImmutable ) )
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
                let ctx, cc =
                  comp cc (assign_to_place config st.span rv p ctx)
                in
                ((ctx, Unit), cc)
          in
          let cc = cc_comp cc cf_assign in
          (* Compose and apply *)
          ([ (ctx, res) ], cc_singleton __FILE__ __LINE__ st.span cc))
  | FakeRead p ->
      let ctx, cc = eval_fake_read config st.span p ctx in
      ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | SetDiscriminant (p, variant_id) ->
      let (ctx, res), cc = set_discriminant config st.span p variant_id ctx in
      ([ (ctx, res) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | Drop p ->
      let ctx, cc = drop_value config st.span p ctx in
      ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | Assert assertion ->
      let (ctx, res), cc = eval_assertion config st.span assertion ctx in
      ([ (ctx, res) ], cc_singleton __FILE__ __LINE__ st.span cc)
  | Call call -> eval_function_call config st.span call ctx
  | Panic -> ([ (ctx, Panic) ], cf_singleton __FILE__ __LINE__ st.span)
  | Return -> ([ (ctx, Return) ], cf_singleton __FILE__ __LINE__ st.span)
  | Break i -> ([ (ctx, Break i) ], cf_singleton __FILE__ __LINE__ st.span)
  | Continue i -> ([ (ctx, Continue i) ], cf_singleton __FILE__ __LINE__ st.span)
  | Nop -> ([ (ctx, Unit) ], cf_singleton __FILE__ __LINE__ st.span)
  | Sequence (st1, st2) ->
      (* Evaluate the first statement *)
      let ctx_resl, cf_st1 = eval_statement config st1 ctx in
      (* Evaluate the sequence (evaluate the second statement if the first
         statement successfully evaluated, otherwise transfmit the control-flow
         break) *)
      let ctx_res_cfl =
        List.map
          (fun (ctx, res) ->
            match res with
            (* Evaluation successful: evaluate the second statement *)
            | Unit -> eval_statement config st2 ctx
            (* Control-flow break: transmit. We enumerate the cases on purpose *)
            | Panic
            | Break _
            | Continue _
            | Return
            | LoopReturn _
            | EndEnterLoop _
            | EndContinue _ ->
                ([ (ctx, res) ], cf_singleton __FILE__ __LINE__ st.span))
          ctx_resl
      in
      (* Put everything together:
         - we return the flattened list of contexts and results
         - we need to build the continuation which will build the whole
           expression from the continuations for the individual branches
      *)
      let ctx_resl, cf_st2 = comp_seqs __FILE__ __LINE__ st.span ctx_res_cfl in
      (ctx_resl, cc_comp cf_st1 cf_st2)
  | Loop loop_body ->
      let eval_loop_body = eval_statement config loop_body in
      InterpreterLoops.eval_loop config st.span eval_loop_body ctx
  | Switch switch -> eval_switch config st.span switch ctx
  | Error s -> craise __FILE__ __LINE__ st.span s

and eval_global (config : config) (span : Meta.span) (dest : place)
    (gref : global_decl_ref) : stl_cm_fun =
 fun ctx ->
  match config.mode with
  | ConcreteMode ->
      (* Treat the evaluation of the global as a call to the global body *)
      let generics = gref.global_generics in
      let global = ctx_lookup_global_decl ctx gref.global_id in
      let func = { func = FunId (FRegular global.body); generics } in
      let call = { func = FnOpRegular func; args = []; dest } in
      eval_transparent_function_call_concrete config span global.body call ctx
  | SymbolicMode ->
      (* Generate a fresh symbolic value. In the translation, this fresh symbolic value will be
       * defined as equal to the value of the global (see {!S.synthesize_global_eval}). *)
      let sval = eval_global_as_fresh_symbolic_value span gref ctx in
      let ctx, cc =
        assign_to_place config span
          (mk_typed_value_from_symbolic_value sval)
          dest ctx
      in
      ( [ (ctx, Unit) ],
        cc_singleton __FILE__ __LINE__ span
          (cc_comp (S.synthesize_global_eval gref sval) cc) )

and eval_global_ref (config : config) (span : Meta.span) (dest : place)
    (gref : global_decl_ref) (rk : ref_kind) : stl_cm_fun =
 fun ctx ->
  (* We only support shared references to globals *)
  cassert __FILE__ __LINE__ (rk = RShared) span
    "Can only create shared references to global values";
  match config.mode with
  | ConcreteMode ->
      (* We should treat the evaluation of the global as a call to the global body,
         then create a reference *)
      craise __FILE__ __LINE__ span "Unimplemented"
  | SymbolicMode ->
      (* Generate a fresh symbolic value. In the translation, this fresh symbolic value will be
       * defined as equal to the value of the global (see {!S.synthesize_global_eval}).
       * We then create a reference to the global.
       *)
      let sval = eval_global_as_fresh_symbolic_value span gref ctx in
      let typed_sval = mk_typed_value_from_symbolic_value sval in
      (* Create a shared loan containing the global, as well as a shared borrow *)
      let bid = fresh_borrow_id () in
      let loan : typed_value =
        {
          value = VLoan (VSharedLoan (BorrowId.Set.singleton bid, typed_sval));
          ty = sval.sv_ty;
        }
      in
      let borrow : typed_value =
        {
          value = VBorrow (VSharedBorrow bid);
          ty = TRef (RErased, sval.sv_ty, RShared);
        }
      in
      (* We need to push the shared loan in a dummy variable *)
      let dummy_id = fresh_dummy_var_id () in
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
  (* We evaluate the operand in two steps:
   * first we prepare it, then we check if its value is concrete or
   * symbolic. If it is concrete, we can then evaluate the operand
   * directly, otherwise we must first expand the value.
   * Note that we can't fully evaluate the operand *then* expand the
   * value if it is symbolic, because the value may have been move
   * (and would thus floating in thin air...)!
   * *)
  (* Match on the targets *)
  match switch with
  | If (op, st1, st2) ->
      (* Evaluate the operand *)
      let op_v, ctx, cf_eval_op = eval_operand config span op ctx in
      (* Switch on the value *)
      let ctx_resl, cf_if =
        match op_v.value with
        | VLiteral (VBool b) ->
            (* Branch *)
            if b then eval_statement config st1 ctx
            else eval_statement config st2 ctx
        | VSymbolic sv ->
            (* Expand the symbolic boolean, and continue by evaluating
               the branches *)
            let (ctx_true, ctx_false), cf_bool =
              expand_symbolic_bool config span sv
                (S.mk_opt_place_from_op span op ctx)
                ctx
            in
            let resl_true = eval_statement config st1 ctx_true in
            let resl_false = eval_statement config st2 ctx_false in
            let ctx_resl, cf_branches =
              comp_seqs __FILE__ __LINE__ span [ resl_true; resl_false ]
            in
            let cc el =
              match cf_branches el with
              | [ e_true; e_false ] -> cf_bool (e_true, e_false)
              | _ -> internal_error __FILE__ __LINE__ span
            in
            (ctx_resl, cc)
        | _ -> craise __FILE__ __LINE__ span "Inconsistent state"
      in
      (* Compose *)
      (ctx_resl, cc_comp cf_eval_op cf_if)
  | SwitchInt (op, int_ty, stgts, otherwise) ->
      (* Evaluate the operand *)
      let op_v, ctx, cf_eval_op = eval_operand config span op ctx in
      (* Switch on the value *)
      let ctx_resl, cf_switch =
        match op_v.value with
        | VLiteral (VScalar sv) -> (
            (* Sanity check *)
            sanity_check __FILE__ __LINE__ (sv.int_ty = int_ty) span;
            (* Find the branch *)
            match List.find_opt (fun (svl, _) -> List.mem sv svl) stgts with
            | None -> eval_statement config otherwise ctx
            | Some (_, tgt) -> eval_statement config tgt ctx)
        | VSymbolic sv ->
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
              expand_symbolic_int config span sv
                (S.mk_opt_place_from_op span op ctx)
                int_ty values ctx
            in
            (* Evaluate the branches: first the "regular" branches *)
            let resl_branches =
              List.map
                (fun (ctx, branch) -> eval_statement config branch ctx)
                (List.combine ctx_branches branches)
            in
            (* Then evaluate the "otherwise" branch *)
            let resl_otherwise =
              eval_statement config otherwise ctx_otherwise
            in
            (* Compose the continuations *)
            let resl, cf =
              comp_seqs __FILE__ __LINE__ span
                (resl_branches @ [ resl_otherwise ])
            in
            let cc el =
              let el, e_otherwise = Collections.List.pop_last el in
              cf_int (el, e_otherwise)
            in
            (resl, cc_comp cc cf)
        | _ -> craise __FILE__ __LINE__ span "Inconsistent state"
      in
      (* Compose *)
      (ctx_resl, cc_comp cf_eval_op cf_switch)
  | Match (p, stgts, otherwise) ->
      (* Access the place *)
      let access = Read in
      let expand_prim_copy = false in
      let p_v, ctx, cf_read_p =
        access_rplace_reorganize_and_read config span expand_prim_copy access p
          ctx
      in
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
                | None -> craise __FILE__ __LINE__ span "No otherwise branch"
                | Some otherwise -> eval_statement config otherwise ctx)
            | Some (_, tgt) -> eval_statement config tgt ctx)
        | VSymbolic sv ->
            (* Expand the symbolic value - may lead to branching *)
            let ctxl, cf_expand =
              expand_symbolic_adt config span sv
                (Some (S.mk_mplace span p ctx))
                ctx
            in
            (* Re-evaluate the switch - the value is not symbolic anymore,
               which means we will go to the other branch *)
            let resl =
              List.map (fun ctx -> (eval_switch config span switch) ctx) ctxl
            in
            (* Compose the continuations *)
            let ctx_resl, cf = comp_seqs __FILE__ __LINE__ span resl in
            (ctx_resl, cc_comp cf_expand cf)
        | _ -> craise __FILE__ __LINE__ span "Inconsistent state"
      in
      (* Compose *)
      (ctx_resl, cc_comp cf_read_p cf_match)

(** Evaluate a function call (auxiliary helper for [eval_statement]) *)
and eval_function_call (config : config) (span : Meta.span) (call : call) :
    stl_cm_fun =
  (* There are several cases:
     - this is a local function, in which case we execute its body
     - this is an assumed function, in which case there is a special treatment
     - this is a trait method
  *)
  match config.mode with
  | ConcreteMode -> eval_function_call_concrete config span call
  | SymbolicMode -> eval_function_call_symbolic config span call

and eval_function_call_concrete (config : config) (span : Meta.span)
    (call : call) : stl_cm_fun =
 fun ctx ->
  match call.func with
  | FnOpMove _ -> craise __FILE__ __LINE__ span "Closures are not supported yet"
  | FnOpRegular func -> (
      match func.func with
      | FunId (FRegular fid) ->
          eval_transparent_function_call_concrete config span fid call ctx
      | FunId (FAssumed fid) ->
          (* Continue - note that we do as if the function call has been successful,
           * by giving {!Unit} to the continuation, because we place us in the case
           * where we haven't panicked. Of course, the translation needs to take the
           * panic case into account... *)
          let ctx, cc =
            eval_assumed_function_call_concrete config span fid call ctx
          in
          ([ (ctx, Unit) ], cc_singleton __FILE__ __LINE__ span cc)
      | TraitMethod _ -> craise __FILE__ __LINE__ span "Unimplemented")

and eval_function_call_symbolic (config : config) (span : Meta.span)
    (call : call) : stl_cm_fun =
  match call.func with
  | FnOpMove _ -> craise __FILE__ __LINE__ span "Closures are not supported yet"
  | FnOpRegular func -> (
      match func.func with
      | FunId (FRegular _) | TraitMethod _ ->
          eval_transparent_function_call_symbolic config span call
      | FunId (FAssumed fid) ->
          eval_assumed_function_call_symbolic config span fid call func)

(** Evaluate a local (i.e., non-assumed) function call in concrete mode *)
and eval_transparent_function_call_concrete (config : config) (span : Meta.span)
    (fid : FunDeclId.id) (call : call) : stl_cm_fun =
 fun ctx ->
  let args = call.args in
  let dest = call.dest in
  match call.func with
  | FnOpMove _ -> craise __FILE__ __LINE__ span "Closures are not supported yet"
  | FnOpRegular func ->
      let generics = func.generics in
      (* Sanity check: we don't fully handle the const generic vars environment
         in concrete mode yet *)
      sanity_check __FILE__ __LINE__ (generics.const_generics = []) span;
      (* Retrieve the (correctly instantiated) body *)
      let def = ctx_lookup_fun_decl ctx fid in
      (* We can evaluate the function call only if it is not opaque *)
      let body =
        match def.body with
        | None ->
            craise __FILE__ __LINE__ span
              ("Can't evaluate a call to an opaque function: "
              ^ name_to_string ctx def.item_meta.name)
        | Some body -> body
      in
      (* TODO: we need to normalize the types if we want to correctly support traits *)
      cassert __FILE__ __LINE__ (generics.trait_refs = []) body.span
        "Traits are not supported yet in concrete mode";
      (* There shouldn't be any reference to Self *)
      let tr_self = UnknownTrait __FUNCTION__ in
      let subst =
        Subst.make_subst_from_generics def.signature.generics generics tr_self
      in
      let locals, body_st = Subst.fun_body_substitute_in_body subst body in

      (* Evaluate the input operands *)
      sanity_check __FILE__ __LINE__
        (List.length args = body.locals.arg_count)
        body.span;
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
        | _ -> craise __FILE__ __LINE__ span "Unreachable"
      in
      let input_locals, locals =
        Collections.List.split_at locals body.locals.arg_count
      in

      let ctx = push_var span ret_var (mk_bottom span ret_var.var_ty) ctx in

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
            | Break _
            | Continue _
            | Unit
            | LoopReturn _
            | EndEnterLoop _
            | EndContinue _ -> craise __FILE__ __LINE__ span "Unreachable")
          ctx_resl
      in
      let ctx_resl, cfl = List.split ctx_resl_cfl in
      let cf_pop el = List.map2 (fun cf e -> cf e) cfl el in
      (* Continue *)
      (ctx_resl, cc_comp cc cf_pop)

(** Evaluate a local (i.e., non-assumed) function call in symbolic mode *)
and eval_transparent_function_call_symbolic (config : config) (span : Meta.span)
    (call : call) : stl_cm_fun =
 fun ctx ->
  let func, generics, trait_method_generics, def, regions_hierarchy, inst_sg =
    eval_transparent_function_call_symbolic_inst span call ctx
  in
  (* Sanity check: same number of inputs *)
  sanity_check __FILE__ __LINE__
    (List.length call.args = List.length def.signature.inputs)
    def.item_meta.span;
  (* Sanity check: no nested borrows, borrows in ADTs, etc. *)
  cassert __FILE__ __LINE__
    (List.for_all
       (fun ty -> not (ty_has_nested_borrows ctx.type_ctx.type_infos ty))
       (inst_sg.output :: inst_sg.inputs))
    span "Nested borrows are not supported yet";
  cassert __FILE__ __LINE__
    (List.for_all
       (fun ty -> not (ty_has_adt_with_borrows ctx.type_ctx.type_infos ty))
       (inst_sg.output :: inst_sg.inputs))
    span "ADTs containing borrows are not supported yet";
  (* Evaluate the function call *)
  eval_function_call_symbolic_from_inst_sig config def.item_meta.span func
    def.signature regions_hierarchy inst_sg generics trait_method_generics
    call.args call.dest ctx

(** Evaluate a function call in symbolic mode by using the function signature.

    This allows us to factorize the evaluation of local and non-local function
    calls in symbolic mode: only their signatures matter.

    The [self_trait_ref] trait ref refers to [Self]. We use it when calling
    a provided trait method, because those methods have a special treatment:
    we dot not group them with the required trait methods, and forbid (for now)
    overriding them. We treat them as regular method, which take an additional
    trait ref as input.
 *)
and eval_function_call_symbolic_from_inst_sig (config : config)
    (span : Meta.span) (fid : fun_id_or_trait_method_ref) (sg : fun_sig)
    (regions_hierarchy : region_var_groups) (inst_sg : inst_fun_sig)
    (generics : generic_args)
    (trait_method_generics : (generic_args * trait_instance_id) option)
    (args : operand list) (dest : place) : stl_cm_fun =
 fun ctx ->
  log#ldebug
    (lazy
      ("eval_function_call_symbolic_from_inst_sig:\n- fid: "
      ^ fun_id_or_trait_method_ref_to_string ctx fid
      ^ "\n- inst_sg:\n"
      ^ inst_fun_sig_to_string ctx inst_sg
      ^ "\n- call.generics:\n"
      ^ generic_args_to_string ctx generics
      ^ "\n- args:\n"
      ^ String.concat ", " (List.map (operand_to_string ctx) args)
      ^ "\n- dest:\n" ^ place_to_string ctx dest));

  (* Generate a fresh symbolic value for the return value *)
  let ret_sv_ty = inst_sg.output in
  let ret_spc = mk_fresh_symbolic_value span ret_sv_ty in
  let ret_value = mk_typed_value_from_symbolic_value ret_spc in
  let ret_av regions =
    mk_aproj_loans_value_from_symbolic_value regions ret_spc
  in
  let args_places =
    List.map (fun p -> S.mk_opt_place_from_op span p ctx) args
  in
  let dest_place = Some (S.mk_mplace span dest ctx) in

  (* Evaluate the input operands *)
  let args, ctx, cc = eval_operands config span args ctx in

  (* Generate the abstractions and insert them in the context *)
  let abs_ids = List.map (fun rg -> rg.id) inst_sg.regions_hierarchy in
  let args_with_rtypes = List.combine args inst_sg.inputs in

  (* Check the type of the input arguments *)
  cassert __FILE__ __LINE__
    (List.for_all
       (fun ((arg, rty) : typed_value * rty) ->
         arg.ty = Subst.erase_regions rty)
       args_with_rtypes)
    span "The input arguments don't have the proper type";
  (* Check that the input arguments don't contain symbolic values that can't
   * be fed to functions (i.e., symbolic values output from function return
   * values and which contain borrows of borrows can't be used as function
   * inputs *)
  sanity_check __FILE__ __LINE__
    (List.for_all
       (fun arg ->
         not (value_has_ret_symbolic_value_with_borrow_under_mut ctx arg))
       args)
    span;

  (* Initialize the abstractions and push them in the context.
   * First, we define the function which, given an initialized, empty
   * abstraction, computes the avalues which should be inserted inside.
   *)
  let compute_abs_avalues (abs : abs) (ctx : eval_ctx) :
      eval_ctx * typed_avalue list =
    (* Project over the input values *)
    let ctx, args_projs =
      List.fold_left_map
        (fun ctx (arg, arg_rty) ->
          apply_proj_borrows_on_input_value config span ctx abs.regions
            abs.ancestors_regions arg arg_rty)
        ctx args_with_rtypes
    in
    (* Group the input and output values *)
    (ctx, List.append args_projs [ ret_av abs.regions ])
  in
  (* Actually initialize and insert the abstractions *)
  let call_id = fresh_fun_call_id () in
  let region_can_end _ = true in
  let ctx =
    create_push_abstractions_from_abs_region_groups
      (fun rg_id -> FunCall (call_id, rg_id))
      inst_sg.regions_hierarchy region_can_end compute_abs_avalues ctx
  in
  (* Synthesize the symbolic AST *)
  let cc =
    cc_comp cc
      (S.synthesize_regular_function_call fid call_id ctx sg regions_hierarchy
         abs_ids generics trait_method_generics args args_places ret_spc
         dest_place)
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
          AbstractionId.Set.is_empty abs.parents
          (* Check if it contains non-ignored loans *)
          && Option.is_none
               (InterpreterBorrowsCore
                .get_first_non_ignored_aloan_in_abstraction span abs))
        !abs_ids
    in
    (* Check if there are abstractions to end *)
    if no_loans_abs <> [] then (
      (* Update the reference to the list of asbtraction ids, for the recursive calls *)
      abs_ids := with_loans_abs;
      (* End the abstractions which can be ended *)
      let no_loans_abs = AbstractionId.Set.of_list no_loans_abs in
      let ctx, cc =
        InterpreterBorrows.end_abstractions config span no_loans_abs ctx
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
and eval_assumed_function_call_symbolic (config : config) (span : Meta.span)
    (fid : assumed_fun_id) (call : call) (func : fn_ptr) : stl_cm_fun =
 fun ctx ->
  let generics = func.generics in
  let args = call.args in
  let dest = call.dest in
  (* Sanity check: make sure the type parameters don't contain regions -
   * this is a current limitation of our synthesis *)
  sanity_check __FILE__ __LINE__
    (List.for_all
       (fun ty -> not (ty_has_borrows ctx.type_ctx.type_infos ty))
       generics.types)
    span;

  (* In symbolic mode, the behaviour of a function call is completely defined
   * by the signature of the function: we thus simply generate correctly
   * instantiated signatures, and delegate the work to an auxiliary function *)
  let regions_hierarchy =
    LlbcAstUtils.FunIdMap.find (FAssumed fid) ctx.fun_ctx.regions_hierarchies
  in
  (* There shouldn't be any reference to Self *)
  let tr_self = UnknownTrait __FUNCTION__ in
  let sg = Assumed.get_assumed_fun_sig fid in
  let inst_sig =
    instantiate_fun_sig span ctx generics tr_self sg regions_hierarchy
  in

  (* Evaluate the function call *)
  eval_function_call_symbolic_from_inst_sig config span (FunId (FAssumed fid))
    sg regions_hierarchy inst_sig generics None args dest ctx

(** Evaluate a statement seen as a function body *)
and eval_function_body (config : config) (body : statement) : stl_cm_fun =
 fun ctx ->
  log#ldebug (lazy "eval_function_body:");
  let ctx_resl, cf_body = eval_statement config body ctx in
  let ctx_res_cfl =
    List.map
      (fun (ctx, res) ->
        (* Note that we *don't* check the result ({!Panic}, {!Return}, etc.): we
           delegate the check to the caller. *)
        log#ldebug (lazy "eval_function_body: cf_finish");
        (* Expand the symbolic values if necessary - we need to do that before
           checking the invariants *)
        let ctx, cf = greedy_expand_symbolic_values config body.span ctx in
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
