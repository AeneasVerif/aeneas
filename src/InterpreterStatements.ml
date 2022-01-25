module T = Types
module V = Values
module E = Expressions
module C = Contexts
module Subst = Substitute
module A = CfimAst
module L = Logging
open TypesUtils
open ValuesUtils
module Inv = Invariants
module S = SynthesizeSymbolic
open Cps
open InterpreterUtils
open InterpreterProjectors
open InterpreterExpansion
open InterpreterPaths
open InterpreterExpressions

(** The local logger *)
let log = L.statements_log

(** Drop a value at a given place *)
let drop_value (config : C.config) (p : E.place) : cm_fun =
 fun cf ctx ->
  log#ldebug (lazy ("drop_value: place: " ^ place_to_string ctx p));
  (* Prepare the place (by ending the outer loans and the borrows) *)
  let end_borrows = true in
  let prepare = prepare_lplace config end_borrows p in
  (* Replace the value with [Bottom] *)
  let replace cf (v : V.typed_value) ctx =
    let nv = { v with value = V.Bottom } in
    let ctx = write_place_unwrap config Write p nv ctx in
    cf ctx
  in
  (* Compose and apply *)
  comp prepare replace cf ctx

(** Push a dummy variable to the environment *)
let push_dummy_var (v : V.typed_value) : cm_fun =
 fun cf ctx ->
  let ctx = C.ctx_push_dummy_var ctx v in
  cf ctx

(** Pop a dummy variable from the environment *)
let pop_dummy_var (cf : V.typed_value -> m_fun) : m_fun =
 fun ctx ->
  let ctx, v = C.ctx_pop_dummy_var ctx in
  cf v ctx

(** Push an uninitialized variable to the environment *)
let push_uninitialized_var (var : A.var) : cm_fun =
 fun cf ctx ->
  let ctx = C.ctx_push_uninitialized_var ctx var in
  cf ctx

(** Push a list of uninitialized variables to the environment *)
let push_uninitialized_vars (vars : A.var list) : cm_fun =
 fun cf ctx ->
  let ctx = C.ctx_push_uninitialized_vars ctx vars in
  cf ctx

(** Push a variable to the environment *)
let push_var (var : A.var) (v : V.typed_value) : cm_fun =
 fun cf ctx ->
  let ctx = C.ctx_push_var ctx var v in
  cf ctx

(** Push a list of variables to the environment *)
let push_vars (vars : (A.var * V.typed_value) list) : cm_fun =
 fun cf ctx ->
  let ctx = C.ctx_push_vars ctx vars in
  cf ctx

(** Assign a value to a given place.

    Note that this function first pushes the value to assign in a dummy variable,
    then prepares the destination (by ending borrows, etc.) before popping the
    dummy variable and putting in its destination (after having checked that
    preparing the destination didn't introduce ⊥).
 *)
let assign_to_place (config : C.config) (rv : V.typed_value) (p : E.place) :
    cm_fun =
 fun cf ctx ->
  (* Push the rvalue to a dummy variable, for bookkeeping *)
  let cc = push_dummy_var rv in
  (* Prepare the destination *)
  let end_borrows = false in
  let cc = comp cc (prepare_lplace config end_borrows p) in
  (* Retrieve the rvalue from the dummy variable *)
  let cc = comp cc (fun cf _lv -> pop_dummy_var cf) in
  (* Update the destination *)
  let move_dest cf (rv : V.typed_value) : m_fun =
   fun ctx ->
    (* Move the value at destination (that we will overwrite) to a dummy variable
     * to preserve the borrows *)
    let mv = read_place_unwrap config Write p ctx in
    let ctx = C.ctx_push_dummy_var ctx mv in
    (* Write to the destination *)
    (* Checks - maybe the bookkeeping updated the rvalue and introduced bottoms *)
    assert (not (bottom_in_value ctx.ended_regions rv));
    (* Update the destination *)
    let ctx = write_place_unwrap config Write p rv ctx in
    (* Continue *)
    cf ctx
  in
  (* Compose and apply *)
  comp cc move_dest cf ctx

(** Evaluate an assertion, when the scrutinee is not symbolic *)
let eval_assertion_concrete (config : C.config) (assertion : A.assertion) :
    st_cm_fun =
 fun cf ctx ->
  (* There won't be any symbolic expansions: fully evaluate the operand *)
  let eval_op = eval_operand config assertion.cond in
  let eval_assert cf (v : V.typed_value) : m_fun =
   fun ctx ->
    match v.value with
    | Concrete (Bool b) ->
        (* Branch *)
        if b = assertion.expected then cf Unit ctx else cf Panic ctx
    | _ -> failwith ("Expected a boolean, got: " ^ typed_value_to_string ctx v)
  in
  (* Compose and apply *)
  comp eval_op eval_assert cf ctx

(** Evaluates an assertion.
    
    In the case the boolean under scrutinee is symbolic, we synthesize
    a call to `assert ...` then continue in the success branch (and thus
    expand the boolean to `true`).
 *)
let eval_assertion (config : C.config) (assertion : A.assertion) : st_cm_fun =
 fun cf ctx ->
  (* There may be a symbolic expansion, so don't fully evaluate the operand
   * (if we moved the value, we can't expand it because it is hanging in
   * thin air, outside of the environment...): simply update the environment
   * to make sure we have access to the value we want to check. *)
  let prepare = eval_operand_prepare config assertion.cond in
  (* Evaluate the assertion *)
  let eval cf (v : V.typed_value) : m_fun =
   fun ctx ->
    assert (v.ty = T.Bool);
    (* We make a choice here: we could completely decouple the concrete and
     * symbolic executions here but choose not to. In the case where we
     * know the concrete value of the boolean we test, we use this value
     * even if we are in symbolic mode. Note that this case should be
     * extremely rare... *)
    match v.value with
    | Concrete (Bool _) ->
        (* Delegate to the concrete evaluation function *)
        eval_assertion_concrete config assertion cf ctx
    | Symbolic sv ->
        assert (config.mode = C.SymbolicMode);
        assert (sv.V.sv_ty = T.Bool);
        (* Expand the symbolic value, then call the evaluation function for the
         * non-symbolic case *)
        let allow_branching = true in
        let expand = expand_symbolic_value config allow_branching sv in
        comp expand (eval_assertion_concrete config assertion) cf ctx
    | _ -> failwith ("Expected a boolean, got: " ^ typed_value_to_string ctx v)
  in
  (* Compose and apply *)
  comp prepare eval cf ctx

(** Updates the discriminant of a value at a given place.

    There are two situations:
    - either the discriminant is already the proper one (in which case we
      don't do anything)
    - or it is not the proper one (because the variant is not the proper
      one, or the value is actually [Bottom] - this happens when
      initializing ADT values), in which case we replace the value with
      a variant with all its fields set to [Bottom].
      For instance, something like: `Cons Bottom Bottom`.
 *)
let set_discriminant (config : C.config) (p : E.place)
    (variant_id : T.VariantId.id) : st_cm_fun =
 fun cf ctx ->
  (* Access the value *)
  let access = Write in
  let cc = update_ctx_along_read_place config access p in
  let end_borrows = false in
  let cc = comp cc (prepare_lplace config end_borrows p) in
  (* Update the value *)
  let update_value cf (v : V.typed_value) : m_fun =
   fun ctx ->
    match (v.V.ty, v.V.value) with
    | T.Adt (T.AdtId def_id, regions, types), V.Adt av -> (
        (* There are two situations:
           - either the discriminant is already the proper one (in which case we
             don't do anything)
           - or it is not the proper one, in which case we replace the value with
             a variant with all its fields set to [Bottom]
        *)
        match av.variant_id with
        | None -> failwith "Found a struct value while expected an enum"
        | Some variant_id' ->
            if variant_id' = variant_id then (* Nothing to do *)
              cf Unit ctx
            else
              (* Replace the value *)
              let bottom_v =
                compute_expanded_bottom_adt_value ctx.type_context.type_defs
                  def_id (Some variant_id) regions types
              in
              assign_to_place config bottom_v p (cf Unit) ctx)
    | T.Adt (T.AdtId def_id, regions, types), V.Bottom ->
        let bottom_v =
          compute_expanded_bottom_adt_value ctx.type_context.type_defs def_id
            (Some variant_id) regions types
        in
        assign_to_place config bottom_v p (cf Unit) ctx
    | _, V.Symbolic _ ->
        assert (config.mode = SymbolicMode);
        (* This is a bit annoying: in theory we should expand the symbolic value
         * then set the discriminant, because in the case the discriminant is
         * exactly the one we set, the fields are left untouched, and in the
         * other cases they are set to Bottom.
         * For now, we forbid setting the discriminant of a symbolic value:
         * setting a discriminant should only be used to initialize a value,
         * or reset an already initialized value, really. *)
        failwith "Unexpected value"
    | _, (V.Adt _ | V.Bottom) -> failwith "Inconsistent state"
    | _, (V.Concrete _ | V.Borrow _ | V.Loan _) -> failwith "Unexpected value"
  in
  (* Compose and apply *)
  comp cc update_value cf ctx

(** Push a frame delimiter in the context's environment *)
let ctx_push_frame (ctx : C.eval_ctx) : C.eval_ctx =
  { ctx with env = Frame :: ctx.env }

(** Push a frame delimiter in the context's environment *)
let push_frame : cm_fun = fun cf ctx -> cf (ctx_push_frame ctx)

(** Small helper: compute the type of the return value for a specific
    instantiation of a non-local function.
 *)
let get_non_local_function_return_type (fid : A.assumed_fun_id)
    (region_params : T.erased_region list) (type_params : T.ety list) : T.ety =
  match (fid, region_params, type_params) with
  | A.BoxNew, [], [ bty ] -> T.Adt (T.Assumed T.Box, [], [ bty ])
  | A.BoxDeref, [], [ bty ] -> T.Ref (T.Erased, bty, T.Shared)
  | A.BoxDerefMut, [], [ bty ] -> T.Ref (T.Erased, bty, T.Mut)
  | A.BoxFree, [], [ _ ] -> mk_unit_ty
  | _ -> failwith "Inconsistent state"

(** Pop the current frame.
    
    Drop all the local variables but the return variable, move the return
    value out of the return variable, remove all the local variables (but not the
    abstractions!) from the context, remove the [Frame] indicator delimiting the
    current frame and handle the return value to the continuation.
    
    TODO: rename (remove the "ctx_")
 *)
let ctx_pop_frame (config : C.config) (cf : V.typed_value -> m_fun) : m_fun =
 fun ctx ->
  (* Debug *)
  log#ldebug (lazy ("ctx_pop_frame:\n" ^ eval_ctx_to_string ctx));

  (* List the local variables, but the return variable *)
  let ret_vid = V.VarId.zero in
  let rec list_locals env =
    match env with
    | [] -> failwith "Inconsistent environment"
    | C.Abs _ :: env -> list_locals env
    | C.Var (None, _) :: env -> list_locals env
    | C.Var (Some var, _) :: env ->
        let locals = list_locals env in
        if var.index <> ret_vid then var.index :: locals else locals
    | C.Frame :: _ -> []
  in
  let locals : V.VarId.id list = list_locals ctx.env in
  (* Debug *)
  log#ldebug
    (lazy
      ("ctx_pop_frame: locals in which to drop the outer loans: ["
      ^ String.concat "," (List.map V.VarId.to_string locals)
      ^ "]"));

  (* Move the return value out of the return variable *)
  let cc = eval_operand config (E.Move (mk_place_from_var_id ret_vid)) in
  (* Sanity check *)
  let cc =
    comp_check_value cc (fun ret_value ctx ->
        assert (not (bottom_in_value ctx.ended_regions ret_value)))
  in

  (* Drop the outer *loans* we find in the local variables *)
  let cf_drop_loans_in_locals cf (ret_value : V.typed_value) : m_fun =
    (* Drop the loans *)
    let end_borrows = false in
    let locals = List.rev locals in
    let cf_drop =
      List.fold_left
        (fun cf lid ->
          drop_outer_borrows_loans_at_lplace config end_borrows
            (mk_place_from_var_id lid) cf)
        (cf ret_value) locals
    in
    (* Apply *)
    cf_drop
  in
  let cc = comp cc cf_drop_loans_in_locals in
  (* Debug *)
  let cc =
    comp_check_value cc (fun _ ctx ->
        log#ldebug
          (lazy
            ("ctx_pop_frame: after dropping outer loans in local variables:\n"
           ^ eval_ctx_to_string ctx)))
  in

  (* Pop the frame - we remove the `Frame` delimiter, and reintroduce all
   * the local variables (which may still contain borrow permissions - but
   * no outer loans) as dummy variables in the caller frame *)
  let rec pop env =
    match env with
    | [] -> failwith "Inconsistent environment"
    | C.Abs abs :: env -> C.Abs abs :: pop env
    | C.Var (_, v) :: env -> C.Var (None, v) :: pop env
    | C.Frame :: env -> (* Stop here *) env
  in
  let cf_pop cf (ret_value : V.typed_value) : m_fun =
   fun ctx ->
    let env = pop ctx.env in
    let ctx = { ctx with env } in
    cf ret_value ctx
  in
  (* Compose and apply *)
  comp cc cf_pop cf ctx

(** Pop the current frame and assign the returned value to its destination. *)
let pop_frame_assign (config : C.config) (dest : E.place) : cm_fun =
  let cf_pop = ctx_pop_frame config in
  let cf_assign cf ret_value : m_fun =
    assign_to_place config ret_value dest cf
  in
  comp cf_pop cf_assign

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_new_concrete (config : C.config)
    (region_params : T.erased_region list) (type_params : T.ety list) : cm_fun =
 fun cf ctx ->
  (* Check and retrieve the arguments *)
  match (region_params, type_params, ctx.env) with
  | ( [],
      [ boxed_ty ],
      Var (Some input_var, input_value) :: Var (_ret_var, _) :: C.Frame :: _ )
    ->
      (* Required type checking *)
      assert (input_value.V.ty = boxed_ty);

      (* Move the input value *)
      let cf_move =
        eval_operand config (E.Move (mk_place_from_var_id input_var.C.index))
      in

      (* Create the new box *)
      let cf_create cf (moved_input_value : V.typed_value) : m_fun =
        (* Create the box value *)
        let box_ty = T.Adt (T.Assumed T.Box, [], [ boxed_ty ]) in
        let box_v =
          V.Adt { variant_id = None; field_values = [ moved_input_value ] }
        in
        let box_v = mk_typed_value box_ty box_v in

        (* Move this value to the return variable *)
        let dest = mk_place_from_var_id V.VarId.zero in
        let cf_assign = assign_to_place config box_v dest in

        (* Continue *)
        cf_assign cf
      in

      (* Compose and apply *)
      comp cf_move cf_create cf ctx
  | _ -> failwith "Inconsistent state"

(** Auxiliary function which factorizes code to evaluate `std::Deref::deref`
    and `std::DerefMut::deref_mut` - see [eval_non_local_function_call] *)
let eval_box_deref_mut_or_shared_concrete (config : C.config)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (is_mut : bool) : cm_fun =
 fun cf ctx ->
  (* Check the arguments *)
  match (region_params, type_params, ctx.env) with
  | ( [],
      [ boxed_ty ],
      Var (Some input_var, input_value) :: Var (_ret_var, _) :: C.Frame :: _ )
    ->
      (* Required type checking. We must have:
         - input_value.ty == & (mut) Box<ty>
         - boxed_ty == ty
         for some ty
      *)
      (let _, input_ty, ref_kind = ty_get_ref input_value.V.ty in
       assert (match ref_kind with T.Shared -> not is_mut | T.Mut -> is_mut);
       let input_ty = ty_get_box input_ty in
       assert (input_ty = boxed_ty));

      (* Borrow the boxed value *)
      let p =
        { E.var_id = input_var.C.index; projection = [ E.Deref; E.DerefBox ] }
      in
      let borrow_kind = if is_mut then E.Mut else E.Shared in
      let rv = E.Ref (p, borrow_kind) in
      let cf_borrow = eval_rvalue config rv in

      (* Move the borrow to its destination *)
      let cf_move cf res : m_fun =
        match res with
        | Error EPanic ->
            (* We can't get there by borrowing a value *)
            failwith "Unreachable"
        | Ok borrowed_value ->
            (* Move and continue *)
            let destp = mk_place_from_var_id V.VarId.zero in
            assign_to_place config borrowed_value destp cf
      in

      (* Compose and apply *)
      comp cf_borrow cf_move cf ctx
  | _ -> failwith "Inconsistent state"

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_deref_concrete (config : C.config)
    (region_params : T.erased_region list) (type_params : T.ety list) : cm_fun =
  let is_mut = false in
  eval_box_deref_mut_or_shared_concrete config region_params type_params is_mut

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_deref_mut_concrete (config : C.config)
    (region_params : T.erased_region list) (type_params : T.ety list) : cm_fun =
  let is_mut = true in
  eval_box_deref_mut_or_shared_concrete config region_params type_params is_mut

(** Auxiliary function - see [eval_non_local_function_call].

    `Box::free` is not handled the same way as the other assumed functions:
    - in the regular case, whenever we need to evaluate an assumed function,
      we evaluate the operands, push a frame, call a dedicated function
      to correctly update the variables in the frame (and mimic the execution
      of a body) and finally pop the frame
    - in the case of `Box::free`: the value given to this function is often
      of the form `Box(⊥)` because we can move the value out of the
      box before freeing the box. It makes it invalid to see box_free as a
      "regular" function: it is not valid to call a function with arguments
      which contain `⊥`. For this reason, we execute `Box::free` as drop_value,
      but this is a bit annoying with regards to the semantics...

    Followingly this function doesn't behave like the others: it does not expect
    a stack frame to have been pushed, but rather simply behaves like [drop_value].
    It thus updates the box value (by calling [drop_value]) and updates
    the destination (by setting it to `()`).
*)
let eval_box_free (config : C.config) (region_params : T.erased_region list)
    (type_params : T.ety list) (args : E.operand list) (dest : E.place) : cm_fun
    =
 fun cf ctx ->
  match (region_params, type_params, args) with
  | [], [ boxed_ty ], [ E.Move input_box_place ] ->
      (* Required type checking *)
      let input_box = read_place_unwrap config Write input_box_place ctx in
      (let input_ty = ty_get_box input_box.V.ty in
       assert (input_ty = boxed_ty));

      (* Drop the value *)
      let cc = drop_value config input_box_place in

      (* Update the destination by setting it to `()` *)
      let cc = comp cc (assign_to_place config mk_unit_value dest) in

      (* Continue *)
      cc cf ctx
  | _ -> failwith "Inconsistent state"

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_new_inst_sig (region_params : T.erased_region list)
    (type_params : T.ety list) : A.inst_fun_sig =
  (* The signature is:
     `T -> Box<T>`
     where T is the type pram
  *)
  match (region_params, type_params) with
  | [], [ ty_param ] ->
      let input = ety_no_regions_to_rty ty_param in
      let output = mk_box_ty ty_param in
      let output = ety_no_regions_to_rty output in
      { A.regions_hierarchy = []; inputs = [ input ]; output }
  | _ -> failwith "Inconsistent state"

(** Auxiliary function which factorizes code to evaluate `std::Deref::deref`
    and `std::DerefMut::deref_mut` - see [eval_non_local_function_call] *)
let eval_box_deref_mut_or_shared_inst_sig (region_params : T.erased_region list)
    (type_params : T.ety list) (is_mut : bool) : A.inst_fun_sig =
  (* The signature is:
     `&'a (mut) Box<T> -> &'a (mut) T`
     where T is the type param
  *)
  let rid = C.fresh_region_id () in
  let r = T.Var rid in
  let abs_id = C.fresh_abstraction_id () in
  match (region_params, type_params) with
  | [], [ ty_param ] ->
      let ty_param = ety_no_regions_to_rty ty_param in
      let ref_kind = if is_mut then T.Mut else T.Shared in

      let input = mk_box_ty ty_param in
      let input = mk_ref_ty r input ref_kind in

      let output = mk_ref_ty r ty_param ref_kind in

      let regions = { T.id = abs_id; regions = [ rid ]; parents = [] } in

      let inst_sg =
        { A.regions_hierarchy = [ regions ]; inputs = [ input ]; output }
      in

      inst_sg
  | _ -> failwith "Inconsistent state"

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_deref_inst_sig (region_params : T.erased_region list)
    (type_params : T.ety list) : A.inst_fun_sig =
  let is_mut = false in
  eval_box_deref_mut_or_shared_inst_sig region_params type_params is_mut

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_deref_mut_inst_sig (region_params : T.erased_region list)
    (type_params : T.ety list) : A.inst_fun_sig =
  let is_mut = true in
  eval_box_deref_mut_or_shared_inst_sig region_params type_params is_mut

(** Evaluate a non-local function call in concrete mode *)
let eval_non_local_function_call_concrete (config : C.config)
    (fid : A.assumed_fun_id) (region_params : T.erased_region list)
    (type_params : T.ety list) (args : E.operand list) (dest : E.place) : cm_fun
    =
  (* There are two cases (and this is extremely annoying):
     - the function is not box_free
     - the function is box_free
     See [eval_box_free]
  *)
  match fid with
  | A.BoxFree ->
      (* Degenerate case: box_free *)
      eval_box_free config region_params type_params args dest
  | _ ->
      (* "Normal" case: not box_free *)
      (* Evaluate the operands *)
      (*      let ctx, args_vl = eval_operands config ctx args in *)
      let cf_eval_ops = eval_operands config args in

      (* Evaluate the call
       *
       * Style note: at some point we used [comp_transmit] to
       * transmit the result of [eval_operands] above down to [push_vars]
       * below, without having to introduce an intermediary function call,
       * but it made it less clear where the computed values came from,
       * so we reversed the modifications. *)
      let cf_eval_call cf (args_vl : V.typed_value list) : m_fun =
        (* Push the stack frame: we initialize the frame with the return variable,
           and one variable per input argument *)
        let cc = push_frame in

        (* Create and push the return variable *)
        let ret_vid = V.VarId.zero in
        let ret_ty =
          get_non_local_function_return_type fid region_params type_params
        in
        let ret_var = mk_var ret_vid (Some "@return") ret_ty in
        let cc = comp cc (push_uninitialized_var ret_var) in

        (* Create and push the input variables *)
        let input_vars =
          V.VarId.mapi_from1
            (fun id (v : V.typed_value) -> (mk_var id None v.V.ty, v))
            args_vl
        in
        let cc = comp cc (push_vars input_vars) in

        (* "Execute" the function body. As the functions are assumed, here we call
         * custom functions to perform the proper manipulations: we don't have
         * access to a body. *)
        let cf_eval_body : cm_fun =
          match fid with
          | A.BoxNew -> eval_box_new_concrete config region_params type_params
          | A.BoxDeref ->
              eval_box_deref_concrete config region_params type_params
          | A.BoxDerefMut ->
              eval_box_deref_mut_concrete config region_params type_params
          | A.BoxFree ->
              (* Should have been treated above *) failwith "Unreachable"
        in

        let cc = comp cc cf_eval_body in

        (* Pop the frame *)
        let cc = comp cc (pop_frame_assign config dest) in

        (* Continue *)
        cc cf
      in
      (* Compose and apply *)
      comp cf_eval_ops cf_eval_call

(** Instantiate a function signature, introducing fresh abstraction ids and
    region ids. This is mostly used in preparation of function calls, when
    evaluating in symbolic mode of course.
    
    Note: there are no region parameters, because they should be erased.
 *)
let instantiate_fun_sig (type_params : T.ety list) (sg : A.fun_sig)
    (ctx : C.eval_ctx) : C.eval_ctx * A.inst_fun_sig =
  (* Generate fresh abstraction ids and create a substitution from region
   * group ids to abstraction ids *)
  let ctx, rg_abs_ids_bindings =
    List.fold_left_map
      (fun ctx rg ->
        let abs_id = C.fresh_abstraction_id () in
        (ctx, (rg.T.id, abs_id)))
      ctx sg.regions_hierarchy
  in
  let asubst_map : V.AbstractionId.id T.RegionGroupId.Map.t =
    List.fold_left
      (fun mp (rg_id, abs_id) -> T.RegionGroupId.Map.add rg_id abs_id mp)
      T.RegionGroupId.Map.empty rg_abs_ids_bindings
  in
  let asubst (rg_id : T.RegionGroupId.id) : V.AbstractionId.id =
    T.RegionGroupId.Map.find rg_id asubst_map
  in
  (* Generate fresh regions and their substitutions *)
  let _, rsubst, _ = Subst.fresh_regions_with_substs sg.region_params in
  (* Generate the type substitution
   * Note that we need the substitution to map the type variables to
   * [rty] types (not [ety]). In order to do that, we convert the
   * type parameters to types with regions. This is possible only
   * if those types don't contain any regions.
   * This is a current limitation of the analysis: there is still some
   * work to do to properly handle full type parametrization.
   * *)
  let rtype_params = List.map ety_no_regions_to_rty type_params in
  let tsubst =
    Subst.make_type_subst
      (List.map (fun v -> v.T.index) sg.type_params)
      rtype_params
  in
  (* Substitute the signature *)
  let inst_sig = Subst.substitute_signature asubst rsubst tsubst sg in
  (* Return *)
  (ctx, inst_sig)

(** Helper
 
    Create abstractions (with no avalues, which have to be inserted afterwards)
    from a list of abs region groups.
 *)
let create_empty_abstractions_from_abs_region_groups (call_id : V.FunCallId.id)
    (kind : V.abs_kind) (rgl : A.abs_region_group list) : V.abs list =
  (* We use a reference to progressively create a map from abstraction ids
   * to set of ancestor regions. Note that abs_to_ancestors_regions[abs_id]
   * returns the union of:
   * - the regions of the ancestors of abs_id
   * - the regions of abs_id
   *)
  let abs_to_ancestors_regions : T.RegionId.Set.t V.AbstractionId.Map.t ref =
    ref V.AbstractionId.Map.empty
  in
  (* Auxiliary function to create one abstraction *)
  let create_abs (back_id : T.RegionGroupId.id) (rg : A.abs_region_group) :
      V.abs =
    let abs_id = rg.T.id in
    let back_id = Some back_id in
    let original_parents = rg.parents in
    let parents =
      List.fold_left
        (fun s pid -> V.AbstractionId.Set.add pid s)
        V.AbstractionId.Set.empty rg.parents
    in
    let regions =
      List.fold_left
        (fun s rid -> T.RegionId.Set.add rid s)
        T.RegionId.Set.empty rg.regions
    in
    let ancestors_regions =
      List.fold_left
        (fun acc parent_id ->
          T.RegionId.Set.union acc
            (V.AbstractionId.Map.find parent_id !abs_to_ancestors_regions))
        T.RegionId.Set.empty rg.parents
    in
    let ancestors_regions_union_current_regions =
      T.RegionId.Set.union ancestors_regions regions
    in
    abs_to_ancestors_regions :=
      V.AbstractionId.Map.add abs_id ancestors_regions_union_current_regions
        !abs_to_ancestors_regions;
    (* Create the abstraction *)
    {
      V.abs_id;
      call_id;
      back_id;
      kind;
      parents;
      original_parents;
      regions;
      ancestors_regions;
      avalues = [];
    }
  in
  (* Apply *)
  T.RegionGroupId.mapi create_abs rgl

(** Evaluate a statement *)
let rec eval_statement (config : C.config) (st : A.statement) : st_cm_fun =
 fun cf ctx ->
  (* Debugging *)
  log#ldebug
    (lazy
      ("\n**About to evaluate statement**: [\n"
      ^ statement_to_string_with_tab ctx st
      ^ "\n]\n\n**Context**:\n" ^ eval_ctx_to_string ctx ^ "\n\n"));

  (* Expand the symbolic values if necessary - we need to do that before
   * checking the invariants *)
  let cc = greedy_expand_symbolic_values config in
  (* Sanity check *)
  let cc = comp cc (Inv.cf_check_invariants config) in

  (* Evaluate *)
  let cf_eval_st cf : m_fun =
    match st with
    | A.Assign (p, rvalue) ->
        (* Evaluate the rvalue *)
        let cf_eval_rvalue = eval_rvalue config rvalue in
        (* Assign *)
        let cf_assign cf (res : (V.typed_value, eval_error) result) =
          match res with
          | Error EPanic -> cf Panic
          | Ok rvalue -> assign_to_place config rvalue p (cf Unit)
        in
        (* Compose and apply *)
        comp cf_eval_rvalue cf_assign cf
    | A.FakeRead p ->
        let expand_prim_copy = false in
        let cf_prepare = prepare_rplace config expand_prim_copy Read p in
        let cf_continue cf _ = cf in
        comp cf_prepare cf_continue (cf Unit)
    | A.SetDiscriminant (p, variant_id) ->
        set_discriminant config p variant_id cf
    | A.Drop p -> drop_value config p (cf Unit)
    | A.Assert assertion -> eval_assertion config assertion cf
    | A.Call call -> eval_function_call config call cf
    | A.Panic -> cf Panic
    | A.Return -> cf Return
    | A.Break i -> cf (Break i)
    | A.Continue i -> cf (Continue i)
    | A.Nop -> cf Unit
    | A.Sequence (st1, st2) ->
        (* Evaluate the first statement *)
        let cf_st1 = eval_statement config st1 in
        (* Evaluate the sequence *)
        let cf_st2 cf res =
          match res with
          (* Evaluation successful: evaluate the second statement *)
          | Unit -> eval_statement config st2 cf
          (* Control-flow break: transmit. We enumerate the cases on purpose *)
          | Panic | Break _ | Continue _ | Return -> cf res
        in
        (* Compose and apply *)
        comp cf_st1 cf_st2 cf
    | A.Loop loop_body ->
        (* For now, we don't support loops in symbolic mode *)
        assert (config.C.mode = C.ConcreteMode);
        (* Continuation for after we evaluate the loop body: depending the result
           of doing one loop iteration:
           - redoes a loop iteration
           - exits the loop
           - other...

           We need a specific function because of the [Continue] case: in case we
           continue, we might have to reevaluate the current loop body with the
           new context (and repeat this an indefinite number of times).
        *)
        let rec reeval_loop_body res : m_fun =
          match res with
          | Return | Panic -> cf res
          | Break i ->
              (* Break out of the loop by calling the continuation *)
              let res = if i = 0 then Unit else Break (i - 1) in
              cf res
          | Continue 0 ->
              (* Re-evaluate the loop body *)
              eval_statement config loop_body reeval_loop_body
          | Continue i ->
              (* Continue to an outer loop *)
              cf (Continue (i - 1))
          | Unit ->
              (* We can't get there.
               * Note that if we decide not to fail here but rather do
               * the same thing as for [Continue 0], we could make the
               * code slightly simpler: calling [reeval_loop_body] with
               * [Unit] would account for the first iteration of the loop.
               * We prefer to write it this way for consistency and sanity,
               * though. *)
              failwith "Unreachable"
        in
        (* Apply *)
        eval_statement config loop_body reeval_loop_body
    | A.Switch (op, tgts) -> eval_switch config op tgts cf
  in
  (* Compose and apply *)
  comp cc cf_eval_st cf ctx

(** Evaluate a switch *)
and eval_switch (config : C.config) (op : E.operand) (tgts : A.switch_targets) :
    st_cm_fun =
  (* We evaluate the operand in two steps:
   * first we prepare it, then we check if its value is concrete or
   * symbolic. If it is concrete, we can then evaluate the operand
   * directly, otherwise we must first expand the value.
   * Note that we can't fully evaluate the operand *then* expand the
   * value if it is symbolic, because the value may have been move
   * (and would thus floating in thin air...)!
   * *)
  (* Prepare the operand *)
  let cf_prepare_op cf : m_fun = eval_operand_prepare config op cf in
  (* Match on the targets *)
  let cf_match (cf : st_m_fun) (op_v : V.typed_value) : m_fun =
    match tgts with
    | A.If (st1, st2) -> (
        match op_v.value with
        | V.Concrete (V.Bool b) ->
            (* Evaluate the operand *)
            let cf_eval_op cf : m_fun = eval_operand config op cf in
            (* Evaluate the if and the branch body *)
            let cf_branch cf op_v' : m_fun =
              assert (op_v' = op_v);
              (* Branch *)
              if b then eval_statement config st1 cf
              else eval_statement config st2 cf
            in
            (* Compose the continuations *)
            comp cf_eval_op cf_branch cf
        | V.Symbolic sv ->
            (* Expand the symbolic value *)
            let allows_branching = true in
            let cf_expand cf =
              expand_symbolic_value config allows_branching sv cf
            in
            (* Retry *)
            let cf_eval_if cf = eval_switch config op tgts cf in
            (* Compose *)
            comp cf_expand cf_eval_if cf
        | _ -> failwith "Inconsistent state")
    | A.SwitchInt (int_ty, stgts, otherwise) -> (
        match op_v.value with
        | V.Concrete (V.Scalar sv) ->
            (* Evaluate the operand *)
            let cf_eval_op cf = eval_operand config op cf in
            (* Evaluate the branch *)
            let cf_eval_branch cf op_v' =
              (* Sanity check *)
              assert (op_v' = op_v);
              assert (sv.V.int_ty = int_ty);
              (* Find the branch *)
              match List.find_opt (fun (sv', _) -> sv = sv') stgts with
              | None -> eval_statement config otherwise cf
              | Some (_, tgt) -> eval_statement config tgt cf
            in
            (* Compose *)
            comp cf_eval_op cf_eval_branch cf
        | V.Symbolic sv ->
            (* Expand the symbolic value - note that contrary to the boolean
             * case, we can't expand then retry, because when switching over
             * arbitrary integers we need to have an `otherwise` case, in
             * which the scrutinee remains symbolic: if we expand the symbolic,
             * reevaluate the switch, we loop... *)
            let stgts =
              List.map
                (fun (cv, tgt_st) -> (cv, eval_statement config tgt_st cf))
                stgts
            in
            let otherwise = eval_statement config otherwise cf in
            expand_symbolic_int config sv int_ty stgts otherwise
        | _ -> failwith "Inconsistent state")
  in
  (* Compose the continuations *)
  comp cf_prepare_op cf_match

(** Evaluate a function call (auxiliary helper for [eval_statement]) *)
and eval_function_call (config : C.config) (call : A.call) : st_cm_fun =
  (* There are two cases:
     - this is a local function, in which case we execute its body
     - this is a non-local function, in which case there is a special treatment
  *)
  match call.func with
  | A.Local fid ->
      eval_local_function_call config fid call.region_params call.type_params
        call.args call.dest
  | A.Assumed fid ->
      eval_non_local_function_call config fid call.region_params
        call.type_params call.args call.dest

(** Evaluate a local (i.e., non-assumed) function call in concrete mode *)
and eval_local_function_call_concrete (config : C.config) (fid : A.FunDefId.id)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (args : E.operand list) (dest : E.place) : st_cm_fun =
 fun cf ctx ->
  assert (region_params = []);

  (* Retrieve the (correctly instantiated) body *)
  let def = C.ctx_lookup_fun_def ctx fid in
  let tsubst =
    Subst.make_type_subst
      (List.map (fun v -> v.T.index) def.A.signature.type_params)
      type_params
  in
  let locals, body = Subst.fun_def_substitute_in_body tsubst def in

  (* Evaluate the input operands *)
  assert (List.length args = def.A.arg_count);
  let cc = eval_operands config args in

  (* Push a frame delimiter - we use [comp_transmit] to transmit the result
   * of the operands evaluation from above to the functions afterwards, while
   * ignoring it in this function *)
  let cc = comp_transmit cc push_frame in

  (* Compute the initial values for the local variables *)
  (* 1. Push the return value *)
  let ret_var, locals =
    match locals with
    | ret_ty :: locals -> (ret_ty, locals)
    | _ -> failwith "Unreachable"
  in
  let input_locals, locals = Collections.List.split_at locals def.A.arg_count in

  let cc = comp_transmit cc (push_var ret_var (mk_bottom ret_var.var_ty)) in

  (* 2. Push the input values *)
  let cf_push_inputs cf args =
    let inputs = List.combine input_locals args in
    (* Note that this function checks that the variables and their values
     * have the same type (this is important) *)
    push_vars inputs cf
  in
  let cc = comp cc cf_push_inputs in

  (* 3. Push the remaining local variables (initialized as [Bottom]) *)
  let cc = comp cc (push_uninitialized_vars locals) in

  (* Execute the function body *)
  let cc = comp cc (eval_function_body config body) in

  (* Pop the stack frame and move the return value to its destination *)
  let cf_finish cf res =
    match res with
    | Panic -> cf Panic
    | Break _ | Continue _ | Unit -> failwith "Unreachable"
    | Return ->
        (* Pop the stack frame, retrieve the return value, move it to
         * its destination and continue *)
        pop_frame_assign config dest (cf Unit)
  in
  let cc = comp cc cf_finish in

  (* Continue *)
  cc cf ctx

(** Evaluate a local (i.e., non-assumed) function call in symbolic mode *)
and eval_local_function_call_symbolic (config : C.config) (fid : A.FunDefId.id)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (args : E.operand list) (dest : E.place) : st_cm_fun =
 fun cf ctx ->
  (* Retrieve the (correctly instantiated) signature *)
  let def = C.ctx_lookup_fun_def ctx fid in
  let sg = def.A.signature in
  (* Instantiate the signature and introduce fresh abstraction and region ids
   * while doing so *)
  let ctx, inst_sg = instantiate_fun_sig type_params sg ctx in
  (* Sanity check *)
  assert (List.length args = def.A.arg_count);
  (* Evaluate the function call *)
  eval_function_call_symbolic_from_inst_sig config (A.Local fid) inst_sg
    region_params type_params args dest cf ctx

(** Evaluate a function call in symbolic mode by using the function signature.

    This allows us to factorize the evaluation of local and non-local function
    calls in symbolic mode: only their signatures matter.
 *)
and eval_function_call_symbolic_from_inst_sig (config : C.config)
    (fid : A.fun_id) (inst_sg : A.inst_fun_sig)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (args : E.operand list) (dest : E.place) : st_cm_fun =
 fun cf ctx ->
  assert (region_params = []);
  (* Generate a fresh symbolic value for the return value *)
  let ret_sv_ty = inst_sg.A.output in
  let ret_spc = mk_fresh_symbolic_value V.FunCallRet ret_sv_ty in
  let ret_value = mk_typed_value_from_symbolic_value ret_spc in
  let ret_av regions =
    mk_aproj_loans_value_from_symbolic_value regions ret_spc
  in

  (* Evaluate the input operands *)
  let cc = eval_operands config args in

  (* Generate the abstractions and insert them in the context *)
  let cf_call cf (args : V.typed_value list) : m_fun =
   fun ctx ->
    let args_with_rtypes = List.combine args inst_sg.A.inputs in

    (* Check the type of the input arguments *)
    assert (
      List.for_all
        (fun ((arg, rty) : V.typed_value * T.rty) ->
          arg.V.ty = Subst.erase_regions rty)
        args_with_rtypes);
    (* Check that the input arguments don't contain symbolic values that can't 
     * be fed to functions (i.e., symbolic values output from function return
     * values and which contain borrows of borrows can't be used as function
     * inputs *)
    assert (
      List.for_all
        (fun arg ->
          not (value_has_ret_symbolic_value_with_borrow_under_mut ctx arg))
        args);

    (* Initialize the abstractions as empty (i.e., with no avalues) abstractions *)
    let call_id = C.fresh_fun_call_id () in
    let empty_absl =
      create_empty_abstractions_from_abs_region_groups call_id V.FunCall
        inst_sg.A.regions_hierarchy
    in

    (* Add the avalues to the abstractions and insert them in the context *)
    let insert_abs (ctx : C.eval_ctx) (abs : V.abs) : C.eval_ctx =
      (* Project over the input values *)
      let ctx, args_projs =
        List.fold_left_map
          (fun ctx (arg, arg_rty) ->
            apply_proj_borrows_on_input_value config ctx abs.regions
              abs.ancestors_regions arg arg_rty)
          ctx args_with_rtypes
      in
      (* Group the input and output values *)
      let avalues = List.append args_projs [ ret_av abs.regions ] in
      (* Add the avalues to the abstraction *)
      let abs = { abs with avalues } in
      (* Insert the abstraction in the context *)
      let ctx = { ctx with env = Abs abs :: ctx.env } in
      (* Return *)
      ctx
    in
    let ctx = List.fold_left insert_abs ctx empty_absl in

    (* Apply the continuation *)
    let expr = cf ctx in

    (* Synthesize the symbolic AST *)
    let abs_ids = List.map (fun rg -> rg.T.id) inst_sg.regions_hierarchy in
    S.synthesize_regular_function_call fid call_id abs_ids type_params args
      ret_spc expr
  in
  let cc = comp cc cf_call in

  (* Move the return value to its destination *)
  let cc = comp cc (assign_to_place config ret_value dest) in

  (* Continue - note that we do as if the function call has been successful,
   * by giving [Unit] to the continuation, because we place us in the case
   * where we haven't panicked. Of course, the translation needs to take the
   * panic case into account... *)
  cc (cf Unit) ctx

(** Evaluate a non-local function call in symbolic mode *)
and eval_non_local_function_call_symbolic (config : C.config)
    (fid : A.assumed_fun_id) (region_params : T.erased_region list)
    (type_params : T.ety list) (args : E.operand list) (dest : E.place) :
    st_cm_fun =
 fun cf ctx ->
  (* Sanity check: make sure the type parameters don't contain regions -
   * this is a current limitation of our synthesis *)
  assert (
    List.for_all
      (fun ty -> not (ty_has_borrows ctx.type_context.type_infos ty))
      type_params);

  (* There are two cases (and this is extremely annoying):
     - the function is not box_free
     - the function is box_free
       See [eval_box_free]
  *)
  match fid with
  | A.BoxFree ->
      (* Degenerate case: box_free - note that this is not really a function
       * call: no need to call a "synthesize_..." function *)
      eval_box_free config region_params type_params args dest (cf Unit) ctx
  | _ ->
      (* "Normal" case: not box_free *)
      (* In symbolic mode, the behaviour of a function call is completely defined
       * by the signature of the function: we thus simply generate correctly
       * instantiated signatures, and delegate the work to an auxiliary function *)
      let inst_sig =
        match fid with
        | A.BoxNew -> eval_box_new_inst_sig region_params type_params
        | A.BoxDeref -> eval_box_deref_inst_sig region_params type_params
        | A.BoxDerefMut -> eval_box_deref_mut_inst_sig region_params type_params
        | A.BoxFree -> failwith "Unreachable"
        (* should have been treated above *)
      in

      (* Evaluate the function call *)
      eval_function_call_symbolic_from_inst_sig config (A.Assumed fid) inst_sig
        region_params type_params args dest cf ctx

(** Evaluate a non-local (i.e, assumed) function call such as `Box::deref`
    (auxiliary helper for [eval_statement]) *)
and eval_non_local_function_call (config : C.config) (fid : A.assumed_fun_id)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (args : E.operand list) (dest : E.place) : st_cm_fun =
 fun cf ctx ->
  (* Debug *)
  log#ldebug
    (lazy
      (let type_params =
         "["
         ^ String.concat ", " (List.map (ety_to_string ctx) type_params)
         ^ "]"
       in
       let args =
         "[" ^ String.concat ", " (List.map (operand_to_string ctx) args) ^ "]"
       in
       let dest = place_to_string ctx dest in
       "eval_non_local_function_call:\n- fid:" ^ A.show_assumed_fun_id fid
       ^ "\n- type_params: " ^ type_params ^ "\n- args: " ^ args ^ "\n- dest: "
       ^ dest));

  match config.mode with
  | C.ConcreteMode ->
      eval_non_local_function_call_concrete config fid region_params type_params
        args dest (cf Unit) ctx
  | C.SymbolicMode ->
      eval_non_local_function_call_symbolic config fid region_params type_params
        args dest cf ctx

(** Evaluate a local (i.e, not assumed) function call (auxiliary helper for
    [eval_statement]) *)
and eval_local_function_call (config : C.config) (fid : A.FunDefId.id)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (args : E.operand list) (dest : E.place) : st_cm_fun =
  match config.mode with
  | ConcreteMode ->
      eval_local_function_call_concrete config fid region_params type_params
        args dest
  | SymbolicMode ->
      eval_local_function_call_symbolic config fid region_params type_params
        args dest

(** Evaluate a statement seen as a function body (auxiliary helper for
    [eval_statement]) *)
and eval_function_body (config : C.config) (body : A.statement) : st_cm_fun =
 fun cf ctx ->
  let cc = eval_statement config body in
  let cf_finish cf res =
    (* Note that we *don't* check the result ([Panic], [Return], etc.): we
     * delegate the check to the caller. *)
    (* Expand the symbolic values if necessary - we need to do that before
     * checking the invariants *)
    let cc = greedy_expand_symbolic_values config in
    (* Sanity check *)
    let cc = comp_check_ctx cc (Inv.check_invariants config) in
    (* Continue *)
    cc (cf res)
  in
  (* Compose and continue *)
  comp cc cf_finish cf ctx
