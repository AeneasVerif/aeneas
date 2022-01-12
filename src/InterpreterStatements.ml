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
module S = Synthesis
open InterpreterUtils
open InterpreterProjectors
open InterpreterExpansion
open InterpreterPaths
open InterpreterExpressions

(** The local logger *)
let log = L.statements_log

(** Result of evaluating a statement *)
type statement_eval_res = Unit | Break of int | Continue of int | Return

(** Drop a value at a given place *)
let drop_value (config : C.config) (ctx : C.eval_ctx) (p : E.place) : C.eval_ctx
    =
  log#ldebug (lazy ("drop_value: place: " ^ place_to_string ctx p));
  (* Prepare the place (by ending the loans, then the borrows) *)
  let ctx, v = prepare_lplace config p ctx in
  (* Replace the value with [Bottom] *)
  let nv = { v with value = V.Bottom } in
  let ctx = write_place_unwrap config Write p nv ctx in
  ctx

(** Assign a value to a given place.

    Note that this function first pushes the value to assign in a dummy variable,
    then prepares the destination (by ending borrows, etc.) before popping the
    dummy variable and putting in its destination (after having checked that
    preparing the destination didn't introduce ⊥).
 *)
let assign_to_place (config : C.config) (ctx : C.eval_ctx) (v : V.typed_value)
    (p : E.place) : C.eval_ctx =
  (* Push the rvalue to a dummy variable, for bookkeeping *)
  let ctx = C.ctx_push_dummy_var ctx v in
  (* Prepare the destination *)
  let ctx, _ = prepare_lplace config p ctx in
  (* Retrieve the dummy variable *)
  let ctx, v = C.ctx_pop_dummy_var ctx in
  (* Checks *)
  assert (not (bottom_in_value ctx.ended_regions v));
  (* Update the destination *)
  let ctx = write_place_unwrap config Write p v ctx in
  ctx

(** Evaluates an assertion.
    
    In the case the boolean under scrutinee is symbolic, we synthesize
    a call to `assert ...` then continue in the success branch (and thus
    expand the boolean to `true`).
 *)
let eval_assertion (config : C.config) (ctx : C.eval_ctx)
    (assertion : A.assertion) : C.eval_ctx eval_result =
  (* There may be a symbolic expansion, so don't fully evaluate the operand
   * (if we moved the value, we can't expand it because it is hanging in
   * thin air, outside of the environment... *)
  let ctx, v = eval_operand_prepare config ctx assertion.cond in
  assert (v.ty = T.Bool);
  let symbolic_mode = config.mode = C.SymbolicMode in
  (* We make a choice here: we could completely decouple the concrete and
   * symbolic executions here but choose not to. In the case where we
   * know the concrete value of the boolean we test, we use this value
   * even if we are in symbolic mode. Note that this case should be
   * extremely rare... *)
  match v.value with
  | Concrete (Bool b) ->
      (* There won't be any symbolic expansions: fully evaluate the operand *)
      let ctx, v' = eval_operand config ctx assertion.cond in
      assert (v' = v);
      (* Branch *)
      if b = assertion.expected then Ok ctx
      else (
        if symbolic_mode then S.synthesize_panic ();
        Error Panic)
  | Symbolic sv ->
      (* We register the fact that we called an assertion (the synthesized
       * code will then check that the assert succeeded) then continue
       * with the succeeding branch: we thus expand the symbolic value with
       * `true` *)
      S.synthesize_assert v;
      let see = SeConcrete (V.Bool true) in
      let ctx = apply_symbolic_expansion_non_borrow config sv see ctx in
      S.synthesize_symbolic_expansion_no_branching sv see;
      (* We can finally fully evaluate the operand *)
      let ctx, _ = eval_operand config ctx assertion.cond in
      Ok ctx
  | _ -> failwith ("Expected a boolean, got: " ^ V.show_value v.value)

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
let set_discriminant (config : C.config) (ctx : C.eval_ctx) (p : E.place)
    (variant_id : T.VariantId.id) : C.eval_ctx * statement_eval_res =
  (* Access the value *)
  let access = Write in
  let ctx = update_ctx_along_read_place config access p ctx in
  let ctx = end_loan_exactly_at_place config access p ctx in
  let v = read_place_unwrap config access p ctx in
  (* Update the value *)
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
            (ctx, Unit)
          else
            (* Replace the value *)
            let bottom_v =
              compute_expanded_bottom_adt_value ctx.type_context.type_defs
                def_id (Some variant_id) regions types
            in
            let ctx = write_place_unwrap config access p bottom_v ctx in
            (ctx, Unit))
  | T.Adt (T.AdtId def_id, regions, types), V.Bottom ->
      let bottom_v =
        compute_expanded_bottom_adt_value ctx.type_context.type_defs def_id
          (Some variant_id) regions types
      in
      let ctx = write_place_unwrap config access p bottom_v ctx in
      (ctx, Unit)
  | _, V.Symbolic _ ->
      assert (config.mode = SymbolicMode);
      (* This is a bit annoying: in theory we should expand the symbolic value
       * then set the discriminant, because in the case the discriminant is
       * exactly the one we set, the fields are left untouched, and in the
       * other cases they are set to Bottom.
       * For now, we forbid setting the discriminant of a symbolic value:
       * setting a discriminant should only be used to initialize a value,
       * really. *)
      failwith "Unexpected value"
  | _, (V.Adt _ | V.Bottom) -> failwith "Inconsistent state"
  | _, (V.Concrete _ | V.Borrow _ | V.Loan _) -> failwith "Unexpected value"

(** Push a frame delimiter in the context's environment *)
let ctx_push_frame (ctx : C.eval_ctx) : C.eval_ctx =
  { ctx with env = Frame :: ctx.env }

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
    current frame and return the return value and the updated context.
 *)
let ctx_pop_frame (config : C.config) (ctx : C.eval_ctx) :
    C.eval_ctx * V.typed_value =
  (* Debug *)
  log#ldebug (lazy ("ctx_pop_frame:\n" ^ eval_ctx_to_string ctx));
  (* Eval *)
  let ret_vid = V.VarId.zero in
  (* List the local variables, but the return variable *)
  let rec list_locals env =
    match env with
    | [] -> failwith "Inconsistent environment"
    | C.Abs _ :: env -> list_locals env
    | C.Var (var, _) :: env ->
        (* There shouldn't be dummy variables *)
        let var = Option.get var in
        let locals = list_locals env in
        if var.index <> ret_vid then var.index :: locals else locals
    | C.Frame :: _ -> []
  in
  let locals = list_locals ctx.env in
  (* Debug *)
  log#ldebug
    (lazy
      ("ctx_pop_frame: locals to drop: ["
      ^ String.concat "," (List.map V.VarId.to_string locals)
      ^ "]"));
  (* Drop the local variables *)
  let ctx =
    List.fold_left
      (fun ctx lid -> drop_value config ctx (mk_place_from_var_id lid))
      ctx locals
  in
  (* Debug *)
  log#ldebug
    (lazy
      ("ctx_pop_frame: after dropping local variables:\n"
     ^ eval_ctx_to_string ctx));
  (* Move the return value out of the return variable *)
  let ctx, ret_value =
    eval_operand config ctx (E.Move (mk_place_from_var_id ret_vid))
  in
  (* Pop the frame *)
  let rec pop env =
    match env with
    | [] -> failwith "Inconsistent environment"
    | C.Abs abs :: env -> C.Abs abs :: pop env
    | C.Var (_, _) :: env -> pop env
    | C.Frame :: env -> env
  in
  let env = pop ctx.env in
  let ctx = { ctx with env } in
  (ctx, ret_value)

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_new_concrete (config : C.config)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (ctx : C.eval_ctx) : C.eval_ctx eval_result =
  (* Check and retrieve the arguments *)
  match (region_params, type_params, ctx.env) with
  | ( [],
      [ boxed_ty ],
      Var (Some input_var, input_value) :: Var (_ret_var, _) :: C.Frame :: _ )
    ->
      (* Required type checking *)
      assert (input_value.V.ty = boxed_ty);

      (* Move the input value *)
      let ctx, moved_input_value =
        eval_operand config ctx
          (E.Move (mk_place_from_var_id input_var.C.index))
      in

      (* Create the box value *)
      let box_ty = T.Adt (T.Assumed T.Box, [], [ boxed_ty ]) in
      let box_v =
        V.Adt { variant_id = None; field_values = [ moved_input_value ] }
      in
      let box_v = mk_typed_value box_ty box_v in

      (* Move this value to the return variable *)
      let dest = mk_place_from_var_id V.VarId.zero in
      let ctx = assign_to_place config ctx box_v dest in

      (* Return *)
      Ok ctx
  | _ -> failwith "Inconsistent state"

(** Auxiliary function which factorizes code to evaluate `std::Deref::deref`
    and `std::DerefMut::deref_mut` - see [eval_non_local_function_call] *)
let eval_box_deref_mut_or_shared_concrete (config : C.config)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (is_mut : bool) (ctx : C.eval_ctx) : C.eval_ctx eval_result =
  (* Check the arguments *)
  match (region_params, type_params, ctx.env) with
  | ( [],
      [ boxed_ty ],
      Var (Some input_var, input_value) :: Var (_ret_var, _) :: C.Frame :: _ )
    -> (
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
      (* Note that the rvalue can't be a discriminant value *)
      match eval_rvalue_non_discriminant config ctx rv with
      | Error err -> Error err
      | Ok (ctx, borrowed_value) ->
          (* Move the borrowed value to its destination *)
          let destp = mk_place_from_var_id V.VarId.zero in
          let ctx = assign_to_place config ctx borrowed_value destp in
          Ok ctx)
  | _ -> failwith "Inconsistent state"

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_deref_concrete (config : C.config)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (ctx : C.eval_ctx) : C.eval_ctx eval_result =
  let is_mut = false in
  eval_box_deref_mut_or_shared_concrete config region_params type_params is_mut
    ctx

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_deref_mut_concrete (config : C.config)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (ctx : C.eval_ctx) : C.eval_ctx eval_result =
  let is_mut = true in
  eval_box_deref_mut_or_shared_concrete config region_params type_params is_mut
    ctx

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
    (type_params : T.ety list) (args : E.operand list) (dest : E.place)
    (ctx : C.eval_ctx) : C.eval_ctx =
  match (region_params, type_params, args) with
  | [], [ boxed_ty ], [ E.Move input_box_place ] ->
      (* Required type checking *)
      let input_box = read_place_unwrap config Write input_box_place ctx in
      (let input_ty = ty_get_box input_box.V.ty in
       assert (input_ty = boxed_ty));

      (* Drop the value *)
      let ctx = drop_value config ctx input_box_place in

      (* Update the destination by setting it to `()` *)
      let ctx = assign_to_place config ctx mk_unit_value dest in

      (* Return *)
      ctx
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
    (type_params : T.ety list) (is_mut : bool) (ctx : C.eval_ctx) :
    C.eval_ctx * A.inst_fun_sig =
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

      let regions = { A.id = abs_id; regions = [ rid ]; parents = [] } in

      let inst_sg =
        { A.regions_hierarchy = [ regions ]; inputs = [ input ]; output }
      in

      (ctx, inst_sg)
  | _ -> failwith "Inconsistent state"

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_deref_inst_sig (region_params : T.erased_region list)
    (type_params : T.ety list) (ctx : C.eval_ctx) : C.eval_ctx * A.inst_fun_sig
    =
  let is_mut = false in
  eval_box_deref_mut_or_shared_inst_sig region_params type_params is_mut ctx

(** Auxiliary function - see [eval_non_local_function_call] *)
let eval_box_deref_mut_inst_sig (region_params : T.erased_region list)
    (type_params : T.ety list) (ctx : C.eval_ctx) : C.eval_ctx * A.inst_fun_sig
    =
  let is_mut = true in
  eval_box_deref_mut_or_shared_inst_sig region_params type_params is_mut ctx

(** Evaluate a non-local function call in concrete mode *)
let eval_non_local_function_call_concrete (config : C.config) (ctx : C.eval_ctx)
    (fid : A.assumed_fun_id) (region_params : T.erased_region list)
    (type_params : T.ety list) (args : E.operand list) (dest : E.place) :
    C.eval_ctx eval_result =
  (* There are two cases (and this is extremely annoying):
     - the function is not box_free
     - the function is box_free
     See [eval_box_free]
  *)
  match fid with
  | A.BoxFree ->
      (* Degenerate case: box_free *)
      Ok (eval_box_free config region_params type_params args dest ctx)
  | _ -> (
      (* "Normal" case: not box_free *)
      (* Evaluate the operands *)
      let ctx, args_vl = eval_operands config ctx args in

      (* Push the stack frame: we initialize the frame with the return variable,
         and one variable per input argument *)
      let ctx = ctx_push_frame ctx in

      (* Create and push the return variable *)
      let ret_vid = V.VarId.zero in
      let ret_ty =
        get_non_local_function_return_type fid region_params type_params
      in
      let ret_var = mk_var ret_vid (Some "@return") ret_ty in
      let ctx = C.ctx_push_uninitialized_var ctx ret_var in

      (* Create and push the input variables *)
      let input_vars =
        V.VarId.mapi_from1
          (fun id (v : V.typed_value) -> (mk_var id None v.V.ty, v))
          args_vl
      in
      let ctx = C.ctx_push_vars ctx input_vars in

      (* "Execute" the function body. As the functions are assumed, here we call
         custom functions to perform the proper manipulations: we don't have
         access to a body. *)
      let res =
        match fid with
        | A.BoxNew -> eval_box_new_concrete config region_params type_params ctx
        | A.BoxDeref ->
            eval_box_deref_concrete config region_params type_params ctx
        | A.BoxDerefMut ->
            eval_box_deref_mut_concrete config region_params type_params ctx
        | A.BoxFree -> failwith "Unreachable"
        (* should have been treated above *)
      in

      (* Check if the function body evaluated correctly *)
      match res with
      | Error err -> Error err
      | Ok ctx ->
          (* Pop the stack frame and retrieve the return value *)
          let ctx, ret_value = ctx_pop_frame config ctx in

          (* Move the return value to its destination *)
          let ctx = assign_to_place config ctx ret_value dest in

          (* Return *)
          Ok ctx)

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
        (ctx, (rg.A.id, abs_id)))
      ctx sg.regions_hierarchy
  in
  let asubst_map : V.AbstractionId.id A.RegionGroupId.Map.t =
    List.fold_left
      (fun mp (rg_id, abs_id) -> A.RegionGroupId.Map.add rg_id abs_id mp)
      A.RegionGroupId.Map.empty rg_abs_ids_bindings
  in
  let asubst (rg_id : A.RegionGroupId.id) : V.AbstractionId.id =
    A.RegionGroupId.Map.find rg_id asubst_map
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
let create_empty_abstractions_from_abs_region_groups
    (rgl : A.abs_region_group list) : V.abs list =
  (* We use a reference to progressively create a map from abstraction ids
   * to set of ancestor regions. Note that abs_to_ancestors_regions[abs_id]
   * returns the union of:
   * - the regions of the ancestors of abs_id
   * - the regions of abs_id
   *)
  let abs_to_ancestors_regions : T.RegionId.set_t V.AbstractionId.Map.t ref =
    ref V.AbstractionId.Map.empty
  in
  (* Auxiliary function to create one abstraction *)
  let create_abs (rg : A.abs_region_group) : V.abs =
    let abs_id = rg.A.id in
    let parents =
      List.fold_left
        (fun s pid -> V.AbstractionId.Set.add pid s)
        V.AbstractionId.Set.empty rg.A.parents
    in
    let regions =
      List.fold_left
        (fun s rid -> T.RegionId.Set.add rid s)
        T.RegionId.Set.empty rg.A.regions
    in
    let ancestors_regions =
      List.fold_left
        (fun acc parent_id ->
          T.RegionId.Set.union acc
            (V.AbstractionId.Map.find parent_id !abs_to_ancestors_regions))
        T.RegionId.Set.empty rg.A.parents
    in
    let ancestors_regions_union_current_regions =
      T.RegionId.Set.union ancestors_regions regions
    in
    abs_to_ancestors_regions :=
      V.AbstractionId.Map.add abs_id ancestors_regions_union_current_regions
        !abs_to_ancestors_regions;
    (* Create the abstraction *)
    { V.abs_id; parents; regions; ancestors_regions; avalues = [] }
  in
  (* Apply *)
  List.map create_abs rgl

(** Evaluate a statement *)
let rec eval_statement (config : C.config) (ctx : C.eval_ctx) (st : A.statement)
    : (C.eval_ctx * statement_eval_res) eval_result list =
  (* Debugging *)
  log#ldebug
    (lazy
      ("\n**About to evaluate statement**: [\n"
      ^ statement_to_string_with_tab ctx st
      ^ "\n]\n\n**Context**:\n" ^ eval_ctx_to_string ctx ^ "\n\n"));
  (* Sanity check *)
  if config.C.check_invariants then Inv.check_invariants ctx;
  (* Evaluate *)
  match st with
  | A.Assign (p, rvalue) -> (
      (* Evaluate the rvalue *)
      match eval_rvalue config ctx rvalue with
      | Error err -> [ Error err ]
      | Ok res ->
          (* Assign *)
          let assign (ctx, rvalue) =
            let ctx = assign_to_place config ctx rvalue p in
            Ok (ctx, Unit)
          in
          List.map assign res)
  | A.FakeRead p ->
      let ctx, _ = prepare_rplace config Read p ctx in
      [ Ok (ctx, Unit) ]
  | A.SetDiscriminant (p, variant_id) ->
      [ Ok (set_discriminant config ctx p variant_id) ]
  | A.Drop p -> [ Ok (drop_value config ctx p, Unit) ]
  | A.Assert assertion -> (
      match eval_assertion config ctx assertion with
      | Ok ctx -> [ Ok (ctx, Unit) ]
      | Error e -> [ Error e ])
  | A.Call call -> eval_function_call config ctx call
  | A.Panic ->
      S.synthesize_panic ();
      [ Error Panic ]
  | A.Return -> [ Ok (ctx, Return) ]
  | A.Break i -> [ Ok (ctx, Break i) ]
  | A.Continue i -> [ Ok (ctx, Continue i) ]
  | A.Nop -> [ Ok (ctx, Unit) ]
  | A.Sequence (st1, st2) ->
      (* Evaluate the first statement *)
      let res1 = eval_statement config ctx st1 in
      (* Evaluate the sequence *)
      let eval_seq res1 =
        match res1 with
        | Error err -> [ Error err ]
        | Ok (ctx, Unit) ->
            (* Evaluate the second statement *)
            eval_statement config ctx st2
        (* Control-flow break: transmit. We enumerate the cases on purpose *)
        | Ok (ctx, Break i) -> [ Ok (ctx, Break i) ]
        | Ok (ctx, Continue i) -> [ Ok (ctx, Continue i) ]
        | Ok (ctx, Return) -> [ Ok (ctx, Return) ]
      in
      List.concat (List.map eval_seq res1)
  | A.Loop loop_body ->
      (* For now, we don't support loops in symbolic mode *)
      assert (config.C.mode = C.ConcreteMode);
      (* Evaluate a loop body

         We need a specific function for the [Continue] case: in case we continue,
         we might have to reevaluate the current loop body with the new context
         (and repeat this an indefinite number of times).
      *)
      let rec eval_loop_body (ctx : C.eval_ctx) :
          (C.eval_ctx * statement_eval_res) eval_result list =
        (* Evaluate the loop body *)
        let body_res = eval_statement config ctx loop_body in
        (* Evaluate the next steps *)
        let eval res =
          match res with
          | Error err -> [ Error err ]
          | Ok (ctx, Unit) ->
              (* We finished evaluating the statement in a "normal" manner *)
              [ Ok (ctx, Unit) ]
          (* Control-flow breaks *)
          | Ok (ctx, Break i) ->
              (* Decrease the break index *)
              if i = 0 then [ Ok (ctx, Unit) ] else [ Ok (ctx, Break (i - 1)) ]
          | Ok (ctx, Continue i) ->
              (* Decrease the continue index *)
              if i = 0 then
                (* We stop there. When we continue, we go back to the beginning
                   of the loop: we must thus reevaluate the loop body (and
                   recheck the result to know whether we must reevaluate again,
                   etc. *)
                eval_loop_body ctx
              else
                (* We don't stop there: transmit *)
                [ Ok (ctx, Continue (i - 1)) ]
          | Ok (ctx, Return) -> [ Ok (ctx, Return) ]
        in
        List.concat (List.map eval body_res)
      in
      (* Apply *)
      eval_loop_body ctx
  | A.Switch (op, tgts) -> eval_switch config op tgts ctx

(** Evaluate a switch *)
and eval_switch (config : C.config) (op : E.operand) (tgts : A.switch_targets)
    (ctx : C.eval_ctx) : (C.eval_ctx * statement_eval_res) eval_result list =
  (* We evaluate the operand in two steps:
   * first we prepare it, then we check if its value is concrete or
   * symbolic. If it is concrete, we can then evaluate the operand
   * directly, otherwise we must first expand the value.
   * Note that we can't fully evaluate the operand *then* expand the
   * value if it is symbolic, because the value may have been move
   * (and would thus floating in thin air...)!
   * *)
  (* Prepare the operand *)
  let ctx, op_v = eval_operand_prepare config ctx op in
  (* Match on the targets *)
  match tgts with
  | A.If (st1, st2) -> (
      match op_v.value with
      | V.Concrete (V.Bool b) ->
          (* Evaluate the operand *)
          let ctx, op_v' = eval_operand config ctx op in
          assert (op_v' = op_v);
          (* Branch *)
          if b then eval_statement config ctx st1
          else eval_statement config ctx st2
      | V.Symbolic sv ->
          (* Synthesis *)
          S.synthesize_symbolic_expansion_if_branching sv;
          (* Expand the symbolic value to true or false *)
          let see_true = SeConcrete (V.Bool true) in
          let see_false = SeConcrete (V.Bool false) in
          let expand_and_execute see st =
            (* Apply the symbolic expansion *)
            let ctx = apply_symbolic_expansion_non_borrow config sv see ctx in
            (* Evaluate the operand *)
            let ctx, _ = eval_operand config ctx op in
            (* Evaluate the branch *)
            eval_statement config ctx st
          in
          (* Execute the two branches *)
          let ctxl_true = expand_and_execute see_true st1 in
          let ctxl_false = expand_and_execute see_false st2 in
          List.append ctxl_true ctxl_false
      | _ -> failwith "Inconsistent state")
  | A.SwitchInt (int_ty, tgts, otherwise) -> (
      match op_v.value with
      | V.Concrete (V.Scalar sv) -> (
          (* Evaluate the operand *)
          let ctx, op_v' = eval_operand config ctx op in
          assert (op_v' = op_v);
          (* Sanity check *)
          assert (sv.V.int_ty = int_ty);
          (* Find the branch *)
          match List.find_opt (fun (sv', _) -> sv = sv') tgts with
          | None -> eval_statement config ctx otherwise
          | Some (_, tgt) -> eval_statement config ctx tgt)
      | V.Symbolic sv ->
          (* Synthesis *)
          S.synthesize_symbolic_expansion_switch_int_branching sv;
          (* For all the branches of the switch, we expand the symbolic value
           * to the value given by the branch and execute the branch statement.
           * For the otherwise branch, we leave the symbolic value as it is
           * (because this branch doesn't precisely define which should be the
           * value of the scrutinee...) and simply execute the otherwise statement.
           *)
          (* Branches other than "otherwise" *)
          let exec_branch (switch_value, branch_st) =
            let see = SeConcrete (V.Scalar switch_value) in
            (* Apply the symbolic expansion *)
            let ctx = apply_symbolic_expansion_non_borrow config sv see ctx in
            (* Evaluate the operand *)
            let ctx, _ = eval_operand config ctx op in
            (* Evaluate the branch *)
            eval_statement config ctx branch_st
          in
          let ctxl = List.map exec_branch tgts in
          (* Otherwise branch *)
          let ctx_otherwise = eval_statement config ctx otherwise in
          (* Put everything together *)
          List.append (List.concat ctxl) ctx_otherwise
      | _ -> failwith "Inconsistent state")

(** Evaluate a function call (auxiliary helper for [eval_statement]) *)
and eval_function_call (config : C.config) (ctx : C.eval_ctx) (call : A.call) :
    (C.eval_ctx * statement_eval_res) eval_result list =
  (* There are two cases *
     - this is a local function, in which case we execute its body
     - this is a non-local function, in which case there is a special treatment
  *)
  let res =
    match call.func with
    | A.Local fid ->
        eval_local_function_call config ctx fid call.region_params
          call.type_params call.args call.dest
    | A.Assumed fid ->
        [
          eval_non_local_function_call config ctx fid call.region_params
            call.type_params call.args call.dest;
        ]
  in
  List.map
    (fun res ->
      match res with Error err -> Error err | Ok ctx -> Ok (ctx, Unit))
    res

(** Evaluate a local (i.e., non-assumed) function call in concrete mode *)
and eval_local_function_call_concrete (config : C.config) (ctx : C.eval_ctx)
    (fid : A.FunDefId.id) (_region_params : T.erased_region list)
    (type_params : T.ety list) (args : E.operand list) (dest : E.place) :
    C.eval_ctx eval_result list =
  (* Retrieve the (correctly instantiated) body *)
  let def = C.ctx_lookup_fun_def ctx fid in
  let tsubst =
    Subst.make_type_subst
      (List.map (fun v -> v.T.index) def.A.signature.type_params)
      type_params
  in
  let locals, body = Subst.fun_def_substitute_in_body tsubst def in

  (* Evaluate the input operands *)
  let ctx, args = eval_operands config ctx args in
  assert (List.length args = def.A.arg_count);

  (* Push a frame delimiter *)
  let ctx = ctx_push_frame ctx in

  (* Compute the initial values for the local variables *)
  (* 1. Push the return value *)
  let ret_var, locals =
    match locals with
    | ret_ty :: locals -> (ret_ty, locals)
    | _ -> failwith "Unreachable"
  in
  let ctx = C.ctx_push_var ctx ret_var (C.mk_bottom ret_var.var_ty) in

  (* 2. Push the input values *)
  let input_locals, locals = Utils.list_split_at locals def.A.arg_count in
  let inputs = List.combine input_locals args in
  (* Note that this function checks that the variables and their values
     have the same type (this is important) *)
  let ctx = C.ctx_push_vars ctx inputs in

  (* 3. Push the remaining local variables (initialized as [Bottom]) *)
  let ctx = C.ctx_push_uninitialized_vars ctx locals in

  (* Execute the function body *)
  let res = eval_function_body config ctx body in

  (* Pop the stack frame and move the return value to its destination *)
  let finish res =
    match res with
    | Error Panic -> Error Panic
    | Ok ctx ->
        (* Pop the stack frame and retrieve the return value *)
        let ctx, ret_value = ctx_pop_frame config ctx in

        (* Move the return value to its destination *)
        let ctx = assign_to_place config ctx ret_value dest in

        (* Return *)
        Ok ctx
  in
  List.map finish res

(** Evaluate a local (i.e., non-assumed) function call in symbolic mode *)
and eval_local_function_call_symbolic (config : C.config) (ctx : C.eval_ctx)
    (fid : A.FunDefId.id) (region_params : T.erased_region list)
    (type_params : T.ety list) (args : E.operand list) (dest : E.place) :
    C.eval_ctx =
  (* Retrieve the (correctly instantiated) signature *)
  let def = C.ctx_lookup_fun_def ctx fid in
  let sg = def.A.signature in
  (* Instantiate the signature and introduce fresh abstraction and region ids
   * while doing so *)
  let ctx, inst_sg = instantiate_fun_sig type_params sg ctx in
  (* Sanity check *)
  assert (List.length args = def.A.arg_count);
  (* Evaluate the function call *)
  eval_function_call_symbolic_from_inst_sig config ctx (A.Local fid) inst_sg
    region_params type_params args dest

(** Evaluate a function call in symbolic mode by using the function signature.

    This allows us to factorize the evaluation of local and non-local function
    calls in symbolic mode: only their signatures matter.
 *)
and eval_function_call_symbolic_from_inst_sig (config : C.config)
    (ctx : C.eval_ctx) (fid : A.fun_id) (inst_sg : A.inst_fun_sig)
    (region_params : T.erased_region list) (type_params : T.ety list)
    (args : E.operand list) (dest : E.place) : C.eval_ctx =
  (* Generate a fresh symbolic value for the return value *)
  let ret_sv_ty = inst_sg.A.output in
  let ret_spc = mk_fresh_symbolic_value ret_sv_ty in
  let ret_value = mk_typed_value_from_symbolic_value ret_spc in
  let ret_av = mk_aproj_loans_from_symbolic_value ret_spc in
  (* Evaluate the input operands *)
  let ctx, args = eval_operands config ctx args in
  let args_with_rtypes = List.combine args inst_sg.A.inputs in
  (* Check the type of the input arguments *)
  assert (
    List.for_all
      (fun ((arg, rty) : V.typed_value * T.rty) ->
        arg.V.ty = Subst.erase_regions rty)
      args_with_rtypes);
  (* Initialize the abstractions as empty (i.e., with no avalues) abstractions *)
  let empty_absl =
    create_empty_abstractions_from_abs_region_groups inst_sg.A.regions_hierarchy
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
    let avalues = List.append args_projs [ ret_av ] in
    (* Add the avalues to the abstraction *)
    let abs = { abs with avalues } in
    (* Insert the abstraction in the context *)
    let ctx = { ctx with env = Abs abs :: ctx.env } in
    (* Return *)
    ctx
  in
  let ctx = List.fold_left insert_abs ctx empty_absl in
  (* Move the return value to its destination *)
  let ctx = assign_to_place config ctx ret_value dest in
  (* Synthesis *)
  S.synthesize_function_call fid region_params type_params args dest ret_spc;
  (* Return *)
  ctx

(** Evaluate a non-local function call in symbolic mode *)
and eval_non_local_function_call_symbolic (config : C.config) (ctx : C.eval_ctx)
    (fid : A.assumed_fun_id) (region_params : T.erased_region list)
    (type_params : T.ety list) (args : E.operand list) (dest : E.place) :
    C.eval_ctx =
  (* Sanity check: make sure the type parameters don't contain regions -
   * this is a current limitation of our synthesis *)
  assert (List.for_all (fun ty -> not (ty_has_regions ty)) type_params);

  (* There are two cases (and this is extremely annoying):
     - the function is not box_free
     - the function is box_free
       See [eval_box_free]
  *)
  match fid with
  | A.BoxFree ->
      (* Degenerate case: box_free - note that this is not really a function
       * call: no need to call a "synthesize_..." function *)
      eval_box_free config region_params type_params args dest ctx
  | _ ->
      (* "Normal" case: not box_free *)
      (* In symbolic mode, the behaviour of a function call is completely defined
       * by the signature of the function: we thus simply generate correctly
       * instantiated signatures, and delegate the work to an auxiliary function *)
      let ctx, inst_sig =
        match fid with
        | A.BoxNew -> (ctx, eval_box_new_inst_sig region_params type_params)
        | A.BoxDeref -> eval_box_deref_inst_sig region_params type_params ctx
        | A.BoxDerefMut ->
            eval_box_deref_mut_inst_sig region_params type_params ctx
        | A.BoxFree -> failwith "Unreachable"
        (* should have been treated above *)
      in

      (* Evaluate the function call *)
      eval_function_call_symbolic_from_inst_sig config ctx (A.Assumed fid)
        inst_sig region_params type_params args dest

(** Evaluate a non-local (i.e, assumed) function call such as `Box::deref`
    (auxiliary helper for [eval_statement]) *)
and eval_non_local_function_call (config : C.config) (ctx : C.eval_ctx)
    (fid : A.assumed_fun_id) (region_params : T.erased_region list)
    (type_params : T.ety list) (args : E.operand list) (dest : E.place) :
    C.eval_ctx eval_result =
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
      eval_non_local_function_call_concrete config ctx fid region_params
        type_params args dest
  | C.SymbolicMode ->
      Ok
        (eval_non_local_function_call_symbolic config ctx fid region_params
           type_params args dest)

(** Evaluate a local (i.e, not assumed) function call (auxiliary helper for
    [eval_statement]) *)
and eval_local_function_call (config : C.config) (ctx : C.eval_ctx)
    (fid : A.FunDefId.id) (region_params : T.erased_region list)
    (type_params : T.ety list) (args : E.operand list) (dest : E.place) :
    C.eval_ctx eval_result list =
  match config.mode with
  | ConcreteMode ->
      eval_local_function_call_concrete config ctx fid region_params type_params
        args dest
  | SymbolicMode ->
      [
        Ok
          (eval_local_function_call_symbolic config ctx fid region_params
             type_params args dest);
      ]

(** Evaluate a statement seen as a function body (auxiliary helper for
    [eval_statement]) *)
and eval_function_body (config : C.config) (ctx : C.eval_ctx)
    (body : A.statement) : C.eval_ctx eval_result list =
  let res = eval_statement config ctx body in
  let finish res =
    match res with
    | Error err -> Error err
    | Ok (ctx, res) -> (
        (* Sanity check *)
        if config.C.check_invariants then Inv.check_invariants ctx;
        match res with
        | Unit | Break _ | Continue _ -> failwith "Inconsistent state"
        | Return -> Ok ctx)
  in
  List.map finish res
