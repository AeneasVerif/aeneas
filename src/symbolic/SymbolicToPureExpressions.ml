open Pure
open PureUtils
open InterpreterUtils
open SymbolicToPureCore
open SymbolicToPureTypes
open SymbolicToPureValues

(** The local logger *)
let log = Logging.symbolic_to_pure_expressions_log

let mk_closed_checked_let file line ctx can_fail pat bound next =
  mk_closed_checked_let file line ctx.span can_fail pat bound next

let mk_closed_checked_lets file line ctx can_fail pat_bounds next =
  mk_closed_checked_lets file line ctx.span can_fail pat_bounds next

(** TODO: not very clean. *)
let get_fun_effect_info (ctx : bs_ctx) (fun_id : A.fn_ptr_kind)
    (lid : V.LoopId.id option) (gid : T.RegionGroupId.id option) :
    fun_effect_info =
  match lid with
  | None -> (
      match fun_id with
      | TraitMethod (_, _, fid) | FunId (FRegular fid) ->
          let dsg = A.FunDeclId.Map.find fid ctx.fun_dsigs in
          let info =
            match gid with
            | None -> dsg.fun_ty.fwd_info.effect_info
            | Some gid ->
                (RegionGroupId.Map.find gid dsg.fun_ty.back_sg).effect_info
          in
          {
            info with
            is_rec = (info.is_rec || Option.is_some lid) && gid = None;
          }
      | FunId (FBuiltin _) ->
          compute_raw_fun_effect_info (Some ctx.span) ctx.fun_ctx.fun_infos
            fun_id lid gid)
  | Some lid -> (
      (* This is necessarily for the current function *)
      match fun_id with
      | FunId (FRegular fid) -> (
          [%sanity_check] ctx.span (fid = ctx.fun_decl.def_id);
          (* Lookup the loop *)
          let lid = V.LoopId.Map.find lid ctx.loop_ids_map in
          let loop_info = LoopId.Map.find lid ctx.loops in
          match gid with
          | None -> loop_info.fwd_effect_info
          | Some gid -> RegionGroupId.Map.find gid loop_info.back_effect_infos)
      | _ -> [%craise] ctx.span "Unreachable")

let translate_fn_ptr_kind (ctx : bs_ctx) (id : A.fn_ptr_kind) : fn_ptr_kind =
  match id with
  | FunId fun_id -> FunId fun_id
  | TraitMethod (trait_ref, method_name, fun_decl_id) ->
      let type_infos = ctx.type_ctx.type_infos in
      let trait_ref =
        translate_fwd_trait_ref (Some ctx.span) type_infos trait_ref
      in
      TraitMethod (trait_ref, method_name, fun_decl_id)

(* Introduce variables for the backward functions.

   We may filter the region group ids. This is useful for the loops: not all the
   parent function region groups can be linked to a region abstraction
   introduced by the loop.
*)
let fresh_back_vars_for_current_fun (ctx : bs_ctx)
    (keep_rg_ids : RegionGroupId.Set.t option) : bs_ctx * fvar option list =
  (* We lookup the LLBC definition in an attempt to derive pretty names
     for the backward functions. *)
  let back_var_names =
    let def_id = ctx.fun_decl.def_id in
    let sg = ctx.fun_decl.signature in
    let regions_hierarchy =
      LlbcAstUtils.FunIdMap.find (FRegular def_id)
        ctx.fun_ctx.regions_hierarchies
    in
    List.map
      (fun (gid, _) ->
        let rg = RegionGroupId.nth regions_hierarchy gid in
        let region_names =
          List.map
            (fun rid -> (T.RegionId.nth sg.generics.regions rid).name)
            rg.regions
        in
        let name =
          match region_names with
          | [] -> "back"
          | [ Some r ] -> "back" ^ r
          | _ ->
              (* Concatenate all the region names *)
              "back"
              ^ String.concat "" (List.filter_map (fun x -> x) region_names)
        in
        Some name)
      (RegionGroupId.Map.bindings ctx.sg.fun_ty.back_sg)
  in
  let back_vars =
    List.combine back_var_names (compute_back_tys ctx.sg.fun_ty keep_rg_ids)
  in
  let back_vars =
    List.map
      (fun (name, ty) ->
        match ty with
        | None -> None
        | Some ty ->
            (* If the type is not an arrow type, don't use the name "back"
               (it is a backward function with no inputs, that is to say a
               value) *)
            let name = if is_arrow_ty ty then name else None in
            Some (name, ty))
      back_vars
  in
  (* If there is one backward function or less, we use the name "back"
     (there is no point in using the lifetime name, and it makes the
     code generation more stable) *)
  let num_back_vars = List.length (List.filter_map (fun x -> x) back_vars) in
  let back_vars =
    if num_back_vars = 1 then
      List.map
        (Option.map (fun (name, ty) -> (Option.map (fun _ -> "back") name, ty)))
        back_vars
    else back_vars
  in
  fresh_opt_vars back_vars ctx

(** Add meta-information to an expression *)
let mk_emeta_symbolic_assignments (vars : fvar list) (values : texpr list)
    (e : texpr) : texpr =
  let var_values = List.combine (List.map mk_texpr_from_fvar vars) values in
  if var_values <> [] then mk_emeta (SymbolicAssignments var_values) e else e

(** Derive naming information from a context.

    We explore the LLBC context and look in which bindings the symbolic values
    appear: we use this information to derive naming information. *)
let eval_ctx_to_symbolic_assignments_info (ctx : bs_ctx)
    (ectx : Contexts.eval_ctx) : (fvar * string) list =
  let info : (fvar * string) list ref = ref [] in
  let push_info fv name = info := (fv, name) :: !info in
  let visitor =
    object (self)
      inherit [_] Contexts.iter_eval_ctx

      method! visit_env_elem _ ee =
        match ee with
        | EBinding (BVar { index = _; name = Some name }, v) ->
            self#visit_tvalue name v
        | _ -> () (* Ignore *)

      method! visit_value name v =
        match v with
        | VLiteral _ | VBottom -> ()
        | VBorrow (VMutBorrow (_, v)) | VLoan (VSharedLoan (_, v)) ->
            self#visit_tvalue name v
        | VSymbolic sv ->
            (* Translate the type *)
            let ty = ctx_translate_fwd_ty ctx sv.sv_ty in
            (* If the type is unit, do nothing *)
            if ty_is_unit ty then ()
            else
              (* Otherwise lookup the variable - note that the variable may
                 not be present in the context in case of error: we delegate
                 to the lookup function the task of raising an error if the user
                 wants to fail hard. *)
              Option.iter
                (fun (var : fvar) -> push_info var name)
                (lookup_var_for_symbolic_value sv.sv_id ctx)
        | _ -> ()
    end
  in
  (* Visit the context *)
  visitor#visit_eval_ctx "x" ectx;
  (* Return the computed information *)
  !info

let translate_error (span : Meta.span option) (msg : string) : texpr =
  { e = EError (span, msg); ty = Error }

(** Small helper.

    We use this to properly deconstruct the values given back by backward
    functions in the presence of enumerations. See
    [bs_ctx.mut_borrow_to_consumed].

    This helper transforms a let-bound pattern and a bound expression to
    properly introduce matches if necessary.

    For instance, we use it to transform this:
    {[
      let Some x = e in
          ^^^^^^   ^
           pat     let-bound expression
    ]}
    into:
    {[
       let x = match e with | Some x -> x | _ -> default_value in
           ^   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
      new pat     new let-bound expression
    ]}

    **Remarks:** the function receives an open pattern and outputs an open
    pattern. *)
let decompose_let_match (ctx : bs_ctx) ((pat, bound) : tpattern * texpr) :
    bs_ctx * (tpattern * texpr) =
  [%ltrace
    "- pat: " ^ tpattern_to_string ctx pat ^ "\n- bound: "
    ^ texpr_to_string ctx bound];

  let found_enum = ref false in
  (* We update the pattern if it deconstructs an enumeration with > 1 variants *)
  let visitor =
    object
      inherit [_] reduce_expr as super
      method zero : fvar list = []
      method plus vars0 vars1 = vars0 @ vars1
      method! visit_tpattern _ pat = super#visit_tpattern pat.ty pat

      method! visit_adt_pattern ty pat =
        (* Lookup the type decl *)
        let type_id, _ = ty_as_adt ctx.span ty in
        match type_id with
        | TAdtId id ->
            let decl = bs_ctx_lookup_type_decl id ctx in
            begin
              match decl.kind with
              | Struct _ | Opaque -> ()
              | Enum vl -> if List.length vl > 1 then found_enum := true else ()
            end;
            super#visit_adt_pattern ty pat
        | TTuple ->
            (* ok *)
            super#visit_adt_pattern ty pat
        | TBuiltin _ ->
            (* Shouldn't happen *)
            [%craise] ctx.span "Unreachable"

      method! visit_PBound _ _ _ = [%internal_error] ctx.span
      method! visit_POpen _ var _ = [ var ]
    end
  in

  (* Visit the pattern *)
  let vars : fvar list = visitor#visit_tpattern pat.ty pat in

  (* *)
  if !found_enum then
    (* Found an enumeration with > 1 variants: we have to deconstruct
       the pattern *)
    (* First, refresh the variables - we will use fresh variables
       in the patterns of the internal match *)
    let (ctx, fresh_vars) : _ * fvar list =
      List.fold_left_map
        (fun ctx (var : fvar) -> fresh_var var.basename var.ty ctx)
        ctx vars
    in
    (* Create the new pattern for the match, with the fresh variables *)
    let subst =
      FVarId.Map.of_list
        (List.map2 (fun (v0 : fvar) (v1 : fvar) -> (v0.id, v1)) vars fresh_vars)
    in
    let subst_visitor =
      object
        inherit [_] map_expr
        method! visit_POpen _ v mp = POpen (FVarId.Map.find v.id subst, mp)
        method! visit_PBound _ _ = [%internal_error] ctx.span
      end
    in
    (* Create the correct branch *)
    let match_pat = subst_visitor#visit_tpattern () pat in
    let match_e = List.map mk_texpr_from_fvar fresh_vars in
    let match_e = mk_simpl_tuple_texpr ctx.span match_e in
    let match_branch = close_branch ctx.span match_pat match_e in
    (* Create the otherwise branch *)
    let default_e =
      List.map
        (fun (v : fvar) ->
          (* We need to lookup the default values corresponding to
             each given back symbolic value *)
          match FVarId.Map.find_opt v.id ctx.var_id_to_default with
          | Some e -> e
          | None ->
              (* This is a bug, but we might want to continue generating the model:
                 as an escape hatch, simply use the original variable (this will
                 lead to incorrect code of course) *)
              [%save_error] ctx.span
                ("Internal error: could not find variable. Please report an \
                  issue. Debugging information:" ^ "\n- v.id: "
               ^ FVarId.to_string v.id ^ "\n- ctx.var_id_to_default: "
                ^ FVarId.Map.to_string None (texpr_to_string ctx)
                    ctx.var_id_to_default
                ^ "\n");
              mk_texpr_from_fvar v)
        vars
    in
    let default_e = mk_simpl_tuple_texpr ctx.span default_e in
    let default_pat = mk_dummy_pattern pat.ty in
    let default_branch = close_branch ctx.span default_pat default_e in
    let switch_e = Switch (bound, Match [ match_branch; default_branch ]) in
    let bound = { e = switch_e; ty = match_e.ty } in
    (* Update the pattern itself *)
    let pat =
      mk_simpl_tuple_pattern
        (List.map (fun v -> mk_tpattern_from_fvar v None) vars)
    in
    (* *)
    (ctx, (pat, bound))
  else (* Nothing to do *)
    (ctx, (pat, bound))

let rec translate_expr (e : S.expr) (ctx : bs_ctx) : texpr =
  [%ldebug "e:\n" ^ bs_ctx_expr_to_string ctx e];
  match e with
  | S.Return (ectx, opt_v) ->
      (* We reached a return.
         Remark: we can't get there if we are inside a loop. *)
      translate_return ectx opt_v ctx
  | ReturnWithLoop (loop_id, is_continue) ->
      (* We reached a return and are inside a loop. *)
      translate_return_with_loop loop_id is_continue ctx
  | Panic -> translate_panic ctx
  | FunCall (call, e) -> translate_function_call call e ctx
  | EndAbstraction (ectx, abs, e) -> translate_end_abstraction ectx abs e ctx
  | EvalGlobal (gid, generics, sv, e) ->
      translate_global_eval gid generics sv e ctx
  | Assertion (ectx, v, e) -> translate_assertion ectx v e ctx
  | Expansion (p, sv, exp) -> translate_expansion p sv exp ctx
  | IntroSymbolic (ectx, p, sv, v, e) ->
      translate_intro_symbolic ectx p sv v e ctx
  | Meta (span, e) -> translate_espan span e ctx
  | ForwardEnd (return_value, ectx, loop_sid_maps, e, back_e) ->
      (* Translate the end of a function, or the end of a loop.

         The case where we (re-)enter a loop is handled here.
      *)
      translate_forward_end return_value ectx loop_sid_maps e back_e ctx
  | Loop loop -> translate_loop loop ctx
  | Error (span, msg) -> translate_error span msg

and translate_panic (ctx : bs_ctx) : texpr = Option.get ctx.mk_panic

(** [opt_v]: the value to return, in case we translate a forward body.

    Remark: for now, we can't get there if we are inside a loop. If inside a
    loop, we use {!translate_return_with_loop}.

    Remark: in case we merge the forward/backward functions, we introduce those
    in [translate_forward_end]. *)
and translate_return (ectx : C.eval_ctx) (opt_v : V.tvalue option)
    (ctx : bs_ctx) : texpr =
  let opt_v = Option.map (tvalue_to_texpr ctx ectx) opt_v in
  (Option.get ctx.mk_return) ctx opt_v

and translate_return_with_loop (loop_id : V.LoopId.id) (is_continue : bool)
    (ctx : bs_ctx) : texpr =
  [%sanity_check] ctx.span (is_continue = ctx.inside_loop);
  let loop_id = V.LoopId.Map.find loop_id ctx.loop_ids_map in
  [%sanity_check] ctx.span (loop_id = Option.get ctx.loop_id);

  (* Lookup the loop information *)
  let loop_id = Option.get ctx.loop_id in
  let loop_info = LoopId.Map.find loop_id ctx.loops in

  (* There are two cases depending on whether we translate a backward function
     or not.
  *)
  let output =
    match ctx.bid with
    | None -> Option.get loop_info.forward_output_no_state_no_result
    | Some _ ->
        (* Backward *)
        (* Group the variables in which we stored the values we need to give back.
         * See the explanations for the [SynthInput] case in [translate_end_abstraction] *)
        (* It can happen that we did not end any output abstraction, because the
           loop didn't use borrows corresponding to the region we just ended.
           If this happens, there are no backward outputs.
        *)
        let backward_outputs =
          match ctx.backward_outputs with
          | Some outputs -> outputs
          | None -> []
        in
        let field_values = List.map mk_texpr_from_fvar backward_outputs in
        mk_simpl_tuple_texpr ctx.span field_values
  in

  (* We may need to return a state
   * - error-monad: Return x
   * - state-error: Return (state, x)
   * Note that the loop function and the parent function live in the same
   * effect - in particular, one manipulates a state iff the other does
   * the same.
   *)
  let effect_info = ctx_get_effect_info ctx in
  (* Wrap in a result if the backward function cal fail *)
  let output =
    if effect_info.can_fail then mk_result_ok_texpr ctx.span output else output
  in
  mk_emeta (Tag "return_with_loop") output

and translate_function_call (call : S.call) (e : S.expr) (ctx : bs_ctx) : texpr
    =
  [%ltrace
    "- call.call_id:"
    ^ S.show_call_id call.call_id
    ^ "\n\n- call.generics:\n"
    ^ ctx_generic_args_to_string ctx call.generics
    ^ "\n\n- call.inst_sg:\n"
    ^ Print.option_to_string (inst_fun_sig_to_string call.ctx) call.inst_sg];
  (* We have to treat unsized casts separately *)
  match call.call_id with
  | S.Unop (Cast (CastUnsize (ty0, ty1, _))) ->
      translate_cast_unsize call e ty0 ty1 ctx
  | _ -> translate_function_call_aux call e ctx

(** Handle the function call cases which are not unsized casts *)
and translate_function_call_aux (call : S.call) (e : S.expr) (ctx : bs_ctx) :
    texpr =
  (* Register the consumed mutable borrows to compute default values *)
  let ctx =
    List.fold_left (register_consumed_mut_borrows call.ctx) ctx call.args
  in
  (* Translate the function call *)
  let generics = ctx_translate_fwd_generic_args ctx call.generics in
  let args =
    let args = List.map (tvalue_to_texpr ctx call.ctx) call.args in
    let args_mplaces =
      List.map
        (translate_opt_mplace (Some call.span) ctx.type_ctx.type_infos)
        call.args_places
    in
    List.map
      (fun (arg, mp) -> mk_opt_mplace_texpr mp arg)
      (List.combine args args_mplaces)
  in
  let dest_mplace =
    translate_opt_mplace (Some call.span) ctx.type_ctx.type_infos
      call.dest_place
  in
  (* Retrieve the function id, and register the function call in the context
     if necessary. *)
  let ctx, fun_id, effect_info, args, back_funs, dest_v =
    match call.call_id with
    | S.Fun (fid, call_id) ->
        (* Regular function call *)
        let fid_t = translate_fn_ptr_kind ctx fid in
        let func = Fun (FromLlbc (fid_t, None)) in
        (* Retrieve the effect information about this function (can fail,
         * takes a state as input, etc.) *)
        let effect_info = get_fun_effect_info ctx fid None None in
        (* Generate the variables for the backward functions returned by the forward
           function. *)
        let ctx, ignore_fwd_output, back_funs_map, back_funs =
          (* We need to compute the signatures of the backward functions. *)
          let sg = Option.get call.sg in
          let inst_sg = Option.get call.inst_sg in
          let decls_ctx = ctx.decls_ctx in
          let dsg =
            translate_inst_fun_sig_to_decomposed_fun_type (Some ctx.span)
              decls_ctx fid inst_sg
              (List.map (fun _ -> None) sg.inputs)
          in
          let back_tys = compute_back_tys_with_info dsg None in
          [%ltrace
            "back_tys:\n "
            ^ String.concat "\n"
                (List.map (pure_ty_to_string ctx)
                   (List.map snd (List.filter_map (fun x -> x) back_tys)))];
          (* Introduce variables for the backward functions *)
          (* Compute a proper basename for the variables *)
          let back_fun_name =
            let name =
              match fid with
              | FunId (FBuiltin fid) -> begin
                  match fid with
                  | BoxNew -> "box_new"
                  | ArrayRepeat -> "array_repeat"
                  | ArrayToSliceShared -> "to_slice_shared"
                  | ArrayToSliceMut -> "to_slice_mut"
                  | Index { is_array = _; mutability = RMut; is_range = false }
                    -> "index_mut"
                  | Index
                      { is_array = _; mutability = RShared; is_range = false }
                    -> "index_shared"
                  | Index { is_array = _; mutability = RMut; is_range = true }
                    -> "subslice_mut"
                  | Index
                      { is_array = _; mutability = RShared; is_range = true } ->
                      "subslice_shared"
                  | PtrFromParts RMut -> "ptr_from_parts_mut"
                  | PtrFromParts RShared -> "ptr_from_parts_shared"
                end
              | FunId (FRegular fid) | TraitMethod (_, _, fid) -> (
                  let decl =
                    FunDeclId.Map.find fid ctx.fun_ctx.llbc_fun_decls
                  in
                  match Collections.List.last decl.item_meta.name with
                  | PeIdent (s, _) -> s
                  | _ ->
                      (* We shouldn't get there *)
                      [%craise] decl.item_meta.span "Unexpected")
            in
            name ^ "_back"
          in
          let ctx, back_vars =
            fresh_opt_vars
              (List.map
                 (fun ty ->
                   match ty with
                   | None -> None
                   | Some (_back_sg, ty) ->
                       (* We insert a name for the variable only if the type
                          is an arrow type. If it is not, it means the backward
                          function is degenerate (it takes no inputs) so it is
                          not a function anymore but a value: it doesn't make
                          sense to use a name like "back...". *)
                       let name =
                         if is_arrow_ty ty then Some back_fun_name else None
                       in
                       Some (name, ty))
                 back_tys)
              ctx
          in
          let back_funs =
            List.filter_map
              (fun v ->
                match v with
                | None -> None
                | Some v -> Some (mk_tpattern_from_fvar v None))
              back_vars
          in
          let gids =
            List.map
              (fun (g : T.region_var_group) -> g.id)
              inst_sg.regions_hierarchy
          in
          let back_vars = List.map (Option.map mk_texpr_from_fvar) back_vars in
          let back_funs_map =
            RegionGroupId.Map.of_list (List.combine gids back_vars)
          in
          (ctx, dsg.fwd_info.ignore_output, Some back_funs_map, back_funs)
        in
        (* Compute the pattern for the destination *)
        let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
        let dest = mk_tpattern_from_fvar dest dest_mplace in
        let dest =
          (* Here there is something subtle: as we might ignore the output
             of the forward function (because it translates to unit) we do NOT
             necessarily introduce in the let-binding the variable to which we
             map the symbolic value which was introduced for the output of the
             function call. This would be problematic if later we need to
             translate this symbolic value, but we implemented
             {!symbolic_value_to_texpr} so that it doesn't perform any
             lookups if the symbolic value has type unit.
          *)
          let vars =
            if ignore_fwd_output then back_funs else dest :: back_funs
          in
          mk_simpl_tuple_pattern vars
        in
        (* Register the function call *)
        let ctx =
          bs_ctx_register_forward_call call_id call args back_funs_map ctx
        in
        (ctx, func, effect_info, args, back_funs, dest)
    | S.Unop E.Not -> (
        match args with
        | [ arg ] ->
            let ty =
              let lit_ty = ty_as_literal ctx.span arg.ty in
              match lit_ty with
              | TBool -> None
              | TInt int_ty -> Some (V.Signed int_ty)
              | TUInt int_ty -> Some (V.Unsigned int_ty)
              | _ -> [%craise] ctx.span "Unreachable"
            in
            let effect_info =
              {
                can_fail = false;
                stateful_group = false;
                stateful = false;
                can_diverge = false;
                is_rec = false;
              }
            in
            let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
            let dest = mk_tpattern_from_fvar dest dest_mplace in
            (ctx, Unop (Not ty), effect_info, args, [], dest)
        | _ -> [%craise] ctx.span "Unreachable")
    | S.Unop (E.Neg overflow) -> (
        match args with
        | [ arg ] ->
            let int_ty = ty_as_integer ctx.span arg.ty in
            (* Note that negation can lead to an overflow and thus fail (it
             * is thus monadic) *)
            let effect_info =
              {
                can_fail = overflow <> OWrap;
                stateful_group = false;
                stateful = false;
                can_diverge = false;
                is_rec = false;
              }
            in
            let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
            let dest = mk_tpattern_from_fvar dest dest_mplace in
            (ctx, Unop (Neg int_ty), effect_info, args, [], dest)
        | _ -> [%craise] ctx.span "Unreachable")
    | S.Unop (E.Cast cast_kind) -> begin
        match cast_kind with
        | CastScalar (src_ty, tgt_ty) ->
            (* Note that cast can fail *)
            let effect_info =
              {
                can_fail = not (Config.backend () = Lean);
                stateful_group = false;
                stateful = false;
                can_diverge = false;
                is_rec = false;
              }
            in
            let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
            let dest = mk_tpattern_from_fvar dest dest_mplace in
            (ctx, Unop (Cast (src_ty, tgt_ty)), effect_info, args, [], dest)
        | CastFnPtr _ -> [%craise] ctx.span "TODO: function casts"
        | CastUnsize _ ->
            (* We shouldn't get there: this case should have been detected before
               and handled in [translate_cast_unsize] *)
            [%internal_error] ctx.span
        | CastRawPtr _ -> [%craise] ctx.span "Unsupported: raw ptr casts"
        | CastTransmute _ -> [%craise] ctx.span "Unsupported: transmute"
      end
    | S.Unop E.PtrMetadata -> [%craise] ctx.span "Unsupported unop: PtrMetadata"
    | S.Binop binop -> (
        match args with
        | [ arg0; arg1 ] ->
            let int_ty0 = ty_as_integer ctx.span arg0.ty in
            let int_ty1 = ty_as_integer ctx.span arg1.ty in
            (match binop with
            (* The Rust compiler accepts bitshifts for any integer type combination for ty0, ty1 *)
            | E.Shl _ | E.Shr _ -> ()
            | _ -> [%sanity_check] ctx.span (int_ty0 = int_ty1));
            let effect_info =
              {
                can_fail = ExpressionsUtils.binop_can_fail binop;
                stateful_group = false;
                stateful = false;
                can_diverge = false;
                is_rec = false;
              }
            in
            let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
            let dest = mk_tpattern_from_fvar dest dest_mplace in
            (ctx, Binop (binop, int_ty0), effect_info, args, [], dest)
        | _ -> [%craise] ctx.span "Unreachable")
  in
  let func = { id = FunOrOp fun_id; generics } in
  let input_tys = (List.map (fun (x : texpr) -> x.ty)) args in
  let ret_ty =
    if effect_info.can_fail then mk_result_ty dest_v.ty else dest_v.ty
  in
  let func_ty = mk_arrows input_tys ret_ty in
  let func = { e = Qualif func; ty = func_ty } in
  let call_e = mk_apps ctx.span func args in
  (* This is a **hack** for [Box::new]: introduce backward functions
     which are the identity if we instantiated [Box::new] with types
     containing mutable borrows.

     We simply replace the function call with a tuple: (call to [Box::new], backward functions).

     TODO: make this general.
  *)
  let ctx, call_e =
    match call.call_id with
    | S.Fun (FunId (FBuiltin BoxNew), _) ->
        let ctx, back_funs_bodies =
          List.fold_left_map
            (fun ctx (f : tpattern) ->
              let ty, _ = dest_arrow_ty ctx.span f.ty in
              let ctx, v = fresh_var (Some "back") ty ctx in
              let pat = mk_tpattern_from_fvar v None in
              (ctx, mk_closed_lambda ctx.span pat (mk_texpr_from_fvar v)))
            ctx back_funs
        in
        (* We also need to change the type of the function *)
        let call_e =
          let call, args = destruct_apps call_e in
          match args with
          | [ x ] ->
              let call = { call with ty = mk_arrows [ x.ty ] x.ty } in
              mk_app ctx.span call x
          | _ -> [%internal_error] ctx.span
        in
        let call_e =
          mk_simpl_tuple_texpr ctx.span (call_e :: back_funs_bodies)
        in
        (ctx, call_e)
    | _ -> (ctx, call_e)
  in
  [%ldebug "call_e: " ^ texpr_to_string ctx call_e];
  [%ldebug
    "- dest_v.ty: "
    ^ pure_ty_to_string ctx dest_v.ty
    ^ "\n- call_e.ty: "
    ^ pure_ty_to_string ctx call_e.ty];
  [%sanity_check] ctx.span
    (let call_ty =
       if effect_info.can_fail then unwrap_result_ty ctx.span call_e.ty
       else call_e.ty
     in
     dest_v.ty = call_ty);
  (* Translate the next expression *)
  let next_e = translate_expr e ctx in
  (* Put together *)
  mk_closed_checked_let __FILE__ __LINE__ ctx effect_info.can_fail dest_v call_e
    next_e

and translate_cast_unsize (call : S.call) (e : S.expr) (ty0 : T.ty) (ty1 : T.ty)
    (ctx : bs_ctx) : texpr =
  (* Retrieve the information about the cast *)
  let info =
    InterpreterExpressions.cast_unsize_to_modified_fields ctx.span call.ctx ty0
      ty1
  in

  (* Process the arguments and the destination *)
  let dest_mplace =
    translate_opt_mplace (Some call.span) ctx.type_ctx.type_infos
      call.dest_place
  in
  let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
  let dest = mk_tpattern_from_fvar dest dest_mplace in
  let arg =
    match call.args with
    | [ arg ] -> arg
    | _ -> [%internal_error] ctx.span
  in
  let arg = tvalue_to_texpr ctx call.ctx arg in
  let arg_mp =
    translate_opt_mplace (Some call.span) ctx.type_ctx.type_infos
      (List.hd call.args_places)
  in
  let arg = mk_opt_mplace_texpr arg_mp arg in

  (* Small helper to create an [array_to_slice] expression *)
  let mk_array_to_slice (v : texpr) : texpr =
    let ty, n = ty_as_array ctx.span v.ty in
    let generics =
      { types = [ ty ]; const_generics = [ n ]; trait_refs = [] }
    in
    let func = { id = FunOrOp (Unop ArrayToSlice); generics } in
    let input_ty = v.ty in
    let ret_ty = TAdt (TBuiltin TSlice, mk_generic_args_from_types [ ty ]) in
    let func_ty = mk_arrows [ input_ty ] ret_ty in
    let func = { e = Qualif func; ty = func_ty } in
    mk_apps ctx.span func [ v ]
  in

  (* Create the cast expression *)
  let cast_expr =
    match info with
    | None ->
        (* This is a cast from a boxed array to a boxed slice: we simply insert
           a call to [array_to_slice] *)
        mk_array_to_slice arg
    | Some (adt_id, generics, field_id, ty0, _) ->
        (* This is cast between structures.
           We update the last field of the structure by using [array_to_slice] *)
        let adt_id = TAdtId adt_id in
        let generics = ctx_translate_fwd_generic_args ctx generics in
        let adt_ty = TAdt (adt_id, generics) in

        (* Create the field access expression *)
        let ty0 = ctx_translate_fwd_ty ctx ty0 in
        let field =
          let qualif : qualif = { id = Proj { adt_id; field_id }; generics } in
          let qualif_ty = mk_arrows [ adt_ty ] ty0 in
          let qualif = { e = Qualif qualif; ty = qualif_ty } in
          mk_app ctx.span qualif arg
        in

        (* Create the array to slice expression *)
        let nfield = mk_array_to_slice field in

        (* Create the field update expression *)
        let updt =
          let updt =
            StructUpdate
              {
                struct_id = adt_id;
                init = Some arg;
                updates = [ (field_id, nfield) ];
              }
          in
          let ty = arg.ty in
          { e = updt; ty }
        in
        updt
  in

  (* Create the let-binding *)
  let next_e = translate_expr e ctx in
  let monadic = false in
  mk_closed_checked_let __FILE__ __LINE__ ctx monadic dest cast_expr next_e

and translate_end_abstraction (ectx : C.eval_ctx) (abs : V.abs) (e : S.expr)
    (ctx : bs_ctx) : texpr =
  [%ltrace "abstraction kind: " ^ V.show_abs_kind abs.kind];
  match abs.kind with
  | V.SynthInput rg_id ->
      translate_end_abstraction_synth_input ectx abs e ctx rg_id
  | V.FunCall (call_id, rg_id) ->
      translate_end_abstraction_fun_call ectx abs e ctx call_id rg_id
  | V.SynthRet rg_id -> translate_end_abstraction_synth_ret ectx abs e ctx rg_id
  | V.Loop (loop_id, rg_id, abs_kind) ->
      translate_end_abstraction_loop ectx abs e ctx loop_id rg_id abs_kind
  | V.Identity | V.CopySymbolicValue ->
      translate_end_abstraction_identity ectx abs e ctx

and translate_end_abstraction_synth_input (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expr) (ctx : bs_ctx) (rg_id : T.RegionGroupId.id) : texpr =
  [%ltrace
    "- function: "
    ^ name_to_string ctx ctx.fun_decl.item_meta.name
    ^ "\n- rg_id: "
    ^ T.RegionGroupId.to_string rg_id
    ^ "\n- loop_id: "
    ^ Print.option_to_string Pure.LoopId.to_string ctx.loop_id
    ^ "\n- eval_ctx:\n"
    ^ eval_ctx_to_string ~span:(Some ctx.span) ectx
    ^ "\n- abs:\n" ^ abs_to_string ctx abs];

  (* When we end an input abstraction, this input abstraction gets back
     the borrows which it introduced in the context through the input
     values: by listing those values, we get the values which are given
     back by one of the backward functions we are synthesizing.

     Note that we don't support nested borrows for now: if we find
     an ended synthesized input abstraction, it must be the one corresponding
     to the backward function wer are synthesizing, it can't be the one
     for a parent backward function.
  *)
  let bid = Option.get ctx.bid in
  [%sanity_check] ctx.span (rg_id = bid);

  (* First, introduce the given back variables.

     We don't use the same given back variables if we translate a loop or
     the standard body of a function.
  *)
  let ctx, given_back_variables =
    let vars =
      if ctx.inside_loop then
        (* We are synthesizing a loop body *)
        let loop_id = Option.get ctx.loop_id in
        let loop = LoopId.Map.find loop_id ctx.loops in
        let tys = RegionGroupId.Map.find bid loop.back_outputs in
        List.map (fun ty -> (None, ty)) tys
      else
        (* Regular function body *)
        let back_sg = RegionGroupId.Map.find bid ctx.sg.fun_ty.back_sg in
        List.combine back_sg.output_names back_sg.outputs
    in
    let ctx, vars = fresh_vars vars ctx in
    ({ ctx with backward_outputs = Some vars }, vars)
  in

  (* Get the list of values consumed by the abstraction upon ending *)
  let consumed_values = abs_to_consumed ctx ectx abs in

  [%ltrace
    "\n- given back variables types:\n"
    ^ Print.list_to_string
        (fun (v : fvar) -> pure_ty_to_string ctx v.ty)
        given_back_variables
    ^ "\n\n- consumed values:\n"
    ^ Print.list_to_string
        (fun e -> texpr_to_string ctx e ^ " : " ^ pure_ty_to_string ctx e.ty)
        consumed_values];

  (* Prepare the let-bindings by introducing a match if necessary *)
  let given_back_variables =
    List.map (fun v -> mk_tpattern_from_fvar v None) given_back_variables
  in
  [%sanity_check] ctx.span
    (List.length given_back_variables = List.length consumed_values);
  let variables_values = List.combine given_back_variables consumed_values in

  (* Sanity check: the two lists match (same types) *)
  (* TODO: normalize the types *)
  if !Config.type_check_pure_code then
    List.iter
      (fun (var, v) ->
        [%sanity_check] ctx.span ((var : tpattern).ty = (v : texpr).ty))
      variables_values;
  (* Translate the next expression *)
  let next_e = translate_expr e ctx in
  (* Generate the assignemnts *)
  let monadic = false in
  mk_closed_checked_lets __FILE__ __LINE__ ctx monadic variables_values next_e

and translate_end_abstraction_fun_call (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expr) (ctx : bs_ctx) (call_id : V.FunCallId.id)
    (rg_id : T.RegionGroupId.id) : texpr =
  let call_info = V.FunCallId.Map.find call_id ctx.calls in
  let call = call_info.forward in
  let fun_id =
    match call.call_id with
    | S.Fun (fun_id, _) -> fun_id
    | Unop _ | Binop _ ->
        (* Those don't have backward functions *)
        [%craise] ctx.span "Unreachable"
  in
  let effect_info = get_fun_effect_info ctx fun_id None (Some rg_id) in
  (* Retrieve the values consumed upon ending the loans inside this
   * abstraction: those give us the remaining input values *)
  let back_inputs = abs_to_consumed ctx ectx abs in
  (* Retrieve the values given back by this function: those are the output
   * values. We rely on the fact that there are no nested borrows to use the
   * meta-place information from the input values given to the forward function
   * (we need to add [None] for the return avalue) *)
  let output_mpl =
    List.append
      (List.map
         (translate_opt_mplace (Some call.span) ctx.type_ctx.type_infos)
         call.args_places)
      [ None ]
  in
  let ctx, outputs = abs_to_given_back (Some output_mpl) abs ctx in
  (* Group the output values together *)
  let output = mk_simpl_tuple_pattern outputs in
  (* Retrieve the function id, and register the function call in the context
     if necessary. *)
  let ctx, func =
    bs_ctx_register_backward_call abs call_id rg_id back_inputs ctx
  in
  (* Translate the next expression *)
  let next_e ctx = translate_expr e ctx in
  (* Put everything together *)
  let inputs = back_inputs in
  let args_mplaces = List.map (fun _ -> None) inputs in
  let args =
    List.map
      (fun (arg, mp) -> mk_opt_mplace_texpr mp arg)
      (List.combine inputs args_mplaces)
  in
  (* The backward function might have been filtered if it does nothing
     (consumes unit and returns unit). *)
  match func with
  | None -> next_e ctx
  | Some func ->
      [%ltrace
        let args = List.map (texpr_to_string ctx) args in
        "func: " ^ texpr_to_string ctx func ^ "\nfunc type: "
        ^ pure_ty_to_string ctx func.ty
        ^ "\n\nargs:\n" ^ String.concat "\n" args];
      let call = mk_apps ctx.span func args in
      (* Introduce a match if necessary *)
      let ctx, (output, call) = decompose_let_match ctx (output, call) in
      (* Translate the next expression and construct the let *)
      mk_closed_checked_let __FILE__ __LINE__ ctx effect_info.can_fail output
        call (next_e ctx)

and translate_end_abstraction_identity (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expr) (ctx : bs_ctx) : texpr =
  (* We simply check that the abstraction only contains shared borrows/loans,
     and translate the next expression *)

  (* We can do this simply by checking that it consumes and gives back nothing *)
  let inputs = abs_to_consumed ctx ectx abs in
  let ctx, outputs = abs_to_given_back None abs ctx in
  [%sanity_check] ctx.span (inputs = []);
  [%sanity_check] ctx.span (outputs = []);

  (* Translate the next expression *)
  translate_expr e ctx

and translate_end_abstraction_synth_ret (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expr) (ctx : bs_ctx) (rg_id : T.RegionGroupId.id) : texpr =
  [%ltrace "Translating ended synthesis abstraction: " ^ abs_to_string ctx abs];
  (* If we end the abstraction which consumed the return value of the function
     we are synthesizing, we get back the borrows which were inside. Those borrows
     are actually input arguments of the backward function we are synthesizing.
     So we simply need to introduce proper let bindings.

     For instance:
     {[
       fn id<'a>(x : &'a mut u32) -> &'a mut u32 {
         x
       }
     ]}

     Upon ending the return abstraction for 'a, we get back the borrow for [x].
     This new value is the second argument of the backward function:
     {[
       let id_back x nx = nx
     ]}

     In practice, upon ending this abstraction we introduce a useless
     let-binding:
     {[
       let id_back x nx =
       let s = nx in // the name [s] is not important (only collision matters)
       ...
     ]}

     This let-binding later gets inlined, during a micro-pass.
  *)
  (* First, retrieve the list of variables used for the inputs for the
   * backward function *)
  let inputs = T.RegionGroupId.Map.find rg_id ctx.backward_inputs in
  [%ltrace
    "Consumed inputs: " ^ Print.list_to_string (fvar_to_string ctx) inputs];
  (* Retrieve the values consumed upon ending the loans inside this
   * abstraction: as there are no nested borrows, there should be none. *)
  let consumed = abs_to_consumed ctx ectx abs in
  [%cassert] ctx.span (consumed = []) "Nested borrows are not supported yet";
  (* Retrieve the values given back upon ending this abstraction - note that
     we don't provide meta-place information, because those assignments will
     be inlined anyway... *)
  [%ltrace "abs: " ^ abs_to_string ctx abs];
  let ctx, given_back = abs_to_given_back_no_mp abs ctx in
  [%ltrace
    "given back: " ^ Print.list_to_string (tpattern_to_string ctx) given_back];
  (* Link the inputs to those given back values - note that this also
     checks we have the same number of values, of course *)
  let given_back_inputs = List.combine given_back inputs in
  (* Sanity check *)
  List.iter
    (fun ((given_back, input) : tpattern * fvar) ->
      [%ltrace
        "- given_back ty: "
        ^ pure_ty_to_string ctx given_back.ty
        ^ "\n- sig input ty: "
        ^ pure_ty_to_string ctx input.ty];
      [%sanity_check] ctx.span (given_back.ty = input.ty))
    given_back_inputs;
  (* Prepare the let-bindings by introducing a match if necessary *)
  let given_back_inputs =
    List.map (fun (v, e) -> (v, mk_texpr_from_fvar e)) given_back_inputs
  in
  let ctx, given_back_inputs =
    List.fold_left_map decompose_let_match ctx given_back_inputs
  in
  (* Translate the next expression *)
  let next_e = translate_expr e ctx in
  (* Generate the assignments *)
  let monadic = false in
  mk_closed_checked_lets __FILE__ __LINE__ ctx monadic given_back_inputs next_e

and translate_end_abstraction_loop (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expr) (ctx : bs_ctx) (loop_id : V.LoopId.id)
    (rg_id : T.RegionGroupId.id option) (abs_kind : V.loop_abs_kind) : texpr =
  let vloop_id = loop_id in
  let loop_id = V.LoopId.Map.find loop_id ctx.loop_ids_map in
  [%sanity_check] ctx.span (loop_id = Option.get ctx.loop_id);
  let rg_id = Option.get rg_id in
  (* There are two cases depending on the [abs_kind] (whether this is a
     synth input or a regular loop call) *)
  match abs_kind with
  | V.LoopSynthInput ->
      (* Actually the same case as [SynthInput] *)
      translate_end_abstraction_synth_input ectx abs e ctx rg_id
  | V.LoopCall -> (
      (* We need to introduce a call to the backward function corresponding
         to a forward call which happened earlier *)
      let fun_id = T.FRegular ctx.fun_decl.def_id in
      let effect_info =
        get_fun_effect_info ctx (FunId fun_id) (Some vloop_id) (Some rg_id)
      in
      let loop_info = LoopId.Map.find loop_id ctx.loops in
      (* Retrieve the additional backward inputs. Note that those are actually
         the backward inputs of the function we are synthesizing (and that we
         need to *transmit* to the loop backward function): they are not the
         values consumed upon ending the abstraction (i.e., we don't use
         [abs_to_consumed]) *)
      let back_inputs_vars =
        T.RegionGroupId.Map.find rg_id ctx.backward_inputs
      in
      let inputs = List.map mk_texpr_from_fvar back_inputs_vars in
      (* Retrieve the values given back by this function *)
      let ctx, outputs = abs_to_given_back None abs ctx in
      (* Group the output values together: first the updated inputs *)
      let output = mk_simpl_tuple_pattern outputs in
      (* Translate the next expression *)
      let next_e ctx = translate_expr e ctx in
      (* Put everything together *)
      let args_mplaces = List.map (fun _ -> None) inputs in
      let args =
        List.map
          (fun (arg, mp) -> mk_opt_mplace_texpr mp arg)
          (List.combine inputs args_mplaces)
      in
      (* Create the expression for the function:
         - it is either a call to a top-level function, if we split the
           forward/backward functions
         - or a call to the variable we introduced for the backward function,
           if we merge the forward/backward functions *)
      let func =
        RegionGroupId.Map.find rg_id (Option.get loop_info.back_funs)
      in
      (* We may have filtered the backward function elsewhere if it doesn't
         do anything (doesn't consume anything and doesn't return anything) *)
      match func with
      | None -> next_e ctx
      | Some func ->
          let call = mk_apps ctx.span func args in
          (* Create the let-binding - we may have to introduce a match *)
          let ctx, (output, call) = decompose_let_match ctx (output, call) in

          let next_e = next_e ctx in

          (* Add meta-information - this is slightly hacky: we look at the
             values consumed by the abstraction (note that those come from
             *before* we applied the fixed-point context) and use them to
             guide the naming of the output vars. Because of this, the meta
             information might reference *some variables which are not in
             the context*. This forces us to cleanup the meta-data later
             to make sure the expressions are well-formed.

             Also, we need to convert the backward outputs from patterns to
             variables.

             Finally, in practice, this works well only for loop bodies:
             we do this only in this case.
             TODO: improve the heuristics, to give weight to the hints for
             instance.
          *)
          let next_e =
            if ctx.inside_loop && Config.allow_unbound_variables_in_metadata
            then
              let consumed_values = abs_to_consumed ctx ectx abs in
              let var_values = List.combine outputs consumed_values in
              let var_values =
                List.filter_map
                  (fun ((var, v) : tpattern * _) ->
                    match var.Pure.pat with
                    | POpen (var, _) -> Some (var, v)
                    | PBound _ -> [%internal_error] ctx.span
                    | _ -> None)
                  var_values
              in
              let vars, values = List.split var_values in
              mk_emeta_symbolic_assignments vars values next_e
            else next_e
          in

          mk_closed_checked_let __FILE__ __LINE__ ctx effect_info.can_fail
            output call next_e)

and translate_global_eval (gid : A.GlobalDeclId.id) (generics : T.generic_args)
    (sval : V.symbolic_value) (e : S.expr) (ctx : bs_ctx) : texpr =
  let ctx, var = fresh_var_for_symbolic_value sval ctx in
  let decl = A.GlobalDeclId.Map.find gid ctx.decls_ctx.crate.global_decls in
  let generics = ctx_translate_fwd_generic_args ctx generics in
  let global_expr = { id = Global gid; generics } in
  (* We use translate_fwd_ty to translate the global type *)
  let ty = ctx_translate_fwd_ty ctx decl.ty in
  let gval = { e = Qualif global_expr; ty } in
  let e = translate_expr e ctx in
  mk_closed_checked_let __FILE__ __LINE__ ctx false
    (mk_tpattern_from_fvar var None)
    gval e

and translate_assertion (ectx : C.eval_ctx) (v : V.tvalue) (e : S.expr)
    (ctx : bs_ctx) : texpr =
  let next_e = translate_expr e ctx in
  let monadic = true in
  let v = tvalue_to_texpr ctx ectx v in
  let args = [ v ] in
  let func =
    { id = FunOrOp (Fun (Pure Assert)); generics = empty_generic_args }
  in
  let func_ty = mk_arrow (TLiteral TBool) (mk_result_ty mk_unit_ty) in
  let func = { e = Qualif func; ty = func_ty } in
  let assertion = mk_apps ctx.span func args in
  mk_closed_checked_let __FILE__ __LINE__ ctx monadic
    (mk_dummy_pattern mk_unit_ty)
    assertion next_e

and translate_expansion (p : S.mplace option) (sv : V.symbolic_value)
    (exp : S.expansion) (ctx : bs_ctx) : texpr =
  [%ldebug "expansion:\n" ^ bs_ctx_expansion_to_string ctx sv exp];
  (* Translate the scrutinee *)
  let scrutinee = symbolic_value_to_texpr ctx sv in
  let scrutinee_mplace =
    translate_opt_mplace (Some ctx.span) ctx.type_ctx.type_infos p
  in
  (* Translate the branches *)
  match exp with
  | ExpandNoBranch (sexp, e) -> (
      match sexp with
      | V.SeLiteral _ ->
          (* We do not *register* symbolic expansions to literal
             values in the symbolic ADT *)
          [%craise] ctx.span "Unreachable"
      | SeMutRef (_, nsv) | SeSharedRef (_, nsv) ->
          (* The (mut/shared) borrow type is extracted to identity: we thus simply
             introduce an reassignment *)
          let ctx, var = fresh_var_for_symbolic_value nsv ctx in
          let next_e = translate_expr e ctx in
          let monadic = false in
          mk_closed_checked_let __FILE__ __LINE__ ctx monadic
            (mk_tpattern_from_fvar var None)
            (mk_opt_mplace_texpr scrutinee_mplace scrutinee)
            next_e
      | SeAdt _ ->
          (* Should be in the [ExpandAdt] case *)
          [%craise] ctx.span "Unreachable")
  | ExpandAdt branches -> (
      (* We don't do the same thing if there is a branching or not *)
      match branches with
      | [] -> [%craise] ctx.span "Unreachable"
      | [ (variant_id, svl, branch) ]
        when not
               (TypesUtils.ty_is_custom_adt sv.V.sv_ty
               && !Config.always_deconstruct_adts_with_matches) ->
          (* There is exactly one branch: no branching.

             We can decompose the ADT value with a let-binding, unless
             the backend doesn't support this (see {!Config.always_deconstruct_adts_with_matches}):
             we *ignore* this branch (and go to the next one) if the ADT is a custom
             adt, and [always_deconstruct_adts_with_matches] is true.
          *)
          translate_ExpandAdt_one_branch sv scrutinee scrutinee_mplace
            variant_id svl branch ctx
      | branches ->
          let translate_branch (variant_id : T.VariantId.id option)
              (svl : V.symbolic_value list) (branch : S.expr) : match_branch =
            let ctx, vars = fresh_vars_for_symbolic_values svl ctx in
            let vars = List.map (fun x -> mk_tpattern_from_fvar x None) vars in
            let pat_ty = scrutinee.ty in
            let pat = mk_adt_pattern pat_ty variant_id vars in
            let branch = translate_expr branch ctx in
            close_branch ctx.span pat branch
          in
          let branches =
            List.map (fun (vid, svl, e) -> translate_branch vid svl e) branches
          in
          let e =
            Switch
              (mk_opt_mplace_texpr scrutinee_mplace scrutinee, Match branches)
          in
          (* There should be at least one branch *)
          let branch = List.hd branches in
          let ty = branch.branch.ty in
          (* Sanity check *)
          [%sanity_check] ctx.span
            (List.for_all (fun br -> br.branch.ty = ty) branches);
          (* Return *)
          { e; ty })
  | ExpandBool (true_e, false_e) ->
      (* We don't need to update the context: we don't introduce any
         new values/variables *)
      let true_e = translate_expr true_e ctx in
      let false_e = translate_expr false_e ctx in
      let e =
        Switch
          (mk_opt_mplace_texpr scrutinee_mplace scrutinee, If (true_e, false_e))
      in
      let ty = true_e.ty in
      [%ltrace
        "true_e.ty: "
        ^ pure_ty_to_string ctx true_e.ty
        ^ "\n\nfalse_e.ty: "
        ^ pure_ty_to_string ctx false_e.ty];
      [%ltrace
        "true_e: " ^ texpr_to_string ctx true_e ^ " \n\nfalse_e: "
        ^ texpr_to_string ctx false_e];
      [%sanity_check] ctx.span (ty = false_e.ty);
      { e; ty }
  | ExpandInt (int_ty, branches, otherwise) ->
      let translate_branch ((v, branch_e) : V.scalar_value * S.expr) :
          match_branch =
        (* We don't need to update the context: we don't introduce any
           new values/variables *)
        let branch = translate_expr branch_e ctx in
        let pat = mk_tpattern_from_literal (VScalar v) in
        close_branch ctx.span pat branch
      in
      let branches = List.map translate_branch branches in
      let otherwise = translate_expr otherwise ctx in
      let pat_ty = TLiteral (TypesUtils.integer_as_literal int_ty) in
      let otherwise_pat : tpattern = { pat = PDummy; ty = pat_ty } in
      let otherwise : match_branch =
        { pat = otherwise_pat; branch = otherwise }
      in
      let all_branches = List.append branches [ otherwise ] in
      let e =
        Switch
          (mk_opt_mplace_texpr scrutinee_mplace scrutinee, Match all_branches)
      in
      let ty = otherwise.branch.ty in
      [%sanity_check] ctx.span
        (List.for_all (fun (br : match_branch) -> br.branch.ty = ty) branches);
      { e; ty }

(* Translate and [ExpandAdt] when there is no branching (i.e., one branch).

   We generate something of the shape:
   {[
     let Cons x0 ... xn = y in
     ...
   ]}
*)
and translate_ExpandAdt_one_branch (sv : V.symbolic_value) (scrutinee : texpr)
    (scrutinee_mplace : mplace option) (variant_id : variant_id option)
    (svl : V.symbolic_value list) (branch : S.expr) (ctx : bs_ctx) : texpr =
  (* TODO: always introduce a match, and use micro-passes to turn the
     the match into a let? *)
  let type_id, _ = TypesUtils.ty_as_adt sv.V.sv_ty in
  let ctx, vars = fresh_vars_for_symbolic_values svl ctx in
  let branch = translate_expr branch ctx in
  match type_id with
  | TAdtId _ ->
      let lvars = List.map (fun v -> mk_tpattern_from_fvar v None) vars in
      let lv = mk_adt_pattern scrutinee.ty variant_id lvars in
      let monadic = false in
      mk_closed_checked_let __FILE__ __LINE__ ctx monadic lv
        (mk_opt_mplace_texpr scrutinee_mplace scrutinee)
        branch
  | TTuple ->
      let vars = List.map (fun x -> mk_tpattern_from_fvar x None) vars in
      let monadic = false in
      mk_closed_checked_let __FILE__ __LINE__ ctx monadic
        (mk_simpl_tuple_pattern vars)
        (mk_opt_mplace_texpr scrutinee_mplace scrutinee)
        branch
  | TBuiltin TBox ->
      (* There should be exactly one variable *)
      let var =
        match vars with
        | [ v ] -> v
        | _ -> [%craise] ctx.span "Unreachable"
      in
      (* We simply introduce an assignment - the box type is the
       * identity when extracted ([box a = a]) *)
      let monadic = false in
      mk_closed_checked_let __FILE__ __LINE__ ctx monadic
        (mk_tpattern_from_fvar var None)
        (mk_opt_mplace_texpr scrutinee_mplace scrutinee)
        branch
  | TBuiltin (TArray | TSlice | TStr) ->
      (* We can't expand those values: we can access the fields only
       * through the functions provided by the API (note that we don't
       * know how to expand values like vectors or arrays, because they have a variable number
       * of fields!) *)
      [%craise] ctx.span "Attempt to expand a non-expandable value"

and translate_intro_symbolic (ectx : C.eval_ctx) (p : S.mplace option)
    (sv : V.symbolic_value) (v : S.value_aggregate) (e : S.expr) (ctx : bs_ctx)
    : texpr =
  [%ltrace "- value aggregate: " ^ S.show_value_aggregate v];
  let mplace = translate_opt_mplace (Some ctx.span) ctx.type_ctx.type_infos p in

  (* Introduce a fresh variable for the symbolic value. *)
  let ctx, var = fresh_var_for_symbolic_value sv ctx in

  (* Translate the next expression *)
  let next_e = translate_expr e ctx in

  (* Translate the value: there are several cases, depending on whether this
     is a "regular" let-binding, an array aggregate, a const generic or
     a trait associated constant.
  *)
  let v =
    match v with
    | VaSingleValue v -> tvalue_to_texpr ctx ectx v
    | VaArray values ->
        (* We use a struct update to encode the array aggregate, in order
           to preserve the structure and allow generating code of the shape
           `[x0, ...., xn]` *)
        let values = List.map (tvalue_to_texpr ctx ectx) values in
        let values = FieldId.mapi (fun fid v -> (fid, v)) values in
        let su : struct_update =
          { struct_id = TBuiltin TArray; init = None; updates = values }
        in
        { e = StructUpdate su; ty = var.ty }
    | VaCgValue cg_id -> { e = CVar cg_id; ty = var.ty }
    | VaTraitConstValue (trait_ref, const_name) ->
        let type_infos = ctx.type_ctx.type_infos in
        let trait_ref =
          translate_fwd_trait_ref (Some ctx.span) type_infos trait_ref
        in
        let qualif_id = TraitConst (trait_ref, const_name) in
        let qualif = { id = qualif_id; generics = empty_generic_args } in
        { e = Qualif qualif; ty = var.ty }
  in

  (* Make the let-binding *)
  let monadic = false in
  let var = mk_tpattern_from_fvar var mplace in
  mk_closed_checked_let __FILE__ __LINE__ ctx monadic var v next_e

and translate_forward_end (return_value : (C.eval_ctx * V.tvalue) option)
    (ectx : C.eval_ctx)
    (loop_sid_maps :
      (V.tvalue S.symbolic_value_id_map
      * V.symbolic_value_id S.symbolic_value_id_map)
      option) (fwd_e : S.expr) (back_e : S.expr S.region_group_id_map)
    (ctx : bs_ctx) : texpr =
  (* Register the consumed mutable borrows to compute default values *)
  let ctx =
    match return_value with
    | None -> ctx
    | Some (ectx, v) -> register_consumed_mut_borrows ectx ctx v
  in

  let translate_one_end ctx (bid : RegionGroupId.id option) =
    let ctx = { ctx with bid } in
    let ctx, e, finish =
      match bid with
      | None ->
          (* We are translating the forward function - nothing to do *)
          (ctx, fwd_e, fun e -> e)
      | Some bid ->
          (* We need to wrap the expression in a lambda, which introduces the
           additional inputs of the backward function.
          *)
          let ctx =
            (* We need to introduce fresh variables for the additional inputs,
               because they are locally introduced in a lambda. *)
            let back_sg = RegionGroupId.Map.find bid ctx.sg.fun_ty.back_sg in
            let ctx, backward_inputs = fresh_vars back_sg.inputs ctx in
            (* Update the functions mk_return and mk_panic *)
            let effect_info = back_sg.effect_info in
            let mk_return ctx v =
              assert (v = None);
              let output =
                (* Group the variables in which we stored the values we need to give back.
                   See the explanations for the [SynthInput] case in [translate_end_abstraction] *)
                let backward_outputs = Option.get ctx.backward_outputs in
                let field_values =
                  List.map mk_texpr_from_fvar backward_outputs
                in
                mk_simpl_tuple_texpr ctx.span field_values
              in
              (* Wrap in a result if the backward function can fail *)
              if effect_info.can_fail then mk_result_ok_texpr ctx.span output
              else output
            in
            let mk_panic =
              (* TODO: we should use a [Fail] function *)
              let mk_output output_ty =
                mk_result_fail_texpr_with_error_id ctx.span error_failure_id
                  output_ty
              in
              let output =
                mk_simpl_tuple_ty
                  (RegionGroupId.Map.find bid ctx.sg.fun_ty.back_sg).outputs
              in
              mk_output output
            in
            {
              ctx with
              backward_inputs =
                RegionGroupId.Map.add bid backward_inputs ctx.backward_inputs;
              mk_return = Some mk_return;
              mk_panic = Some mk_panic;
            }
          in

          let e = T.RegionGroupId.Map.find bid back_e in
          let finish e =
            (* Wrap in lambdas if necessary *)
            let inputs = RegionGroupId.Map.find bid ctx.backward_inputs in
            let places = List.map (fun _ -> None) inputs in
            mk_closed_lambdas_from_fvars ctx.span inputs places e
          in
          (ctx, e, finish)
    in
    let e = translate_expr e ctx in
    finish e
  in

  (* We need to translate the end of the forward
     function (this is the value we will return) and generate the bodies
     of the backward functions (which we will also return).

     Update the current state with the additional state received by the backward
     function, if needs be, and lookup the proper expression.
  *)
  let translate_end ctx =
    (* Compute the output of the forward function *)
    let fwd_effect_info = ctx.sg.fun_ty.fwd_info.effect_info in
    let ctx, pure_fwd_var = fresh_var None ctx.sg.fun_ty.fwd_output ctx in
    let fwd_e = translate_one_end ctx None in

    (* If we reached a loop: if we are *inside* a loop, we need to ignore the
       backward functions which are not associated to region abstractions.
    *)
    let keep_rg_ids =
      match ctx.loop_id with
      | None -> None
      | Some loop_id ->
          if ctx.inside_loop then
            let loop_info = LoopId.Map.find loop_id ctx.loops in
            Some
              (RegionGroupId.Set.of_list
                 (RegionGroupId.Map.keys loop_info.back_outputs))
          else None
    in
    let keep_rg_id =
      match keep_rg_ids with
      | None -> fun _ -> true
      | Some ids -> fun id -> RegionGroupId.Set.mem id ids
    in

    let back_el =
      List.map
        (fun ((gid, _) : RegionGroupId.id * back_sg_info) ->
          if keep_rg_id gid then Some (translate_one_end ctx (Some gid))
          else None)
        (RegionGroupId.Map.bindings ctx.sg.fun_ty.back_sg)
    in

    (* Compute whether the backward expressions should be evaluated straight
       away or not (i.e., if we should bind them with monadic let-bindings
       or not). We evaluate them straight away if they can fail and have no
       inputs. *)
    let evaluate_backs =
      List.map
        (fun ((rg_id, sg) : RegionGroupId.id * back_sg_info) ->
          if keep_rg_id rg_id then
            Some
              (if !Config.simplify_merged_fwd_backs then
                 sg.inputs = [] && sg.effect_info.can_fail
               else false)
          else None)
        (RegionGroupId.Map.bindings ctx.sg.fun_ty.back_sg)
    in

    (* Introduce variables for the backward functions.
       We lookup the LLBC definition in an attempt to derive pretty names
       for those functions. *)
    let _, back_vars = fresh_back_vars_for_current_fun ctx keep_rg_ids in

    (* Create the return expressions *)
    let vars =
      let back_vars = List.filter_map (fun x -> x) back_vars in
      if ctx.sg.fun_ty.fwd_info.ignore_output then back_vars
      else pure_fwd_var :: back_vars
    in
    let vars = List.map mk_texpr_from_fvar vars in
    let ret = mk_simpl_tuple_texpr ctx.span vars in
    let ret = mk_result_ok_texpr ctx.span ret in

    (* Introduce all the let-bindings *)

    (* Combine:
       - the backward variables
       - whether we should evaluate the expression for the backward function
         (i.e., should we use a monadic let-binding or not - we do if the
         backward functions don't have inputs and can fail)
       - the expressions for the backward functions
    *)
    let back_vars_els =
      List.filter_map
        (fun (v, (eval, el)) ->
          match v with
          | None -> None
          | Some v -> Some (v, Option.get eval, Option.get el))
        (List.combine back_vars (List.combine evaluate_backs back_el))
    in
    let e =
      List.fold_right
        (fun (var, evaluate, back_e) e ->
          mk_closed_checked_let __FILE__ __LINE__ ctx evaluate
            (mk_tpattern_from_fvar var None)
            back_e e)
        back_vars_els ret
    in

    (* Bind the expression for the forward output *)
    let pat = mk_tpattern_from_fvar pure_fwd_var None in
    mk_closed_checked_let __FILE__ __LINE__ ctx fwd_effect_info.can_fail pat
      fwd_e e
  in

  (* If we are (re-)entering a loop, we need to introduce a call to the
     forward translation of the loop. *)
  match loop_sid_maps with
  | None ->
      (* "Regular" case: we reached a return *)
      translate_end ctx
  | Some (loop_input_values_map, refreshed_sids) ->
      (* Loop *)
      let loop_id = Option.get ctx.loop_id in

      (* Lookup the loop information *)
      let loop_info = LoopId.Map.find loop_id ctx.loops in

      [%ltrace
        "- loop_input_values_map:\n"
        ^ V.SymbolicValueId.Map.show (tvalue_to_string ctx)
            loop_input_values_map
        ^ "\n- loop_info.input_svl:\n"
        ^ Print.list_to_string
            (symbolic_value_to_string ctx)
            loop_info.input_svl];

      (* Translate the input values *)
      let loop_input_values =
        List.map
          (fun (sv : V.symbolic_value) ->
            [%ltrace
              "looking up input_svl: " ^ V.SymbolicValueId.to_string sv.V.sv_id];
            V.SymbolicValueId.Map.find sv.V.sv_id loop_input_values_map)
          loop_info.input_svl
      in
      [%ltrace
        "loop_input_values: "
        ^ String.concat "," (List.map (tvalue_to_string ctx) loop_input_values)];
      let args = List.map (tvalue_to_texpr ctx ectx) loop_input_values in

      (* Lookup the effect info for the loop function *)
      let fid = T.FRegular ctx.fun_decl.def_id in
      let effect_info = get_fun_effect_info ctx (FunId fid) None ctx.bid in

      (* Introduce a fresh output value for the forward function *)
      let ctx, fwd_output, output_pat =
        if ctx.sg.fun_ty.fwd_info.ignore_output then
          (* Note that we still need the forward output (which is unit),
             because even though the loop function will ignore the forward output,
             the forward expression will still compute an output (which
             will have type unit - otherwise we can't ignore it). *)
          (ctx, mk_unit_rvalue, [])
        else
          let ctx, output_var = fresh_var None ctx.sg.fun_ty.fwd_output ctx in
          ( ctx,
            mk_texpr_from_fvar output_var,
            [ mk_tpattern_from_fvar output_var None ] )
      in

      (* Introduce fresh variables for the backward functions of the loop.

         For now, the backward functions of the loop are the same as the
         backward functions of the outer function.
      *)
      let ctx, back_funs_map, back_funs =
        (* We need to filter the region groups which are not linked to region
           abstractions appearing in the loop, so as not to introduce unnecessary
           backward functions. *)
        let keep_rg_ids =
          RegionGroupId.Set.of_list
            (RegionGroupId.Map.keys loop_info.back_outputs)
        in
        let ctx, back_vars =
          fresh_back_vars_for_current_fun ctx (Some keep_rg_ids)
        in
        let back_funs =
          List.filter_map
            (fun v ->
              match v with
              | None -> None
              | Some v -> Some (mk_tpattern_from_fvar v None))
            back_vars
        in
        let gids = RegionGroupId.Map.keys ctx.sg.fun_ty.back_sg in
        let back_funs_map =
          RegionGroupId.Map.of_list
            (List.combine gids
               (List.map (Option.map mk_texpr_from_fvar) back_vars))
        in
        (ctx, Some back_funs_map, back_funs)
      in

      (* Introduce patterns *)
      let args, ctx, out_pats =
        (* Add the returned backward functions (they might be empty) *)
        let output_pat = mk_simpl_tuple_pattern (output_pat @ back_funs) in
        (List.concat [ args ], ctx, [ output_pat ])
      in

      (* Update the loop information in the context *)
      let loop_info =
        {
          loop_info with
          forward_inputs = Some args;
          forward_output_no_state_no_result = Some fwd_output;
          back_funs = back_funs_map;
        }
      in
      let ctx =
        { ctx with loops = LoopId.Map.add loop_id loop_info ctx.loops }
      in

      (* Introduce the refreshed input symbolic values.

         TODO: remove. We used to need them, but we don't anymore, though we
         have to make sure they are in the context.
      *)
      let ctx, _ =
        List.fold_left_map
          (fun ctx (sid, nid) ->
            let sv_ty =
              (SymbolicValueId.Map.find sid loop_input_values_map).ty
            in
            let sv : V.symbolic_value = { sv_ty; sv_id = sid } in
            let nsv : V.symbolic_value = { sv_ty; sv_id = nid } in
            let ctx, nsv = fresh_var_for_symbolic_value nsv ctx in
            let sv = symbolic_value_to_texpr ctx sv in
            (ctx, (PureUtils.mk_tpattern_from_fvar nsv None, sv)))
          ctx
          (SymbolicValueId.Map.bindings refreshed_sids)
      in

      (* Translate the end of the function *)
      let next_e = translate_end ctx in

      (* Introduce the call to the loop forward function in the generated AST *)
      let out_pat = mk_simpl_tuple_pattern out_pats in

      let loop_call =
        let fun_id = Fun (FromLlbc (FunId fid, Some loop_id)) in
        let func = { id = FunOrOp fun_id; generics = loop_info.generics } in
        let input_tys = (List.map (fun (x : texpr) -> x.ty)) args in
        let ret_ty =
          if effect_info.can_fail then mk_result_ty out_pat.ty else out_pat.ty
        in
        let func_ty = mk_arrows input_tys ret_ty in
        let func = { e = Qualif func; ty = func_ty } in
        let call = mk_apps ctx.span func args in
        call
      in

      (* Create the let expression with the loop call *)
      mk_closed_checked_let __FILE__ __LINE__ ctx effect_info.can_fail out_pat
        loop_call next_e

and translate_loop (loop : S.loop) (ctx : bs_ctx) : texpr =
  let loop_id = V.LoopId.Map.find loop.loop_id ctx.loop_ids_map in

  (* Translate the loop inputs - some inputs are symbolic values already
     in the context, some inputs are introduced by the loop fixed point:
     we need to introduce fresh variables for those. *)
  (* First introduce fresh variables for the new inputs *)
  let ctx =
    (* We have to filter the list of symbolic values, to remove the not fresh ones *)
    let svl =
      List.filter
        (fun (sv : V.symbolic_value) ->
          V.SymbolicValueId.Set.mem sv.sv_id loop.fresh_svalues)
        loop.input_svalues
    in
    [%ltrace
      "- input_svalues: "
      ^ (Print.list_to_string (symbolic_value_to_string ctx)) loop.input_svalues
      ^ "\n- filtered svl: "
      ^ (Print.list_to_string (symbolic_value_to_string ctx)) svl
      ^ "\n- rg_to_abs:\n"
      ^ T.RegionGroupId.Map.show
          (Print.list_to_string (pure_ty_to_string ctx))
          loop.rg_to_given_back_tys];
    let ctx, _ = fresh_vars_for_symbolic_values svl ctx in
    ctx
  in

  (* Sanity check: all the non-fresh symbolic values are in the context *)
  [%sanity_check] ctx.span
    (List.for_all
       (fun (sv : V.symbolic_value) ->
         V.SymbolicValueId.Map.mem sv.sv_id ctx.sv_to_var)
       loop.input_svalues);

  (* Translate the loop inputs *)
  let inputs =
    List.map
      (fun (sv : V.symbolic_value) ->
        V.SymbolicValueId.Map.find sv.V.sv_id ctx.sv_to_var)
      loop.input_svalues
  in

  (* Compute the backward outputs *)
  let rg_to_given_back_tys = loop.rg_to_given_back_tys in

  (* The output type of the loop function *)
  let fwd_effect_info =
    { ctx.sg.fun_ty.fwd_info.effect_info with is_rec = true }
  in
  let back_effect_infos, output_ty =
    (* The loop backward functions consume the same additional inputs as the parent
       function, but have custom outputs *)
    [%ltrace
      let back_sgs = RegionGroupId.Map.bindings ctx.sg.fun_ty.back_sg in
      "- back_sgs: "
      ^ (Print.list_to_string
           (Print.pair_to_string RegionGroupId.to_string show_back_sg_info))
          back_sgs
      ^ "\n- given_back_tys: "
      ^ (RegionGroupId.Map.to_string None
           (Print.list_to_string (pure_ty_to_string ctx)))
          rg_to_given_back_tys];
    let back_info_tys =
      List.map
        (fun ((rg_id, given_back) : RegionGroupId.id * ty list) ->
          (* Lookup the effect information about the parent function region group
             associated to this loop region abstraction *)
          let back_sg = RegionGroupId.Map.find rg_id ctx.sg.fun_ty.back_sg in
          (* Remark: the effect info of the backward function for the loop
             is almost the same as for the backward function of the parent function.
             Quite importantly, the fact that the function is stateful and/or can fail
             mostly depends on whether it has inputs or not, and the backward functions
             for the loops have the same inputs as the backward functions for the parent
             function.
          *)
          let effect_info = back_sg.effect_info in
          (* Compute the input/output types *)
          let inputs = List.map snd back_sg.inputs in
          let outputs = given_back in
          (* Filter if necessary *)
          let ty =
            if !Config.simplify_merged_fwd_backs && inputs = [] && outputs = []
            then None
            else
              let output = mk_simpl_tuple_ty outputs in
              let output =
                mk_back_output_ty_from_effect_info effect_info inputs output
              in
              let ty = mk_arrows inputs output in
              Some ty
          in
          ((rg_id, effect_info), ty))
        (RegionGroupId.Map.bindings rg_to_given_back_tys)
    in
    let back_info = List.map fst back_info_tys in
    let back_info = RegionGroupId.Map.of_list back_info in
    let back_tys = List.filter_map snd back_info_tys in
    let output =
      let output =
        if ctx.sg.fun_ty.fwd_info.ignore_output then back_tys
        else ctx.sg.fun_ty.fwd_output :: back_tys
      in
      let output = mk_simpl_tuple_ty output in
      let effect_info = ctx.sg.fun_ty.fwd_info.effect_info in
      if effect_info.can_fail then mk_result_ty output else output
    in
    (back_info, output)
  in

  (* Add the loop information in the context *)
  let ctx =
    [%sanity_check] ctx.span (not (LoopId.Map.mem loop_id ctx.loops));

    (* Note that we will retrieve the input values later in the [ForwardEnd]
       (and will introduce the outputs at that moment, together with the actual
       call to the loop forward function) *)
    let generics =
      let { types; const_generics; trait_clauses } = ctx.sg.generics in
      let types =
        List.map (fun (ty : T.type_param) -> TVar (Free ty.T.index)) types
      in
      let const_generics =
        List.map
          (fun (cg : T.const_generic_var) -> T.CgVar (Free cg.T.index))
          const_generics
      in
      let trait_refs =
        List.map
          (fun (c : trait_clause) ->
            let trait_decl_ref =
              { trait_decl_id = c.trait_id; decl_generics = c.generics }
            in
            { trait_id = Clause (Free c.clause_id); trait_decl_ref })
          trait_clauses
      in
      { types; const_generics; trait_refs }
    in

    (* Update the helpers to translate the fail and return expressions *)
    let mk_panic =
      (* Note that we reuse the effect information from the parent function *)
      let effect_info = ctx_get_effect_info ctx in
      let back_tys =
        (* We need to filter the region abstractions which are not used by the
         loop - TODO: update this, it will become useless once we allow non
         terminal loops.
      *)
        let fun_ty = ctx.sg.fun_ty in
        let fun_ty =
          {
            fun_ty with
            back_sg =
              RegionGroupId.Map.filter
                (fun rg_id _ ->
                  RegionGroupId.Map.mem rg_id rg_to_given_back_tys)
                fun_ty.back_sg;
          }
        in
        compute_back_tys fun_ty None
      in
      let back_tys = List.filter_map (fun x -> x) back_tys in
      let tys =
        if ctx.sg.fun_ty.fwd_info.ignore_output then back_tys
        else ctx.sg.fun_ty.fwd_output :: back_tys
      in
      let output_ty = mk_simpl_tuple_ty tys in
      if effect_info.stateful then
        (* Create the [Fail] value *)
        let ret_ty = output_ty in
        let ret_v =
          mk_result_fail_texpr_with_error_id ctx.span error_failure_id ret_ty
        in
        ret_v
      else
        mk_result_fail_texpr_with_error_id ctx.span error_failure_id output_ty
    in
    let mk_return ctx v =
      match v with
      | None -> raise (Failure "Unexpected")
      | Some output ->
          let effect_info = ctx_get_effect_info ctx in
          (* Wrap in a result if the function can fail *)
          if effect_info.can_fail then mk_result_ok_texpr ctx.span output
          else output
    in

    let loop_info =
      {
        loop_id;
        input_vars = inputs;
        input_svl = loop.input_svalues;
        generics;
        forward_inputs = None;
        forward_output_no_state_no_result = None;
        back_outputs = rg_to_given_back_tys;
        back_funs = None;
        fwd_effect_info;
        back_effect_infos;
      }
    in
    let loops = LoopId.Map.add loop_id loop_info ctx.loops in
    { ctx with loops; mk_return = Some mk_return; mk_panic = Some mk_panic }
  in

  (* Update the context to translate the function end *)
  let ctx_end = { ctx with loop_id = Some loop_id } in
  let fun_end = translate_expr loop.end_expr ctx_end in

  (* Update the context for the loop body *)
  let ctx_loop = { ctx_end with inside_loop = true } in

  (* Translate the loop body *)
  let loop_body = translate_expr loop.loop_expr ctx_loop in

  (* Create the loop node and return *)
  let loop =
    let loop =
      close_loop loop.span
        {
          fun_end;
          loop_id;
          span = loop.span;
          inputs = List.map (fun v -> mk_tpattern_from_fvar v None) inputs;
          output_ty;
          loop_body;
        }
    in
    Loop loop
  in
  let ty = fun_end.ty in
  { e = loop; ty }

and translate_espan (span : S.espan) (e : S.expr) (ctx : bs_ctx) : texpr =
  let next_e = translate_expr e ctx in
  let span =
    match span with
    | S.Assignment (ectx, lp, rv, rp) ->
        let type_infos = ctx.type_ctx.type_infos in
        let lp = translate_mplace (Some ctx.span) type_infos lp in
        let rv = tvalue_to_texpr ctx ectx rv in
        let rp = translate_opt_mplace (Some ctx.span) type_infos rp in
        Some (Assignment (lp, rv, rp))
    | S.Snapshot ectx ->
        let infos = eval_ctx_to_symbolic_assignments_info ctx ectx in
        let infos =
          List.map (fun (fv, s) -> (mk_texpr_from_fvar fv, s)) infos
        in
        if infos <> [] then
          (* If often happens that the next expression contains exactly the
             same meta information *)
          match next_e.e with
          | Meta (SymbolicPlaces infos1, _) when infos1 = infos -> None
          | _ -> Some (SymbolicPlaces infos)
        else None
  in
  match span with
  | Some span ->
      let e = Meta (span, next_e) in
      let ty = next_e.ty in
      { e; ty }
  | None -> next_e
