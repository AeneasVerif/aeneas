open Pure
open PureUtils
open InterpUtils
open SymbolicToPureCore
open SymbolicToPureTypes
open SymbolicToPureValues
open SymbolicToPureAbs

(** The local logger *)
let log = Logging.symbolic_to_pure_expressions_log

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

   We may filter the region group ids.
*)
let fresh_back_vars_for_current_fun (ctx : bs_ctx) : bs_ctx * fvar option list =
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
    List.combine back_var_names (compute_back_tys ctx.sg.fun_ty)
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
let eval_ctx_to_symbolic_assignments_info (ctx : bs_ctx) (ectx : C.eval_ctx) :
    (fvar * string) list =
  let info : (fvar * string) list ref = ref [] in
  let push_info fv name = info := (fv, name) :: !info in
  let shared_loans = (fst (compute_ctx_ids ectx)).shared_loans_to_values in
  let visitor =
    object (self)
      inherit [_] C.iter_eval_ctx

      method! visit_env_elem _ ee =
        match ee with
        | EBinding (BVar { index = _; name = Some name }, v) ->
            self#visit_tvalue name v
        | _ -> () (* Ignore *)

      method! visit_value name v =
        match v with
        | VLiteral _ | VBottom -> ()
        | VBorrow (VSharedBorrow (bid, _)) ->
            let v = V.BorrowId.Map.find bid shared_loans in
            self#visit_tvalue name v
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
    [bs_ctx.mut_borrow_to_consumed] and [PureUtils.decompose_let_match]. *)
let decompose_let_match (ctx : bs_ctx) (pat : tpat) (bound : texpr) :
    bs_ctx * (tpat * texpr) =
  [%ltrace
    "- pat: " ^ tpat_to_string ctx pat ^ "\n- bound: "
    ^ texpr_to_string ctx bound];
  let span = ctx.span in
  let ctx = ref ctx in
  let refresh_var (var : fvar) =
    let ctx', var' = fresh_var var.basename var.ty !ctx in
    ctx := ctx';
    var'
  in
  (* Using [bs_ctx.mut_borrow_to_consumed] *)
  let get_default_expr (v : fvar) =
    (* We need to lookup the default values corresponding to
             each given back symbolic value *)
    match FVarId.Map.find_opt v.id !ctx.var_id_to_default with
    | Some e -> e
    | None ->
        (* This is a bug, but we might want to continue generating the model:
                 as an escape hatch, simply use the original variable (this will
                 lead to incorrect code of course) *)
        [%save_error] span
          ("Internal error: could not find variable. Please report an issue. \
            Debugging information:" ^ "\n- v.id: " ^ FVarId.to_string v.id
         ^ "\n- ctx.var_id_to_default: "
          ^ FVarId.Map.to_string None (texpr_to_string !ctx)
              !ctx.var_id_to_default
          ^ "\n");
        mk_texpr_from_fvar v
  in
  let pat, bound =
    PureUtils.decompose_let_match span refresh_var get_default_expr
      !ctx.type_ctx.type_decls pat bound
  in
  (!ctx, (pat, bound))

let rec translate_expr (e : S.expr) (ctx : bs_ctx) : texpr =
  [%ldebug "e:\n" ^ bs_ctx_expr_to_string ctx e];
  match e with
  | S.Return (ectx, opt_v) ->
      (* We reached a return.
         Remark: we can't get there if we are inside a loop. *)
      translate_return ectx opt_v ctx
  | Panic -> translate_panic ctx
  | FunCall (call, e) -> translate_function_call call e ctx
  | EndAbs (ectx, abs, e) -> translate_end_abs ectx abs e ctx
  | EvalGlobal (gid, generics, sv, e) ->
      translate_global_eval gid generics sv e ctx
  | Assertion (ectx, v, e) -> translate_assertion ectx v e ctx
  | Expansion (p, sv, exp) -> translate_expansion p sv exp ctx
  | IntroSymbolic (ectx, p, sv, v, e) ->
      translate_intro_symbolic ectx p sv v e ctx
  | SubstituteAbsIds (aids, e) -> translate_substitute_abs_ids ctx aids e
  | Meta (meta, e) -> translate_emeta meta e ctx
  | ForwardEnd (return_value, ectx, e, back_e) ->
      (* Translate the end of a function (this is introduced when we reach a [return] statement). *)
      translate_forward_end return_value ectx e back_e ctx
  | Loop loop -> translate_loop loop ctx
  | Error (span, msg) -> translate_error span msg
  | LoopContinue (ectx, loop_id, input_values, input_abs) ->
      translate_continue_break ctx ~continue:true ectx loop_id input_values
        input_abs
  | LoopBreak (ectx, loop_id, input_values, input_abs) ->
      translate_continue_break ctx ~continue:false ectx loop_id input_values
        input_abs
  | Let lete -> translate_let ctx lete
  | Join (ectx, input_values, input_abs) ->
      translate_join ctx ectx input_values input_abs

and translate_panic (ctx : bs_ctx) : texpr = Option.get ctx.mk_panic

(** [opt_v]: the value to return, in case we translate a forward body.

    Remark: in case we merge the forward/backward functions, we introduce those
    in [translate_forward_end]. *)
and translate_return (ectx : C.eval_ctx) (opt_v : V.tvalue option)
    (ctx : bs_ctx) : texpr =
  [%ldebug "e: return " ^ Print.option_to_string (tvalue_to_string ctx) opt_v];
  let opt_v = Option.map (tvalue_to_texpr ctx ectx) opt_v in
  (Option.get ctx.mk_return) ctx opt_v

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
        let effect_info = get_fun_effect_info ctx fid None in
        (* Generate the variables for the backward functions returned by the forward
           function. *)
        let ctx, ignore_fwd_output, back_funs =
          (* We need to compute the signatures of the backward functions. *)
          let sg = Option.get call.sg in
          let inst_sg = Option.get call.inst_sg in
          let decls_ctx = ctx.decls_ctx in
          let dsg =
            translate_inst_fun_sig_to_decomposed_fun_type (Some ctx.span)
              decls_ctx fid inst_sg
              (List.map (fun _ -> None) sg.inputs)
          in
          let back_tys = compute_back_tys_with_info dsg in
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
            List.filter_map (Option.map (mk_tpat_from_fvar None)) back_vars
          in

          (* Update the information about the backward functions *)
          let ctx =
            let backs, ignored =
              List.partition
                (fun (_, v) -> Option.is_some v)
                (List.combine call.abstractions back_vars)
            in
            let ignored = List.map fst ignored in
            let backs =
              List.map
                (fun (aid, fv) ->
                  let fvar = mk_texpr_from_fvar (Option.get fv) in
                  (aid, { fvar; can_fail = false }))
                backs
            in
            let ctx =
              {
                ctx with
                abs_id_to_info = V.AbsId.Map.add_list backs ctx.abs_id_to_info;
                ignored_abs_ids =
                  V.AbsId.Set.add_list ignored ctx.ignored_abs_ids;
              }
            in
            ctx
          in

          (* *)
          (ctx, dsg.fwd_info.ignore_output, back_funs)
        in
        (* Compute the pattern for the destination *)
        let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
        let dest = mk_tpat_from_fvar dest_mplace dest in
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
          mk_simpl_tuple_pat vars
        in
        (* Register the forward call (some information, for instance about
           the places where the values come from, will be useful later to
           compute names for the values given back by the backward functions) *)
        let ctx =
          { ctx with calls = V.FunCallId.Map.add call_id call ctx.calls }
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
              { can_fail = false; can_diverge = false; is_rec = false }
            in
            let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
            let dest = mk_tpat_from_fvar dest_mplace dest in
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
                can_diverge = false;
                is_rec = false;
              }
            in
            let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
            let dest = mk_tpat_from_fvar dest_mplace dest in
            (ctx, Unop (Neg int_ty), effect_info, args, [], dest)
        | _ -> [%craise] ctx.span "Unreachable")
    | S.Unop (E.Cast cast_kind) -> begin
        match cast_kind with
        | CastScalar (src_ty, tgt_ty) ->
            (* Note that cast can fail *)
            let effect_info =
              {
                can_fail = not (Config.backend () = Lean);
                can_diverge = false;
                is_rec = false;
              }
            in
            let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
            let dest = mk_tpat_from_fvar dest_mplace dest in
            (ctx, Unop (Cast (src_ty, tgt_ty)), effect_info, args, [], dest)
        | CastFnPtr _ -> [%craise] ctx.span "TODO: function casts"
        | CastUnsize _ ->
            (* We shouldn't get there: this case should have been detected before
               and handled in [translate_cast_unsize] *)
            [%internal_error] ctx.span
        | CastRawPtr _ -> [%craise] ctx.span "Unsupported: raw ptr casts"
        | CastTransmute _ -> [%craise] ctx.span "Unsupported: transmute"
        | CastConcretize _ ->
            [%craise] ctx.span "Unsupported: `dyn Trait` concretization"
      end
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
                can_diverge = false;
                is_rec = false;
              }
            in
            let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
            let dest = mk_tpat_from_fvar dest_mplace dest in
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
  let call_e = [%add_loc] mk_apps ctx.span func args in
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
            (fun ctx (f : tpat) ->
              let ty, _ = dest_arrow_ty ctx.span f.ty in
              let ctx, v = fresh_var (Some "back") ty ctx in
              let pat = mk_tpat_from_fvar None v in
              (ctx, mk_closed_lambda ctx.span pat (mk_texpr_from_fvar v)))
            ctx back_funs
        in
        (* We also need to change the type of the function *)
        let call_e =
          let call, args = destruct_apps call_e in
          match args with
          | [ x ] ->
              let call = { call with ty = mk_arrows [ x.ty ] x.ty } in
              [%add_loc] mk_app ctx.span call x
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
  [%add_loc] mk_closed_checked_let ctx effect_info.can_fail dest_v call_e next_e

and translate_cast_unsize (call : S.call) (e : S.expr) (ty0 : T.ty) (ty1 : T.ty)
    (ctx : bs_ctx) : texpr =
  (* Retrieve the information about the cast *)
  let info =
    InterpExpressions.cast_unsize_to_modified_fields ctx.span call.ctx ty0 ty1
  in

  (* Process the arguments and the destination *)
  let dest_mplace =
    translate_opt_mplace (Some call.span) ctx.type_ctx.type_infos
      call.dest_place
  in
  let ctx, dest = fresh_var_for_symbolic_value call.dest ctx in
  let dest = mk_tpat_from_fvar dest_mplace dest in
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
    [%add_loc] mk_apps ctx.span func [ v ]
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
          [%add_loc] mk_app ctx.span qualif arg
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
  [%add_loc] mk_closed_checked_let ctx monadic dest cast_expr next_e

and translate_end_abs (ectx : C.eval_ctx) (abs : V.abs) (e : S.expr)
    (ctx : bs_ctx) : texpr =
  [%ltrace "abstraction kind: " ^ V.show_abs_kind abs.kind];
  match abs.kind with
  | V.SynthInput rg_id ->
      translate_end_abstraction_synth_input ectx abs e ctx rg_id
  | V.FunCall (call_id, _) ->
      translate_end_abstraction_fun_call ectx abs e call_id ctx
  | V.SynthRet rg_id -> translate_end_abstraction_synth_ret ectx abs e ctx rg_id
  | V.Loop _ | V.Join -> translate_end_abstraction_join_or_loop ectx abs e ctx
  | V.WithCont -> translate_end_abstraction_with_cont ectx abs e ctx
  | V.Identity | V.CopySymbolicValue ->
      translate_end_abs_identity ectx abs e ctx

and translate_end_abstraction_synth_input (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expr) (ctx : bs_ctx) (rg_id : T.RegionGroupId.id) : texpr =
  [%ltrace
    "- function: "
    ^ name_to_string ctx ctx.fun_decl.item_meta.name
    ^ "\n- rg_id: "
    ^ T.RegionGroupId.to_string rg_id
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

  (* First, introduce the given back variables. *)
  let ctx, given_back_variables =
    let back_sg = RegionGroupId.Map.find bid ctx.sg.fun_ty.back_sg in
    let vars = List.combine back_sg.output_names back_sg.outputs in
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
    List.map (mk_tpat_from_fvar None) given_back_variables
  in
  [%sanity_check] ctx.span
    (List.length given_back_variables = List.length consumed_values);
  let variables_values = List.combine given_back_variables consumed_values in

  (* Sanity check: the two lists match (same types) *)
  (* TODO: normalize the types *)
  if !Config.type_check_pure_code then
    List.iter
      (fun (var, v) ->
        [%sanity_check] ctx.span ((var : tpat).ty = (v : texpr).ty))
      variables_values;
  (* Translate the next expression *)
  let next_e = translate_expr e ctx in
  (* Generate the assignemnts *)
  let monadic = false in
  mk_closed_checked_lets __FILE__ __LINE__ ctx monadic variables_values next_e

and translate_end_abstraction_fun_call (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expr) (call_id : V.fun_call_id) (ctx : bs_ctx) : texpr =
  let call = V.FunCallId.Map.find call_id ctx.calls in
  let info = V.AbsId.Map.find_opt abs.abs_id ctx.abs_id_to_info in
  (* Retrieve the values consumed upon ending the loans inside this
   * abstraction: those give us the input values *)
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
  let output = mk_simpl_tuple_pat outputs in
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
  match info with
  | None -> next_e ctx
  | Some info ->
      [%ltrace
        let args = List.map (texpr_to_string ctx) args in
        "func: "
        ^ texpr_to_string ctx info.fvar
        ^ "\nfunc type: "
        ^ pure_ty_to_string ctx info.fvar.ty
        ^ "\n\nargs:\n" ^ String.concat "\n" args];
      let call = [%add_loc] mk_apps ctx.span info.fvar args in
      (* Introduce a match if necessary *)
      let ctx, (output, call) = decompose_let_match ctx output call in
      (* Translate the next expression and construct the let *)
      [%add_loc] mk_closed_checked_let ctx info.can_fail output call
        (next_e ctx)

and translate_end_abs_identity (ectx : C.eval_ctx) (abs : V.abs) (e : S.expr)
    (ctx : bs_ctx) : texpr =
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
    "given back: " ^ Print.list_to_string (tpat_to_string ctx) given_back];
  (* Link the inputs to those given back values - note that this also
     checks we have the same number of values, of course *)
  let given_back_inputs = List.combine given_back inputs in
  (* Sanity check *)
  List.iter
    (fun ((given_back, input) : tpat * fvar) ->
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
    List.fold_left_map
      (fun ctx (v, e) -> decompose_let_match ctx v e)
      ctx given_back_inputs
  in
  (* Translate the next expression *)
  let next_e = translate_expr e ctx in
  (* Generate the assignments *)
  let monadic = false in
  mk_closed_checked_lets __FILE__ __LINE__ ctx monadic given_back_inputs next_e

and translate_end_abstraction_join_or_loop (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expr) (ctx : bs_ctx) : texpr =
  let span = ctx.span in
  (* Compute the input and output values *)
  let back_inputs = abs_to_consumed ctx ectx abs in
  let ctx, outputs = abs_to_given_back None abs ctx in
  let output = mk_simpl_tuple_pat outputs in
  (* Lookup the continuation to check if the abstraction is output by a join
     or a loop - note that it might not be there if the backward function was
     filtered because if it consumes nothing and outputs nothing *)
  let func = V.AbsId.Map.find_opt abs.abs_id ctx.abs_id_to_info in
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
  match func with
  | None ->
      [%ldebug
        "No backward function found for abstraction: "
        ^ V.AbsId.to_string abs.abs_id];
      (* TODO: generalize. We should always translate the continuation expression
         directly.

         Note that we can get here when ending a loop abstraction which has
         to be ignored, but also when ending an abstraction which comes from
         converting the shared loan introduced when accessing a global value
         through a reference. *)
      [%sanity_check] span
        (V.AbsId.Set.mem abs.abs_id ctx.ignored_abs_ids
        || (back_inputs = [] && outputs = []));
      next_e ctx
  | Some { fvar = func; can_fail } ->
      [%ltrace
        let args = List.map (texpr_to_string ctx) args in
        "func: " ^ texpr_to_string ctx func ^ "\nfunc type: "
        ^ pure_ty_to_string ctx func.ty
        ^ "\n\nargs:\n" ^ String.concat "\n" args];
      let call = [%add_loc] mk_apps ctx.span func args in
      (* Introduce a match if necessary *)
      let ctx, (output, call) = decompose_let_match ctx output call in
      (* Translate the next expression and construct the let *)
      let next_e = next_e ctx in
      [%ltrace
        "About to reconstruct let-bindings:" ^ "\n- output: "
        ^ tpat_to_string ctx output ^ "\n- call: " ^ texpr_to_string ctx call
        ^ "\n- next:\n" ^ texpr_to_string ctx next_e];
      [%add_loc] mk_closed_checked_let ctx can_fail output call next_e

and translate_end_abstraction_with_cont (ectx : C.eval_ctx) (abs : V.abs)
    (e : S.expr) (ctx : bs_ctx) : texpr =
  [%ldebug "abs:\n" ^ abs_to_string ctx abs];
  (* Translate the continuation *)
  let ctx, can_fail, output, abs_e =
    translate_ended_abs_to_texpr ctx ectx abs
  in
  [%ldebug
    "- output:\n" ^ tpat_to_string ctx output ^ "\n- abs_e:\n"
    ^ texpr_to_string ctx abs_e];
  (* Translate the next expression *)
  let next_e = translate_expr e ctx in
  (* Put everything together *)
  [%add_loc] mk_closed_checked_let ctx can_fail output abs_e next_e

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
  [%add_loc] mk_closed_checked_let ctx false (mk_tpat_from_fvar None var) gval e

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
  let assertion = [%add_loc] mk_apps ctx.span func args in
  [%add_loc] mk_closed_checked_let ctx monadic
    (mk_ignored_pat mk_unit_ty)
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
          [%add_loc] mk_closed_checked_let ctx monadic
            (mk_tpat_from_fvar None var)
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
            let vars = List.map (fun x -> mk_tpat_from_fvar None x) vars in
            let pat_ty = scrutinee.ty in
            let pat = mk_adt_pat pat_ty variant_id vars in
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
        ^ pure_ty_to_string ctx false_e.ty
        ^ "\n\n- true_e:\n" ^ texpr_to_string ctx true_e ^ " \n\nfalse_e:\n"
        ^ texpr_to_string ctx false_e];
      [%sanity_check] ctx.span (ty = false_e.ty);
      { e; ty }
  | ExpandInt (int_ty, branches, otherwise) ->
      let translate_branch ((v, branch_e) : V.scalar_value * S.expr) :
          match_branch =
        (* We don't need to update the context: we don't introduce any
           new values/variables *)
        let branch = translate_expr branch_e ctx in
        let pat = mk_tpat_from_literal (VScalar v) in
        close_branch ctx.span pat branch
      in
      let branches = List.map translate_branch branches in
      let otherwise = translate_expr otherwise ctx in
      let pat_ty = TLiteral (TypesUtils.integer_as_literal int_ty) in
      let otherwise_pat : tpat = { pat = PIgnored; ty = pat_ty } in
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
      let lvars = List.map (fun v -> mk_tpat_from_fvar None v) vars in
      let lv = mk_adt_pat scrutinee.ty variant_id lvars in
      let monadic = false in
      [%add_loc] mk_closed_checked_let ctx monadic lv
        (mk_opt_mplace_texpr scrutinee_mplace scrutinee)
        branch
  | TTuple ->
      let vars = List.map (fun x -> mk_tpat_from_fvar None x) vars in
      let monadic = false in
      [%add_loc] mk_closed_checked_let ctx monadic (mk_simpl_tuple_pat vars)
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
      [%add_loc] mk_closed_checked_let ctx monadic
        (mk_tpat_from_fvar None var)
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
  let var = mk_tpat_from_fvar mplace var in
  [%add_loc] mk_closed_checked_let ctx monadic var v next_e

and translate_forward_end (return_value : (C.eval_ctx * V.tvalue) option)
    (_ectx : C.eval_ctx) (fwd_e : S.expr)
    (back_e : S.expr S.region_group_id_map) (ctx : bs_ctx) : texpr =
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

  (* Compute the output of the forward function *)
  let fwd_effect_info = ctx.sg.fun_ty.fwd_info.effect_info in
  let ctx, pure_fwd_var = fresh_var None ctx.sg.fun_ty.fwd_output ctx in
  let fwd_e = translate_one_end ctx None in

  (* If we reached a loop: if we are *inside* a loop, we need to ignore the
       backward functions which are not associated to region abstractions.
    *)
  let back_el =
    List.map
      (fun ((gid, _) : RegionGroupId.id * back_sg_info) ->
        Some (translate_one_end ctx (Some gid)))
      (RegionGroupId.Map.bindings ctx.sg.fun_ty.back_sg)
  in

  (* Compute whether the backward expressions should be evaluated straight
     away or not (i.e., if we should bind them with monadic let-bindings
     or not). We evaluate them straight away if they can fail and have no
     inputs. *)
  let evaluate_backs =
    List.map
      (fun (sg : back_sg_info) ->
        if !Config.simplify_merged_fwd_backs then
          sg.inputs = [] && sg.effect_info.can_fail
        else false)
      (RegionGroupId.Map.values ctx.sg.fun_ty.back_sg)
  in

  (* Introduce variables for the backward functions.
       We lookup the LLBC definition in an attempt to derive pretty names
       for those functions. *)
  let _, back_vars = fresh_back_vars_for_current_fun ctx in

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
        | Some v -> Some (v, eval, Option.get el))
      (List.combine back_vars (List.combine evaluate_backs back_el))
  in
  let e =
    List.fold_right
      (fun (var, evaluate, back_e) e ->
        [%add_loc] mk_closed_checked_let ctx evaluate
          (mk_tpat_from_fvar None var)
          back_e e)
      back_vars_els ret
  in

  (* Bind the expression for the forward output *)
  let pat = mk_tpat_from_fvar None pure_fwd_var in
  [%add_loc] mk_closed_checked_let ctx fwd_effect_info.can_fail pat fwd_e e

and translate_loop (loop : S.loop) (ctx0 : bs_ctx) : texpr =
  let ctx = ctx0 in
  let loop_id = V.LoopId.Map.find loop.loop_id ctx.loop_ids_map in

  (* Some helpers *)
  let translate_input_abs (absl : V.abs_id list)
      (abs_to_value : V.abs V.AbsId.Map.t) : texpr list =
    let input_abs =
      List.map (fun abs_id -> V.AbsId.Map.find abs_id abs_to_value) absl
    in
    List.filter_map (translate_abs_to_cont ctx loop.ctx) input_abs
  in
  let translate_input_values (vl : V.symbolic_value list)
      (symb_to_value : V.tvalue V.SymbolicValueId.Map.t) : texpr list =
    let input_values =
      List.map
        (fun (sv : V.symbolic_value) ->
          V.SymbolicValueId.Map.find sv.sv_id symb_to_value)
        vl
    in
    List.map (tvalue_to_texpr ctx loop.ctx) input_values
  in
  (* Introduce free variables for the inputs *)
  let bind_inputs (ctx : bs_ctx) (absl : V.abs list)
      (values : V.symbolic_value list) : bs_ctx * tpat list * tpat list =
    let ctx, absl =
      (* Compute the type of the break abstractions *)
      let abs_tys = List.map (abs_to_ty ctx) absl in
      let abs_tys, ignored =
        List.partition_map
          (fun (abs, ty) ->
            match ty with
            | Some ty -> Left (abs.V.abs_id, ty)
            | None -> Right abs.abs_id)
          (List.combine absl abs_tys)
      in
      (* Introduce free variables for the abs *)
      let ctx, fvars =
        List.fold_left_map
          (fun ctx (aid, ty) ->
            let ctx, fvar = fresh_var (Some "back") ty ctx in
            (ctx, (aid, fvar)))
          ctx abs_tys
      in
      (* Register the mapping from abs to free variable *)
      let ctx =
        let fvars =
          List.map
            (fun (aid, fv) ->
              (aid, { fvar = mk_texpr_from_fvar fv; can_fail = false }))
            fvars
        in
        {
          ctx with
          abs_id_to_info = V.AbsId.Map.add_list fvars ctx.abs_id_to_info;
          ignored_abs_ids = V.AbsId.Set.add_list ignored ctx.ignored_abs_ids;
        }
      in
      (* *)
      (ctx, List.map snd fvars)
    in
    let ctx, values = fresh_vars_for_symbolic_values values ctx in
    let mk_pats = List.map (mk_tpat_from_fvar None) in
    (ctx, mk_pats absl, mk_pats values)
  in

  (* Translate the loop input abstractions *)
  let input_abs =
    translate_input_abs
      (List.map (fun a -> a.V.abs_id) loop.input_abs)
      loop.input_abs_to_abs
  in

  (* Translate the loop input values *)
  let input_values =
    translate_input_values loop.input_svalues loop.input_value_to_value
  in
  let inputs = input_abs @ input_values in
  [%ldebug
    "- loop input abstractions:\n "
    ^ String.concat "\n\n"
        (List.map (abs_to_string ctx)
           (V.AbsId.Map.values loop.input_abs_to_abs))
    ^ "\n\n- loop input values:\n"
    ^ String.concat "\n"
        (List.map (tvalue_to_string ctx)
           (V.SymbolicValueId.Map.values loop.input_value_to_value))
    ^ "\n\n- loop translated inputs:\n"
    ^ String.concat "\n\n" (List.map (texpr_to_string ctx) inputs)];

  (* Introduce the binders for the loop outputs *)
  let ctx, break_abs, break_values =
    bind_inputs ctx loop.break_abs loop.break_svalues
  in
  let outputs = break_values @ break_abs in
  let output = mk_simpl_tuple_pat outputs in

  [%ldebug
    "- loop output values:\n"
    ^ String.concat "\n"
        (List.map (symbolic_value_to_string ctx) loop.break_svalues)
    ^ "\n\n- loop output abstractions:\n"
    ^ String.concat "\n\n" (List.map (abs_to_string ctx) loop.break_abs)
    ^ "\n\n- loop translated outputs:\n"
    ^ String.concat "\n" (List.map (tpat_to_string ctx) outputs)];

  (* Translate the body *)
  let loop_body =
    (* Introduce free variables for the inputs *)
    let ctx, input_conts, input_values =
      bind_inputs ctx0 loop.input_abs loop.input_svalues
    in

    (* Update the [mk_panic], [mk_result], etc. functions *)
    let continue_ty = List.map (fun (e : texpr) -> e.ty) inputs in
    let continue_ty = mk_simpl_tuple_ty continue_ty in
    let break_ty = output.ty in
    let mk_panic =
      mk_loop_result_fail_texpr_with_error_id ctx.span continue_ty break_ty
        error_failure_id
    in
    let mk_continue ctx output = mk_continue_texpr ctx.span output break_ty in
    let mk_break ctx output = mk_break_texpr ctx.span continue_ty output in
    let ctx =
      {
        ctx with
        mk_panic = Some mk_panic;
        mk_return = None;
        mk_continue = Some mk_continue;
        mk_break = Some mk_break;
      }
    in

    (* Translate the body *)
    let body = translate_expr loop.loop_expr ctx in

    (* Put everything together *)
    let inputs = input_conts @ input_values in

    (* We need to close the binders *)
    let inputs, loop_body = close_binders ctx.span inputs body in
    { inputs; loop_body }
  in

  (* Make the loop expression *)
  let loop_e : loop =
    {
      loop_id;
      span = loop.span;
      output_tys = List.map (fun (pat : tpat) -> pat.ty) outputs;
      num_output_values = List.length break_values;
      inputs = input_abs @ input_values;
      num_input_conts = List.length input_abs;
      loop_body;
    }
  in
  [%sanity_check] loop.span
    (List.length loop_e.loop_body.inputs = List.length loop_e.inputs);
  let loop_ty = mk_result_ty output.ty in
  let loop_e : texpr = { e = Loop loop_e; ty = loop_ty } in

  [%ltrace
    "- loop expression:\n" ^ texpr_to_string ctx loop_e ^ "\n\n- num inputs: "
    ^ string_of_int (List.length inputs)];

  (* Translate the next expression *)
  let next_e = translate_expr loop.next_expr ctx in

  (* Create the let-binding *)
  [%add_loc] mk_closed_checked_let ctx true output loop_e next_e

and translate_continue_break (ctx : bs_ctx) ~(continue : bool)
    (ectx : C.eval_ctx) (_loop_id : V.loop_id) (input_values : V.tvalue list)
    (input_abs : V.abs list) : texpr =
  [%ldebug
    "- input_values:\n"
    ^ String.concat "\n" (List.map (tvalue_to_string ctx) input_values)
    ^ "\n- input_abs:\n"
    ^ String.concat "\n\n" (List.map (abs_to_string ctx) input_abs)];
  let conts = List.filter_map (translate_abs_to_cont ctx ectx) input_abs in
  let values = List.map (tvalue_to_texpr ctx ectx) input_values in
  [%ldebug
    "- translated values:\n"
    ^ String.concat "\n" (List.map (texpr_to_string ctx) values)
    ^ "\n- translated abs:\n"
    ^ String.concat "\n\n" (List.map (texpr_to_string ctx) conts)];
  (* Note that the order between the values and the continuations is not the same
     depending on whether we reach a break or a continue *)
  let outputs, mk =
    if continue then (conts @ values, ctx.mk_continue)
    else (values @ conts, ctx.mk_break)
  in
  let output = mk_simpl_tuple_texpr ctx.span outputs in
  Option.get mk ctx output

and translate_let (ctx0 : bs_ctx) (lete : S.let_expr) : texpr =
  let ctx = ctx0 in

  (* Introduce free variables for the outputs *)
  let bind_outputs (ctx : bs_ctx) (absl : V.abs list)
      (values : V.symbolic_value list) : bs_ctx * tpat list * tpat list =
    let ctx, absl =
      (* Compute the type of the break abstractions *)
      let abs_tys = List.map (abs_to_ty ctx) absl in
      let abs_tys, ignored =
        List.partition_map
          (fun (abs, ty) ->
            match ty with
            | Some ty -> Left (abs.V.abs_id, ty)
            | None -> Right abs.abs_id)
          (List.combine absl abs_tys)
      in
      (* Introduce free variables for the abs *)
      let ctx, fvars =
        List.fold_left_map
          (fun ctx (aid, ty) ->
            let ctx, fvar = fresh_var (Some "back") ty ctx in
            (ctx, (aid, fvar)))
          ctx abs_tys
      in
      (* Register the mapping from abs to free variable *)
      let ctx =
        let fvars =
          List.map
            (fun (aid, fv) ->
              (aid, { fvar = mk_texpr_from_fvar fv; can_fail = false }))
            fvars
        in
        {
          ctx with
          abs_id_to_info = V.AbsId.Map.add_list fvars ctx.abs_id_to_info;
          ignored_abs_ids = V.AbsId.Set.add_list ignored ctx.ignored_abs_ids;
        }
      in
      (* *)
      (ctx, List.map snd fvars)
    in
    let ctx, values = fresh_vars_for_symbolic_values values ctx in
    let mk_pats = List.map (mk_tpat_from_fvar None) in
    (ctx, mk_pats absl, mk_pats values)
  in

  (* Introduce the binders for the outputs *)
  let ctx, out_abs, out_values =
    bind_outputs ctx lete.out_abs lete.out_svalues
  in
  let outputs = out_values @ out_abs in
  let output = mk_simpl_tuple_pat outputs in

  [%ldebug
    "- output values:\n"
    ^ String.concat "\n"
        (List.map (symbolic_value_to_string ctx) lete.out_svalues)
    ^ "\n\n- output abstractions:\n"
    ^ String.concat "\n\n" (List.map (abs_to_string ctx) lete.out_abs)
    ^ "\n\n- translated outputs:\n"
    ^ String.concat "\n" (List.map (tpat_to_string ctx) outputs)];

  (* Translate the bound expression *)
  let bound_e =
    (* Update the [mk_panic], [mk_continue], etc. functions *)
    let output_ty = output.ty in
    let mk_panic =
      mk_result_fail_texpr_with_error_id ctx.span error_failure_id output_ty
    in
    let ctx =
      {
        ctx with
        mk_panic = Some mk_panic;
        mk_return = None;
        mk_continue = None;
        mk_break = None;
      }
    in

    (* Translate the bound expression *)
    translate_expr lete.bound_expr ctx
  in
  [%ltrace "- bound expression:\n" ^ texpr_to_string ctx bound_e];

  (* Translate the next expression *)
  let next_e = translate_expr lete.next_expr ctx in

  (* Create the let-binding *)
  [%add_loc] mk_closed_checked_let ctx true output bound_e next_e

and translate_join (ctx : bs_ctx) (ectx : C.eval_ctx)
    (input_values : V.tvalue list) (input_abs : V.abs list) : texpr =
  [%ldebug
    "- input_values:\n"
    ^ String.concat "\n" (List.map (tvalue_to_string ctx) input_values)
    ^ "\n- input_abs:\n"
    ^ String.concat "\n\n" (List.map (abs_to_string ctx) input_abs)];
  let conts = List.filter_map (translate_abs_to_cont ctx ectx) input_abs in
  let values = List.map (tvalue_to_texpr ctx ectx) input_values in
  [%ldebug
    "- translated values:\n"
    ^ String.concat "\n" (List.map (texpr_to_string ctx) values)
    ^ "\n- translated abs:\n"
    ^ String.concat "\n\n" (List.map (texpr_to_string ctx) conts)];
  (* Note that the order between the values and the continuations is not the same
     depending on whether we reach a break or a continue *)
  let outputs = values @ conts in
  let output = mk_simpl_tuple_texpr ctx.span outputs in
  mk_result_ok_texpr ctx.span output

and translate_substitute_abs_ids (ctx : bs_ctx) (aids : V.abs_id V.AbsId.Map.t)
    (e : S.expr) : texpr =
  (* We need to update the information we have in the various maps of the context *)
  let { abs_id_to_info; ignored_abs_ids; _ } = ctx in
  let update (aid : V.AbsId.id) : V.AbsId.id =
    match V.AbsId.Map.find_opt aid aids with
    | Some aid -> aid
    | None -> aid
  in

  (* *)
  let abs_id_to_info' =
    V.AbsId.Map.of_list
      ((List.map (fun (aid, x) -> (update aid, x)))
         (V.AbsId.Map.bindings abs_id_to_info))
  in
  (* Check for collisions *)
  [%sanity_check] ctx.span
    (V.AbsId.Map.cardinal abs_id_to_info = V.AbsId.Map.cardinal abs_id_to_info');

  (* *)
  let ignored_abs_ids' = V.AbsId.Set.map update ignored_abs_ids in
  (* Check for collisions *)
  [%sanity_check] ctx.span
    (V.AbsId.Set.cardinal ignored_abs_ids
    = V.AbsId.Set.cardinal ignored_abs_ids');

  (* Translate the next expression with the updated context *)
  let ctx =
    {
      ctx with
      abs_id_to_info = abs_id_to_info';
      ignored_abs_ids = ignored_abs_ids';
    }
  in
  translate_expr e ctx

and translate_emeta (meta : S.emeta) (e : S.expr) (ctx : bs_ctx) : texpr =
  let ctx, meta =
    match meta with
    | S.Assignment (ectx, lp, rv, rp) ->
        let type_infos = ctx.type_ctx.type_infos in
        let lp = translate_mplace (Some ctx.span) type_infos lp in
        let rv = tvalue_to_texpr ctx ectx rv in
        let rp = translate_opt_mplace (Some ctx.span) type_infos rp in
        (ctx, Some (Assignment (lp, rv, rp)))
    | S.Snapshot (mid, ectx) ->
        [%ldebug
          "Translating snapshot: meta id: m@" ^ Values.MetaId.to_string mid];
        let infos = eval_ctx_to_symbolic_assignments_info ctx ectx in
        let infos =
          List.map (fun (fv, s) -> (mk_texpr_from_fvar fv, s)) infos
        in
        (* Filter the information to remove the redundant bits *)
        let infos =
          List.filter
            (fun x -> not (MetaSymbPlaceSet.mem x ctx.meta_symb_places))
            infos
        in
        let ctx =
          {
            ctx with
            meta_symb_places =
              MetaSymbPlaceSet.add_list infos ctx.meta_symb_places;
          }
        in
        let infos = if infos <> [] then Some (SymbolicPlaces infos) else None in
        (ctx, infos)
  in
  let next_e = translate_expr e ctx in
  match meta with
  | Some meta ->
      let e = Meta (meta, next_e) in
      let ty = next_e.ty in
      { e; ty }
  | None -> next_e
