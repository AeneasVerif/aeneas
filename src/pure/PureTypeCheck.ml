(** Module to perform type checking on the pure AST - we use this for sanity
    checks only *)

open Pure
open PureUtils

let log = Logging.pure_type_check_log

(** Utility function, used for type checking.

    This function should only be used for "regular" ADTs, where the number of
    fields is fixed: it shouldn't be used for arrays, slices, etc. *)
let get_adt_field_types (span : Meta.span)
    (type_decls : type_decl TypeDeclId.Map.t) (type_id : type_id)
    (variant_id : VariantId.id option) (generics : generic_args) : ty list =
  match type_id with
  | TTuple ->
      (* Tuple *)
      [%sanity_check] span (generics.const_generics = []);
      [%sanity_check] span (generics.trait_refs = []);
      [%sanity_check] span (variant_id = None);
      generics.types
  | TAdtId def_id ->
      (* "Regular" ADT *)
      let def = TypeDeclId.Map.find def_id type_decls in
      type_decl_get_instantiated_fields_types def variant_id generics
  | TBuiltin aty -> (
      (* Builtin type *)
      match aty with
      | TResult ->
          let ty = Collections.List.to_cons_nil generics.types in
          let variant_id = Option.get variant_id in
          if variant_id = result_ok_id then [ ty ]
          else if variant_id = result_fail_id then [ mk_error_ty ]
          else [%craise] span "Unreachable: improper variant id for result type"
      | TSum ->
          let left, right =
            match generics.types with
            | [ left; right ] -> (left, right)
            | _ -> [%internal_error] span
          in
          let variant_id = Option.get variant_id in
          if variant_id = sum_left_id then [ left ]
          else if variant_id = sum_right_id then [ right ]
          else [%craise] span "Unreachable: improper variant id for sum type"
      | TLoopResult ->
          let continue, break =
            match generics.types with
            | [ continue; break ] -> (continue, break)
            | _ -> [%internal_error] span
          in
          let variant_id = Option.get variant_id in
          if variant_id = loop_result_continue_id then [ continue ]
          else if variant_id = loop_result_break_id then [ break ]
          else
            [%craise] span
              "Unreachable: improper variant id for loop result type"
      | TError ->
          [%sanity_check] span (generics = empty_generic_args);
          let variant_id = Option.get variant_id in
          [%sanity_check] span
            (variant_id = error_failure_id || variant_id = error_out_of_fuel_id);
          []
      | TFuel ->
          let variant_id = Option.get variant_id in
          if variant_id = fuel_zero_id then []
          else if variant_id = fuel_succ_id then [ mk_fuel_ty ]
          else [%craise] span "Unreachable: improper variant id for fuel type"
      | TArray | TSlice | TStr | TRawPtr _ ->
          (* Array: when not symbolic values (for instance, because of aggregates),
             the array expressions are introduced as struct updates *)
          [%craise] span "Attempting to access the fields of an opaque type")

type tc_ctx = {
  decls_ctx : Contexts.decls_ctx;
  type_decls : type_decl TypeDeclId.Map.t;  (** The type declarations *)
  global_decls : A.global_decl A.GlobalDeclId.Map.t;
      (** The global declarations *)
  fenv : ty FVarId.Map.t;  (** Environment from variables to types *)
  benv : ty BVarId.Map.t list;  (** Environment from variables to types *)
  const_generics : ty T.ConstGenericVarId.Map.t;
      (** The types of the const generics *)
  (* TODO: add trait type constraints *)
  pbenv : ty BVarId.Map.t option;
      (** This is similar to what we do with [fmt_env] *)
  bvar_counter : BVarId.id;
}

let texpr_to_string (ctx : tc_ctx) (e : texpr) : string =
  let fmt = PrintPure.decls_ctx_to_fmt_env ctx.decls_ctx in
  PrintPure.texpr_to_string fmt false "" "  " e

let tpat_to_string (ctx : tc_ctx) (x : tpat) : string =
  let fmt = PrintPure.decls_ctx_to_fmt_env ctx.decls_ctx in
  PrintPure.tpat_to_string fmt x

let ty_to_string (ctx : tc_ctx) (x : ty) : string =
  let fmt = PrintPure.decls_ctx_to_fmt_env ctx.decls_ctx in
  PrintPure.ty_to_string fmt false x

let check_literal (span : Meta.span) (v : literal) (ty : literal_type) : unit =
  match (ty, v) with
  | TInt int_ty, VScalar (SignedScalar (ty, _)) ->
      [%sanity_check] span (int_ty = ty)
  | TUInt int_ty, VScalar (UnsignedScalar (ty, _)) ->
      [%sanity_check] span (int_ty = ty)
  | TBool, VBool _ | TChar, VChar _ -> ()
  | _ -> [%craise] span "Inconsistent type"

let tc_ctx_start_pbenv (ctx : tc_ctx) : tc_ctx =
  assert (ctx.pbenv = None);
  { ctx with pbenv = Some BVarId.Map.empty; bvar_counter = BVarId.zero }

let tc_ctx_push_pbenv (ctx : tc_ctx) : tc_ctx =
  {
    ctx with
    benv = Option.get ctx.pbenv :: ctx.benv;
    pbenv = None;
    bvar_counter = BVarId.zero;
  }

let tc_ctx_push_bvar (ctx : tc_ctx) (v : var) : tc_ctx =
  let id = ctx.bvar_counter in
  let counter = BVarId.incr id in
  let pbenv = BVarId.Map.add id v.ty (Option.get ctx.pbenv) in
  { ctx with pbenv = Some pbenv; bvar_counter = counter }

let rec check_tpat_aux (span : Meta.span) (ctx : tc_ctx) (v : tpat) : tc_ctx =
  [%ltrace tpat_to_string ctx v];
  match v.pat with
  | PConstant cv ->
      check_literal span cv (ty_as_literal span v.ty);
      ctx
  | PIgnored -> ctx
  | PBound (var, _) ->
      [%pure_type_check] span (var.ty = v.ty);
      tc_ctx_push_bvar ctx var
  | POpen (var, _) ->
      [%pure_type_check] span (var.ty = v.ty);
      ctx
  | PAdt av ->
      (* Compute the field types *)
      let type_id, generics = ty_as_adt span v.ty in
      let field_tys =
        get_adt_field_types span ctx.type_decls type_id av.variant_id generics
      in
      let check_value (ctx : tc_ctx) (ty : ty) (v : tpat) : tc_ctx =
        if ty <> v.ty then
          (* TODO: we need to normalize the types *)
          [%craise] span
            ("Inconsistent types:" ^ "\n- ty: " ^ show_ty ty ^ "\n- v.ty: "
           ^ show_ty v.ty);
        check_tpat_aux span ctx v
      in
      (* Check the field types: check that the field patterns have the expected
       * types, and check that the field patterns themselves are well-typed *)
      List.fold_left
        (fun ctx (ty, v) -> check_value ctx ty v)
        ctx
        (List.combine field_tys av.fields)

let check_tpat (span : Meta.span) (ctx : tc_ctx) (v : tpat) : tc_ctx =
  tc_ctx_push_pbenv (check_tpat_aux span (tc_ctx_start_pbenv ctx) v)

let rec check_texpr (span : Meta.span) (ctx : tc_ctx) (e : texpr) : unit =
  [%ltrace texpr_to_string ctx e];
  match e.e with
  | BVar var ->
      (* Lookup the variable - note that the variable may not be there,
       * if we type-check a subexpression (i.e.: if the variable is introduced
       * "outside" of the expression) - TODO: this won't happen once
       * we use a locally nameless representation *)
      let tys =
        [%silent_unwrap] span (Collections.List.nth_opt ctx.benv var.scope)
      in
      let ty = [%silent_unwrap] span (BVarId.Map.find_opt var.id tys) in
      [%pure_type_check] span (ty = e.ty)
  | FVar fid ->
      let ty = [%silent_unwrap] span (FVarId.Map.find_opt fid ctx.fenv) in
      [%pure_type_check] span (ty = e.ty)
  | CVar cg_id ->
      let ty = T.ConstGenericVarId.Map.find cg_id ctx.const_generics in
      [%pure_type_check] span (ty = e.ty)
  | Const cv -> check_literal span cv (ty_as_literal span e.ty)
  | App (app, arg) ->
      let input_ty, output_ty = destruct_arrow span app.ty in
      [%pure_type_check] span (input_ty = arg.ty);
      [%pure_type_check] span (output_ty = e.ty);
      check_texpr span ctx app;
      check_texpr span ctx arg
  | Lambda (pat, body) ->
      let pat_ty, body_ty = destruct_arrow span e.ty in
      [%pure_type_check] span (pat.ty = pat_ty);
      [%pure_type_check] span (body.ty = body_ty);
      (* Check the pattern and register the introduced variables at the same time *)
      let ctx = check_tpat span ctx pat in
      check_texpr span ctx body
  | Qualif qualif -> (
      match qualif.id with
      | FunOrOp _ -> () (* TODO *)
      | Global _ -> () (* TODO *)
      | TraitConst _ -> () (* TODO *)
      | Proj { adt_id = proj_adt_id; field_id } ->
          (* Note we can only project fields of structures (not enumerations) *)
          (* Deconstruct the projector type *)
          let adt_ty, field_ty = destruct_arrow span e.ty in
          let adt_id, adt_generics = ty_as_adt span adt_ty in
          (* Check the ADT type *)
          [%pure_type_check] span (adt_id = proj_adt_id);
          [%pure_type_check] span (adt_generics = qualif.generics);
          (* Retrieve and check the expected field type *)
          let variant_id = None in
          let expected_field_tys =
            get_adt_field_types span ctx.type_decls proj_adt_id variant_id
              qualif.generics
          in
          let expected_field_ty = FieldId.nth expected_field_tys field_id in
          [%pure_type_check] span (expected_field_ty = field_ty)
      | AdtCons id -> (
          let expected_field_tys =
            get_adt_field_types span ctx.type_decls id.adt_id id.variant_id
              qualif.generics
          in
          let field_tys, adt_ty = destruct_arrows e.ty in
          [%pure_type_check] span (expected_field_tys = field_tys);
          match adt_ty with
          | TAdt (type_id, generics) ->
              [%pure_type_check] span (type_id = id.adt_id);
              [%pure_type_check] span (generics = qualif.generics)
          | _ -> [%craise] span "Unreachable"))
  | Let (monadic, pat, re, e_next) ->
      [%ldebug "Let: e:\n" ^ texpr_to_string ctx e];
      let expected_pat_ty =
        if monadic then destruct_result span re.ty else re.ty
      in
      [%ldebug
        "Let:\n- pat.ty: " ^ ty_to_string ctx pat.ty ^ "\n- expected_pat_ty: "
        ^ ty_to_string ctx expected_pat_ty];
      [%pure_type_check] span (pat.ty = expected_pat_ty);
      [%pure_type_check] span (e.ty = e_next.ty);
      (* Check the right-expression *)
      check_texpr span ctx re;
      (* Check the pattern and register the introduced variables at the same time *)
      let ctx = check_tpat span ctx pat in
      (* Check the next expression *)
      check_texpr span ctx e_next
  | Switch (scrut, switch_body) -> (
      check_texpr span ctx scrut;
      match switch_body with
      | If (e_then, e_else) ->
          [%pure_type_check] span (scrut.ty = TLiteral TBool);
          [%pure_type_check] span (e_then.ty = e.ty);
          [%pure_type_check] span (e_else.ty = e.ty);
          check_texpr span ctx e_then;
          check_texpr span ctx e_else
      | Match branches ->
          let check_branch (br : match_branch) : unit =
            [%pure_type_check] span (br.pat.ty = scrut.ty);
            let ctx = check_tpat span ctx br.pat in
            check_texpr span ctx br.branch
          in
          List.iter check_branch branches)
  | Loop loop ->
      (* TODO: check the inputs *)
      check_texpr span ctx loop.loop_body.loop_body
  | StructUpdate supd -> (
      (* Check the init value *)
      begin
        match supd.init with
        | None -> ()
        | Some init ->
            check_texpr span ctx init;
            [%pure_type_check] span (init.ty = e.ty)
      end;
      (* Check the fields *)
      (* Retrieve and check the expected field type *)
      let adt_id, adt_generics = ty_as_adt span e.ty in
      [%pure_type_check] span (adt_id = supd.struct_id);
      (* The id can only be: a custom type decl or an array *)
      match adt_id with
      | TAdtId _ ->
          let variant_id = None in
          let expected_field_tys =
            get_adt_field_types span ctx.type_decls adt_id variant_id
              adt_generics
          in
          List.iter
            (fun ((fid, fe) : _ * texpr) ->
              let expected_field_ty = FieldId.nth expected_field_tys fid in
              [%pure_type_check] span (expected_field_ty = fe.ty);
              check_texpr span ctx fe)
            supd.updates
      | TBuiltin TArray ->
          let expected_field_ty =
            Collections.List.to_cons_nil adt_generics.types
          in
          List.iter
            (fun ((_, fe) : _ * texpr) ->
              [%pure_type_check] span (expected_field_ty = fe.ty);
              check_texpr span ctx fe)
            supd.updates
      | _ -> [%craise] span "Unexpected")
  | Meta (_, e_next) ->
      [%pure_type_check] span (e_next.ty = e.ty);
      check_texpr span ctx e_next
  | EError (span, msg) -> [%craise_opt_span] span msg
